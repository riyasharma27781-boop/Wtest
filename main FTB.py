"""
Wordly Telegram bot — optimized for high concurrency on low RAM.

Drop-in replacement for the previous main.py. Same handlers, same commands,
same database schema. Internal architecture rewritten for stability under load.

Key changes vs original:
  * Per-chat outbound serializer (sends, edits, pins, unpins) with race-free
    pipeline creation — every message for a given chat is processed in order.
  * Global token-bucket rate limiter (25 req/s, burst 30) in front of every
    Telegram API call, so the bot never hits Telegram's global 30/s ceiling.
  * Single global ticker task replaces per-game timer tasks (1 task instead
    of N for N active games).
  * Coalesced board edits — multiple "dirty" marks collapse into one edit.
  * user_scores keyed by user_id (fixes duplicate-name score collision).
  * Cached "Go to board" inline keyboard per game (no per-guess allocation).
  * Read-only SQLite connection pool (3 conns, round-robin).
  * Real LRU for played-sets cache (OrderedDict.move_to_end).
  * Bounded deferred-score queue with overflow flush (no unbounded growth).
  * Admin-status cache (300s TTL) avoids repeated get_chat_member calls.
  * Expected Telegram errors (BadRequest/Forbidden) logged at debug, not error.
"""

import asyncio
import functools
import time
import random
import os
import html
import queue
import logging
from collections import OrderedDict, Counter
from logging.handlers import QueueHandler, QueueListener

# uvloop: ~2-4x faster asyncio loop. Optional — falls back to default if missing.
try:
    import uvloop  # type: ignore
    asyncio.set_event_loop_policy(uvloop.EventLoopPolicy())
    _UVLOOP_ENABLED = True
except ImportError:
    _UVLOOP_ENABLED = False

import aiosqlite
from dotenv import load_dotenv
from aiogram import Bot, Dispatcher, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties
from aiogram.filters import Command
from aiogram.types import (
    Message, ChatMemberUpdated,
    BotCommand, InlineKeyboardMarkup, InlineKeyboardButton,
    CallbackQuery, ReactionTypeEmoji,
)
from aiogram.exceptions import (
    TelegramRetryAfter, TelegramForbiddenError, TelegramBadRequest,
)

try:
    import w as _word_source
    LETTER_SETS = getattr(_word_source, "LETTER_SETS", {})
except ImportError:
    _word_source = None
    LETTER_SETS = {1: {"letters": "E, L, T, A, R"}}


# ---------------------------------------------------------------------------
# Logging (non-blocking via QueueHandler/QueueListener)
# ---------------------------------------------------------------------------
load_dotenv()

_log_queue: queue.Queue = queue.Queue(-1)
_stream_handler = logging.StreamHandler()
_log_listener = QueueListener(_log_queue, _stream_handler, respect_handler_level=True)
_log_listener.start()

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(name)s - %(message)s",
    handlers=[QueueHandler(_log_queue)],
    force=True,
)
logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
BOT_TOKEN = os.getenv("BOT_TOKEN")
ADMIN_IDS: set[int] = {
    int(x.strip()) for x in os.getenv("ADMIN_ID", "0").split(",") if x.strip().isdigit()
}
_PROMOTED_ADMINS: set[int] = set()
NOTIFICATION_GROUP = int(os.getenv("NOTIFICATION_GROUP", 0))

P1_ID = "5346105514575025401"
P_BOARD_EMOJI_ID = "5256131095094652290"

# New Premium Emojis
P_STAR = '<tg-emoji emoji-id="4929483658114368660">⭐</tg-emoji>'
P_UP = '<tg-emoji emoji-id="5388602717025351120">⬆️</tg-emoji>'
P_PENCIL = '<tg-emoji emoji-id="5936111781981197900">✍🏻</tg-emoji>'
P_ARROW = '<tg-emoji emoji-id="6271712920103555728">▶️</tg-emoji>'
P_LETTERS = '<tg-emoji emoji-id="6086676112560102104">🔡</tg-emoji>'
P_OK = '<tg-emoji emoji-id="5258396243666681152">👌</tg-emoji>'

# Original Emojis
P4 = '<tg-emoji emoji-id="5255861796350224063">🏁</tg-emoji>'
P_HELP = '<tg-emoji emoji-id="5253742260054409879">📞</tg-emoji>'
P_ALREADY = '<tg-emoji emoji-id="5210952531676504517">⚠️</tg-emoji>'
P_ADD = '<tg-emoji emoji-id="5472146462362048818">➕</tg-emoji>'
P_OVER = '<tg-emoji emoji-id="5461151367559141950">🎉</tg-emoji>'

# Updated Score Emojis
P_SCORES = '<tg-emoji emoji-id="5188344996356448758">🏆</tg-emoji>'
P_DIAMOND = '<tg-emoji emoji-id="5359719332542718652">💎</tg-emoji>'

# Fill-the-blanks challenge emojis
P_FILL_SQUARE = '<tg-emoji emoji-id="5276459604803340645">◾️</tg-emoji>'
P_FILL_BOOKS = '<tg-emoji emoji-id="5373098009640836781">📚</tg-emoji>'
P_FILL_DICE = '<tg-emoji emoji-id="5384474763827620477">🎲</tg-emoji>'
P_FILL_STAR = '<tg-emoji emoji-id="5936111781981197900">⭐</tg-emoji>'
P_FILL_TROPHY = '<tg-emoji emoji-id="5188344996356448758">🏆</tg-emoji>'
P_FILL_MONEY = '<tg-emoji emoji-id="5409048419211682843">💵</tg-emoji>'
FILL_BLANK_REWARD = 100

if not BOT_TOKEN:
    logger.error("BOT_TOKEN is missing from .env file!")
    raise SystemExit(1)

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode="HTML"))
dp = Dispatcher()

# Static end-game keyboard (allocated once)
END_GAME_KB = InlineKeyboardMarkup(inline_keyboard=[[
    InlineKeyboardButton(
        text="New Game",
        callback_data="start_scramble",
        icon_custom_emoji_id=P1_ID,
        style="primary",
    )
]])

def _boldify_letters(text: str) -> str:
    return f'<b>{text}</b>'


# Lookup table: index = word length, value = points awarded
_POINTS = [0, 0, 0, 1, 2, 3, 5, 7, 10, 10, 10, 10, 10]

# Static DM keyboard (allocated once)
_DM_KB = InlineKeyboardMarkup(inline_keyboard=[[
    InlineKeyboardButton(
        text="Join official group",
        url="https://t.me/WordlyChat",
        style="primary",
    ),
    InlineKeyboardButton(
        text="Contact us",
        url="https://t.me/WordlySupportBot",
        style="success",
    ),
]])


# ---------------------------------------------------------------------------
# Bans middleware
# ---------------------------------------------------------------------------
_BANNED_USERS: set = set()
_BANNED_GROUPS: set = set()


class BanMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        if isinstance(event, Message):
            if event.from_user and event.from_user.id in _BANNED_USERS:
                return
            if event.chat and event.chat.id in _BANNED_GROUPS:
                return
        elif isinstance(event, CallbackQuery):
            if event.from_user and event.from_user.id in _BANNED_USERS:
                return
            if event.message and event.message.chat and event.message.chat.id in _BANNED_GROUPS:
                return
        return await handler(event, data)


dp.message.middleware(BanMiddleware())
dp.callback_query.middleware(BanMiddleware())


# ---------------------------------------------------------------------------
# Maintenance mode
# ---------------------------------------------------------------------------
_MAINTENANCE_MODE: bool = False
_MAINTENANCE_MSG = (
    "🚧 Bot is under maintenance\n\n"
    "Kindly wait for sometime ⏳\n\n"
    "◾Join our official channel for more info:\n\n"
    "T.me/wordlyy"
)
_MAINT_COOLDOWN: dict = {}
_MAINT_COOLDOWN_SECS = 15
_LAST_BCAST: dict = {}

# Populated at startup via bot.get_me() — used to filter commands in groups.
_BOT_USERNAME: str = ""


def _is_command_for_this_bot(message: Message) -> bool:
    """
    Return True only when the message contains a bot command aimed at THIS bot.

    In group chats Wordly receives every message (when privacy mode is off or
    the bot is an admin).  That includes plain text, media, and commands sent
    to OTHER bots (/cmd@otherbot).  We must not spam the maintenance message
    for any of those — only reply when the user actually typed a command
    intended for us.

    Rules:
      • No bot_command entity  →  not a command at all → False
      • /cmd            (no @suffix)  →  aimed at all bots, including us → True
      • /cmd@wordlybot  (@our name)   →  explicitly for us → True
      • /cmd@otherbot   (@other name) →  not for us → False
    """
    entities = message.entities or []
    for entity in entities:
        if entity.type == "bot_command":
            text = message.text or message.caption or ""
            cmd_slice = text[entity.offset: entity.offset + entity.length]
            if "@" in cmd_slice:
                _, at_name = cmd_slice.split("@", 1)
                if _BOT_USERNAME and at_name.lower() != _BOT_USERNAME.lower():
                    return False  # command is for a different bot
            return True  # no @, or @matches us
    return False  # no bot_command entity at all


class MaintenanceMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        if _MAINTENANCE_MODE:
            if isinstance(event, Message):
                if event.from_user and event.from_user.id in ADMIN_IDS:
                    return await handler(event, data)
                # In group chats only reply when the command is aimed at us.
                # Plain text, media, and /cmd@otherbot are silently ignored.
                if event.chat and event.chat.type in ("group", "supergroup"):
                    if not _is_command_for_this_bot(event):
                        return
                uid = event.from_user.id if event.from_user else 0
                now = time.time()
                if now - _MAINT_COOLDOWN.get(uid, 0) < _MAINT_COOLDOWN_SECS:
                    return
                _MAINT_COOLDOWN[uid] = now
                try:
                    await event.answer(_MAINTENANCE_MSG)
                except Exception:
                    pass
                return
            elif isinstance(event, CallbackQuery):
                if event.from_user and event.from_user.id in ADMIN_IDS:
                    return await handler(event, data)
                uid = event.from_user.id
                now = time.time()
                if now - _MAINT_COOLDOWN.get(uid, 0) < _MAINT_COOLDOWN_SECS:
                    try:
                        await event.answer()
                    except Exception:
                        pass
                    return
                _MAINT_COOLDOWN[uid] = now
                try:
                    await event.answer(
                        "🚧 Bot is under maintenance. Kindly wait ⏳",
                        show_alert=True,
                    )
                except Exception:
                    pass
                return
        return await handler(event, data)


dp.message.middleware(MaintenanceMiddleware())
dp.callback_query.middleware(MaintenanceMiddleware())


# ---------------------------------------------------------------------------
# Game state
# ---------------------------------------------------------------------------
games: dict = {}
pending_games: set = set()

PLAYED_SETS_CACHE: "OrderedDict[int, set]" = OrderedDict()
MAX_PLAYED_SETS_CACHE = 5000

_PENDING_USER_IDS: set = set()
_DEFERRED_SCORE_QUEUE: list = []
_DEFERRED_FTB_QUEUE: list = []
MAX_DEFERRED_QUEUE = 5000
_FLUSHING_CHATS: set = set()

_NEWGAME_COOLDOWN: dict = {}
NEWGAME_COOLDOWN_SECS = 5
MAX_COOLDOWN_ENTRIES = 2000

_DM_NEW_COOLDOWN: dict = {}
_CMD_COOLDOWN: dict = {}
_STATS_COOLDOWN: dict = {}
_TOP10_COOLDOWN: dict = {}
_LB_COOLDOWN: dict = {}
_TOPCHATS_COOLDOWN: dict = {}

_LB_EDITING: set = set()
_LB_USER_CD: dict = {}
_LAST_HISTORY_CLEANUP: float = 0.0

_PENDING_GAMES_COUNT = 0

# Admin-status cache
_ADMIN_CACHE: "OrderedDict[tuple, tuple]" = OrderedDict()
ADMIN_CACHE_TTL = 300.0
ADMIN_CACHE_MAX = 50000

# Process start timestamp (used by /health for uptime).
_BOT_START = time.time()

# Post-game trailer text (set via /addt, cleared via /rmt).
_ADDT_TEXT: str = ""

# Emoji reaction mode — per-chat on/off flag and chosen emoji.
# Emoji reaction mode — per-chat on/off flag and chosen emoji.
# Off by default for every group. Default emoji is 👀.
_EMOJI_MODE: dict = {}
_CHAT_EMOJI: dict = {}
_PUZZLES_OFF: set = set()


# Fill-the-blanks challenge state. Challenges are intentionally kept in RAM:
# the active answer is only valid for 20 minutes and must never block gameplay.
fill_puzzles: dict = {}
_LAST_PUZZLE_STATS: dict = {}
_PENDING_FILL_SCORES: dict = {}
FILL_PUZZLE_DURATION = 20 * 60
FILL_PUZZLE_INTERVAL = 60 * 60
FILL_SEND_DELAY = 0.1
FILL_CLEANUP_INTERVAL = 5.0
# Keep deletions conservative even though every request also passes through
# GLOBAL_RL. This prevents a large batch of expired group puzzles from
# creating a burst of deleteMessage calls.
FILL_DELETE_DELAY = 2.0


# ---------------------------------------------------------------------------
# Word dictionary preload
# ---------------------------------------------------------------------------
GLOBAL_WORDS_CACHE: list = []
PRECOMPUTED_WORDS: dict = {}
PUZZLE_WORDS: list = []




def _create_fill_puzzle() -> dict | None:
    if not PUZZLE_WORDS:
        return None
        
    word = random.choice(PUZZLE_WORDS)
    word_len = len(word)
    
    # CHANGED: Updated Reveal Logic (1 for 5, 2 for 6-7, 3 for 8)
    if word_len == 5:
        reveal_count = 1
    elif word_len in (6, 7):
        reveal_count = 2
    elif word_len >= 8:
        reveal_count = 3
    else:
        reveal_count = 1  # Fallback
        
    revealed = set(random.sample(range(word_len), reveal_count))
    scrambled = list(word)
    random.shuffle(scrambled)
    
    attempts = 0
    while "".join(scrambled) == word and attempts < 10:
        random.shuffle(scrambled)
        attempts += 1
        
    letters = " ".join(scrambled)
    pattern = " ".join(char if index in revealed else "_" for index, char in enumerate(word))

    # CHANGED: Added `created_at` to accurately measure solve time later
    now = time.monotonic()
    return {
        "word": word,
        "letters": letters,
        "pattern": pattern,
        "created_at": now, 
        "expires_at": now + FILL_PUZZLE_DURATION,
    }



def _fill_puzzle_text(puzzle: dict) -> str:
    # Notice the <b> tags around puzzle['letters'] to make them bold.
    return (
        f"{P_FILL_SQUARE} Find Word Challenge!\n\n"
        f"{P_FILL_BOOKS} Letters: <b>{puzzle['letters']}</b>\n"
        f"{P_FILL_DICE} {puzzle['pattern']}\n\n"
        f"{P_FILL_STAR} Fill the blanks to make the correct word"
    )


def _claim_fill_puzzle(chat_id: int, attempt: str, now: float | None = None):
    """Atomically claim a correct answer before any awaited work can run."""
    puzzle = fill_puzzles.get(chat_id)
    if puzzle is None:
        return None

    current_time = time.monotonic() if now is None else now
    if current_time >= puzzle.get("expires_at", 0):
        fill_puzzles.pop(chat_id, None)
        return None

    if attempt != puzzle["word"].upper():
        return None

    # This synchronous pop is the winner lock: another update cannot run
    # between this lookup and removal because there is no await in this
    # function. The first update processed by this event loop wins.
    fill_puzzles.pop(chat_id, None)
    return puzzle


def load_words():
    global GLOBAL_WORDS_CACHE
    GLOBAL_WORDS_CACHE = []
    try:
        with open("words.txt", "r", encoding="utf-8") as f:
            for line in f:
                w = line.strip().lower()
                if 3 <= len(w) <= 12:
                    GLOBAL_WORDS_CACHE.append((w, Counter(w)))
        logger.info(f"Loaded {len(GLOBAL_WORDS_CACHE)} words into fast memory.")
    except FileNotFoundError:
        logger.warning("words.txt not found. Using fallback dictionary.")
        for w in ["art", "let", "tar", "rat", "ear", "tea", "late", "rate",
                  "tear", "tale", "alter", "alert", "later", "artel"]:
            GLOBAL_WORDS_CACHE.append((w, Counter(w)))


def _find_valid_words(letters_str: str) -> frozenset:
    letters_clean = letters_str.replace(" ", "").replace(",", "").lower()
    letters_count = Counter(letters_clean)
    valid = set()
    for word, word_count in GLOBAL_WORDS_CACHE:
        if all(letters_count[ch] > 0 and word_count[ch] <= 3 for ch in word_count):
            valid.add(word.upper())
    return frozenset(valid)


def precompute_all_sets():
    for set_id, set_data in LETTER_SETS.items():
        PRECOMPUTED_WORDS[set_id] = _find_valid_words(set_data["letters"])
    logger.info(f"Pre-computed valid words for {len(PRECOMPUTED_WORDS)} letter sets.")
    # NOTE: GLOBAL_WORDS_CACHE intentionally NOT cleared — kept resident for
    # /add validation and any future word features. Costs ~30 MB on a 4 GB box.


# ---------------------------------------------------------------------------
# Global rate limiter (token bucket: 25 req/s, burst 30)
# ---------------------------------------------------------------------------
class GlobalRateLimiter:
    def __init__(self, rate: float = 25.0, burst: int = 30):
        self.rate = rate
        self.capacity = burst
        self.tokens = float(burst)
        self.updated = time.monotonic()
        self.lock = asyncio.Lock()

    async def acquire(self):
        async with self.lock:
            now = time.monotonic()
            self.tokens = min(self.capacity,
                              self.tokens + (now - self.updated) * self.rate)
            self.updated = now
            if self.tokens >= 1:
                self.tokens -= 1
                return
            wait = (1.0 - self.tokens) / self.rate
            self.tokens -= 1            # reserve a slot
            self.updated = now + wait
        await asyncio.sleep(wait)


GLOBAL_RL = GlobalRateLimiter(rate=25.0, burst=30)


# ---------------------------------------------------------------------------
# Per-chat outbound pipeline
# ---------------------------------------------------------------------------
PIPELINE_QUEUE_SIZE = 200
PIPELINE_IDLE_SHUTDOWN_SECS = 60


class ChatPipeline:
    __slots__ = ("chat_id", "queue", "worker_task", "pending_edit", "last_active")

    def __init__(self, chat_id: int):
        self.chat_id = chat_id
        self.queue: asyncio.Queue = asyncio.Queue(maxsize=PIPELINE_QUEUE_SIZE)
        self.worker_task: asyncio.Task | None = None
        self.pending_edit: dict | None = None
        self.last_active = time.monotonic()

    async def _execute(self, kind: str, payload: dict):
        fut = payload.get("_future") if kind == "send_wait" else None
        send_kwargs = (
            {k: v for k, v in payload.items() if k != "_future"}
            if kind == "send_wait"
            else payload
        )

        for attempt in range(3):
            await GLOBAL_RL.acquire()
            try:
                if kind == "send":
                    await bot.send_message(self.chat_id, **payload)
                elif kind == "send_wait":
                    msg = await bot.send_message(self.chat_id, **send_kwargs)
                    if fut and not fut.done():
                        fut.set_result(msg)
                    return
                elif kind == "edit":
                    edit_kwargs = self.pending_edit
                    self.pending_edit = None
                    if not edit_kwargs:
                        return
                    await bot.edit_message_text(chat_id=self.chat_id, **edit_kwargs)
                elif kind == "edit_markup":
                    await bot.edit_message_reply_markup(chat_id=self.chat_id, **payload)
                return
            except TelegramRetryAfter as e:
                if e.retry_after > 5:
                    if fut and not fut.done():
                        fut.set_result(None)
                    return
                await asyncio.sleep(e.retry_after + 0.1)
            except (TelegramForbiddenError, TelegramBadRequest) as e:
                logger.debug(f"Pipeline expected drop chat={self.chat_id}: {e}")
                if fut and not fut.done():
                    fut.set_result(None)
                return
            except Exception as e:
                logger.error(f"Pipeline send error chat={self.chat_id} kind={kind}: {e}")
                if fut and not fut.done():
                    fut.set_result(None)
                return

        # Exhausted retries
        if fut and not fut.done():
            fut.set_result(None)


    async def run(self):
        try:
            while True:
                try:
                    job = await asyncio.wait_for(self.queue.get(),
                                                 timeout=PIPELINE_IDLE_SHUTDOWN_SECS)
                except asyncio.TimeoutError:
                    return
                if job is None:
                    return
                kind, payload = job
                self.last_active = time.monotonic()
                try:
                    await self._execute(kind, payload)
                finally:
                    self.queue.task_done()
        except asyncio.CancelledError:
            pass
        finally:
            cur = _PIPELINES.get(self.chat_id)
            if cur is self:
                _PIPELINES.pop(self.chat_id, None)


_PIPELINES: "dict[int, ChatPipeline]" = {}
_PIPELINE_DICT_LOCK = asyncio.Lock()


def _peek_pipeline(chat_id: int) -> ChatPipeline | None:
    p = _PIPELINES.get(chat_id)
    if p and p.worker_task and not p.worker_task.done():
        return p
    return None


async def _ensure_pipeline(chat_id: int) -> ChatPipeline:
    p = _peek_pipeline(chat_id)
    if p:
        return p
    async with _PIPELINE_DICT_LOCK:
        p = _peek_pipeline(chat_id)
        if p:
            return p
        p = ChatPipeline(chat_id)
        p.worker_task = asyncio.create_task(p.run())
        _PIPELINES[chat_id] = p
        return p


async def queue_send(chat_id: int, text: str, **kwargs) -> bool:
    pipe = await _ensure_pipeline(chat_id)
    payload = {"text": text, **kwargs}
    try:
        pipe.queue.put_nowait(("send", payload))
        return True
    except asyncio.QueueFull:
        logger.warning(f"Pipeline queue full for chat={chat_id}, dropped send")
        return False


async def queue_send_and_wait(chat_id: int, text: str, timeout: float = 15.0, **kwargs):
    pipe = await _ensure_pipeline(chat_id)
    fut = asyncio.get_running_loop().create_future()
    payload = {"text": text, "_future": fut, **kwargs}
    try:
        pipe.queue.put_nowait(("send_wait", payload))
    except asyncio.QueueFull:
        return None
    try:
        return await asyncio.wait_for(fut, timeout=timeout)
    except asyncio.TimeoutError:
        return None


async def queue_edit_board(chat_id: int, msg_id: int, text: str, **kwargs):
    """Coalesced board edit. Only the latest text is sent."""
    pipe = await _ensure_pipeline(chat_id)
    payload = {"message_id": msg_id, "text": text, **kwargs}
    needs_marker = pipe.pending_edit is None
    pipe.pending_edit = payload
    if needs_marker:
        try:
            pipe.queue.put_nowait(("edit", None))
        except asyncio.QueueFull:
            pass


async def queue_edit_markup(chat_id: int, msg_id: int, reply_markup):
    pipe = await _ensure_pipeline(chat_id)
    try:
        pipe.queue.put_nowait(("edit_markup",
                               {"message_id": msg_id, "reply_markup": reply_markup}))
    except asyncio.QueueFull:
        pass



async def rate_limited_call(coro):
    """Wrap any direct Bot API call (read or write) in the global RL."""
    await GLOBAL_RL.acquire()
    return await coro


# ---------------------------------------------------------------------------
# Database — single write conn + 3-conn read pool
# ---------------------------------------------------------------------------
_DB_CONN: aiosqlite.Connection | None = None
_DB_LOCK = asyncio.Lock()
_DB_WRITE_LOCK = asyncio.Lock()

_DB_READ_POOL: list = []
_DB_READ_POOL_SIZE = 3
_DB_READ_INDEX = 0
_DB_READ_INIT_LOCK = asyncio.Lock()


async def get_db() -> aiosqlite.Connection:
    global _DB_CONN
    if _DB_CONN is None:
        async with _DB_LOCK:
            if _DB_CONN is None:
                conn = await aiosqlite.connect("scores.db")
                await conn.execute("PRAGMA journal_mode=WAL")
                await conn.execute("PRAGMA synchronous=NORMAL")
                await conn.execute("PRAGMA cache_size=-10000")
                await conn.execute("PRAGMA temp_store=MEMORY")
                await conn.execute("PRAGMA mmap_size=33554432")
                await conn.execute("PRAGMA busy_timeout=5000")
                conn.row_factory = aiosqlite.Row
                _DB_CONN = conn
    return _DB_CONN


async def _init_read_pool():
    global _DB_READ_POOL
    if _DB_READ_POOL:
        return
    async with _DB_READ_INIT_LOCK:
        if _DB_READ_POOL:
            return
        pool = []
        for _ in range(_DB_READ_POOL_SIZE):
            conn = await aiosqlite.connect("scores.db", isolation_level=None)
            await conn.execute("PRAGMA journal_mode=WAL")
            await conn.execute("PRAGMA query_only=ON")
            await conn.execute("PRAGMA cache_size=-10000")
            await conn.execute("PRAGMA temp_store=MEMORY")
            await conn.execute("PRAGMA mmap_size=33554432")
            await conn.execute("PRAGMA busy_timeout=5000")
            conn.row_factory = aiosqlite.Row
            pool.append(conn)
        _DB_READ_POOL = pool


async def get_read_db() -> aiosqlite.Connection:
    if not _DB_READ_POOL:
        await _init_read_pool()
    global _DB_READ_INDEX
    idx = _DB_READ_INDEX
    _DB_READ_INDEX = (idx + 1) % len(_DB_READ_POOL)
    return _DB_READ_POOL[idx]

def load_puzzle_words():
    """Preload challenge words from fill.txt once at startup."""
    global PUZZLE_WORDS
    PUZZLE_WORDS = []
    try:
        with open("fill.txt", "r", encoding="utf-8") as f:
            for line in f:
                word = line.strip().replace('"', '').replace("'", "").replace(",", "").upper()
                
                # CHANGED: 4 to 10 letters for FTB mode and puzzles
                if word and 4 <= len(word) <= 10 and word.isalpha():
                    PUZZLE_WORDS.append(word)
        
        PUZZLE_WORDS = list(set(PUZZLE_WORDS))
        logger.info(f"Loaded {len(PUZZLE_WORDS)} fill-the-blanks words from fill.txt.")
    except FileNotFoundError:
        logger.warning("fill.txt not found. Fill-the-blanks mode will not start until this file exists.")

async def init_db():
    try:
        db = await get_db()
        await db.execute(
            "CREATE TABLE IF NOT EXISTS scramble_scores "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, score INTEGER DEFAULT 0, "
            "PRIMARY KEY (user_id, chat_id))"
        )
        await db.execute(
            "CREATE TABLE IF NOT EXISTS played_scramble_sets "
            "(chat_id INTEGER, set_id INTEGER, PRIMARY KEY (chat_id, set_id))"
        )
        await db.execute("CREATE TABLE IF NOT EXISTS users (user_id INTEGER PRIMARY KEY)")
        await db.execute(
            "CREATE TABLE IF NOT EXISTS bot_stats "
            "(stat_name TEXT PRIMARY KEY, stat_value INTEGER)"
        )
        await db.execute(
            "INSERT OR IGNORE INTO bot_stats (stat_name, stat_value) VALUES ('total_games', 0)"
        )
        await db.execute("CREATE TABLE IF NOT EXISTS tracked_groups (chat_id INTEGER PRIMARY KEY)")
        await db.execute("CREATE TABLE IF NOT EXISTS banned_users (user_id INTEGER PRIMARY KEY)")
        await db.execute("CREATE TABLE IF NOT EXISTS banned_groups (chat_id INTEGER PRIMARY KEY)")
        await db.execute("CREATE TABLE IF NOT EXISTS promoted_admins (user_id INTEGER PRIMARY KEY)")
        
        await db.execute(
            "CREATE TABLE IF NOT EXISTS game_log "
            "(chat_id INTEGER, played_at INTEGER)"
        )
        await db.execute(
            "CREATE INDEX IF NOT EXISTS idx_game_log_played_at "
            "ON game_log(played_at)"
        )
        await db.execute("CREATE INDEX IF NOT EXISTS idx_scramble_scores_chat ON scramble_scores(chat_id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_scramble_scores_user ON scramble_scores(user_id)")
        await db.execute(
            "CREATE TABLE IF NOT EXISTS score_history "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, "
            "score_delta INTEGER, recorded_at INTEGER)"
        )
        await db.execute(
            "CREATE INDEX IF NOT EXISTS idx_score_history_chat_time "
            "ON score_history(chat_id, recorded_at)"
        )
        await db.execute(
            "CREATE INDEX IF NOT EXISTS idx_score_history_time "
            "ON score_history(recorded_at)"
        )
        await db.execute(
            "CREATE TABLE IF NOT EXISTS fill_blank_scores "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, "
            "coins INTEGER DEFAULT 0, puzzles_solved INTEGER DEFAULT 0, "
            "PRIMARY KEY (user_id, chat_id))"
        )
        await db.execute(
            "CREATE TABLE IF NOT EXISTS fill_blank_history "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, "
            "coins_delta INTEGER, recorded_at INTEGER)"
        )
        await db.execute(
            "CREATE INDEX IF NOT EXISTS idx_fill_blank_history_time "
            "ON fill_blank_history(recorded_at)"
        )

        # --- NEW: Tables for Fill The Blanks Mode (/new2) ---
        await db.execute(
            "CREATE TABLE IF NOT EXISTS ftb_scores "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, score INTEGER DEFAULT 0, "
            "games_played INTEGER DEFAULT 0, words_found INTEGER DEFAULT 0, "
            "PRIMARY KEY (user_id, chat_id))"
        )
        await db.execute(
            "CREATE TABLE IF NOT EXISTS ftb_history "
            "(user_id INTEGER, chat_id INTEGER, username TEXT, "
            "score_delta INTEGER, recorded_at INTEGER)"
        )
        await db.execute(
            "CREATE INDEX IF NOT EXISTS idx_ftb_history_time "
            "ON ftb_history(recorded_at)"
        )

        for col_sql in [
            "ALTER TABLE scramble_scores ADD COLUMN games_played INTEGER DEFAULT 0",
            "ALTER TABLE scramble_scores ADD COLUMN words_found INTEGER DEFAULT 0",
            "ALTER TABLE scramble_scores ADD COLUMN longest_word TEXT DEFAULT ''",
        ]:
            try:
                await db.execute(col_sql)
            except Exception:
                pass
        await db.commit()
        await _init_read_pool()
    except Exception as e:
        logger.error(f"Database init failed: {e}")

async def load_bans():
    try:
        db = await get_read_db()
        cur = await db.execute("SELECT user_id FROM banned_users")
        for row in await cur.fetchall():
            _BANNED_USERS.add(row[0])
            
        cur = await db.execute("SELECT chat_id FROM banned_groups")
        for row in await cur.fetchall():
            _BANNED_GROUPS.add(row[0])
            
        # --- NEW: Load Promoted Admins on boot ---
        cur = await db.execute("SELECT user_id FROM promoted_admins")
        for row in await cur.fetchall():
            _PROMOTED_ADMINS.add(row[0])
            
        logger.info(f"Loaded {len(_BANNED_USERS)} banned users, "
                    f"{len(_BANNED_GROUPS)} banned groups, "
                    f"{len(_PROMOTED_ADMINS)} promoted admins.")
    except Exception as e:
        logger.error(f"Error loading bans/admins: {e}")


def track_user_ram(user_id: int):
    _PENDING_USER_IDS.add(user_id)


# ---------------------------------------------------------------------------
# Played-sets cache + picker
# ---------------------------------------------------------------------------
async def _reset_played_sets_db(chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM played_scramble_sets WHERE chat_id = ?", (chat_id,))
            await db.commit()
    except Exception as e:
        logger.error(f"Failed to reset played sets for {chat_id}: {e}")


async def pick_scramble_set(chat_id: int):
    if chat_id in PLAYED_SETS_CACHE:
        PLAYED_SETS_CACHE.move_to_end(chat_id)
    else:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT set_id FROM played_scramble_sets WHERE chat_id = ?", (chat_id,))
        PLAYED_SETS_CACHE[chat_id] = {row[0] for row in await cur.fetchall()}
        if len(PLAYED_SETS_CACHE) > MAX_PLAYED_SETS_CACHE:
            PLAYED_SETS_CACHE.popitem(last=False)

    played = PLAYED_SETS_CACHE[chat_id]
    available = [sid for sid in LETTER_SETS.keys() if sid not in played]
    if not available:
        PLAYED_SETS_CACHE[chat_id] = set()
        asyncio.create_task(_reset_played_sets_db(chat_id))
        available = list(LETTER_SETS.keys())

    chosen_id = random.choice(available)
    return chosen_id, LETTER_SETS[chosen_id]


# ---------------------------------------------------------------------------
# Background batch flusher
# ---------------------------------------------------------------------------
async def _flush_all_pending(deferred_entries: list,
                              pending_user_ids: list,
                              games_to_save: int = 0):
    chat_ids_to_clear = [c for _, c, _ in deferred_entries]
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            if games_to_save > 0:
                await db.execute(
                    "UPDATE bot_stats SET stat_value = stat_value + ? "
                    "WHERE stat_name = 'total_games'",
                    (games_to_save,),
                )
            for pending_scores, chat_id, set_id in deferred_entries:
                if set_id is not None:
                    await db.execute(
                        "INSERT OR IGNORE INTO played_scramble_sets (chat_id, set_id) "
                        "VALUES (?, ?)",
                        (chat_id, set_id),
                    )
                    cache = PLAYED_SETS_CACHE.get(chat_id)
                    if cache is None:
                        PLAYED_SETS_CACHE[chat_id] = {set_id}
                        if len(PLAYED_SETS_CACHE) > MAX_PLAYED_SETS_CACHE:
                            PLAYED_SETS_CACHE.popitem(last=False)
                    else:
                        cache.add(set_id)
                if pending_scores:
                    await db.executemany(
                        "INSERT OR IGNORE INTO users (user_id) VALUES (?)",
                        [(uid,) for uid in pending_scores],
                    )
                    score_rows = [
                        (uid, chat_id, data["username"], data["score"],
                         data.get("games_played", 0), data.get("words_found", 0),
                         data.get("longest_word", ""),
                         data["score"], data["username"],
                         data.get("games_played", 0), data.get("words_found", 0),
                         data.get("longest_word", ""), data.get("longest_word", ""))
                        for uid, data in pending_scores.items()
                    ]
                    await db.executemany(
                        "INSERT INTO scramble_scores "
                        "(user_id, chat_id, username, score, games_played, words_found, longest_word) "
                        "VALUES (?, ?, ?, ?, ?, ?, ?) "
                        "ON CONFLICT(user_id, chat_id) DO UPDATE SET "
                        "score = score + ?, username = ?, "
                        "games_played = games_played + ?, words_found = words_found + ?, "
                        "longest_word = CASE WHEN length(?) > length(longest_word) "
                        "THEN ? ELSE longest_word END",
                        score_rows,
                    )
                    ts = int(time.time())
                    await db.executemany(
                        "INSERT INTO score_history "
                        "(user_id, chat_id, username, score_delta, recorded_at) "
                        "VALUES (?, ?, ?, ?, ?)",
                        [(uid, chat_id, data["username"], data["score"], ts)
                         for uid, data in pending_scores.items()],
                    )
            if pending_user_ids:
                await db.executemany(
                    "INSERT OR IGNORE INTO users (user_id) VALUES (?)",
                    [(uid,) for uid in pending_user_ids],
                )
            await db.commit()
    except Exception as e:
        logger.error(f"Batch flush failed: {e}")
        _PENDING_USER_IDS.update(pending_user_ids)
        global _PENDING_GAMES_COUNT
        _PENDING_GAMES_COUNT += games_to_save
    finally:
        for cid in chat_ids_to_clear:
            _FLUSHING_CHATS.discard(cid)


def _queue_fill_score(user_id: int, chat_id: int, username: str, reward: int):
    key = (user_id, chat_id)
    entry = _PENDING_FILL_SCORES.get(key)
    if entry is None:
        _PENDING_FILL_SCORES[key] = {
            "username": username,
            "coins": reward,
            "puzzles_solved": 1,
        }
    else:
        entry["username"] = username
        entry["coins"] += reward
        entry["puzzles_solved"] += 1


async def _flush_pending_fill_scores():
    if not _PENDING_FILL_SCORES:
        return
    pending = list(_PENDING_FILL_SCORES.items())
    _PENDING_FILL_SCORES.clear()
    now = int(time.time())
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            rows = [
                (
                    user_id, chat_id, data["username"], data["coins"],
                    data["puzzles_solved"], data["coins"],
                    data["puzzles_solved"], data["username"],
                )
                for (user_id, chat_id), data in pending
            ]
            await db.executemany(
                "INSERT INTO fill_blank_scores "
                "(user_id, chat_id, username, coins, puzzles_solved) "
                "VALUES (?, ?, ?, ?, ?) "
                "ON CONFLICT(user_id, chat_id) DO UPDATE SET "
                "coins = coins + ?, puzzles_solved = puzzles_solved + ?, "
                "username = ?",
                rows,
            )
            await db.executemany(
                "INSERT INTO fill_blank_history "
                "(user_id, chat_id, username, coins_delta, recorded_at) "
                "VALUES (?, ?, ?, ?, ?)",
                [
                    (user_id, chat_id, data["username"], data["coins"], now)
                    for (user_id, chat_id), data in pending
                ],
            )
            await db.commit()
    except Exception as e:
        logger.error(f"Fill-the-blanks score flush failed: {e}")
        for key, data in pending:
            existing = _PENDING_FILL_SCORES.get(key)
            if existing is None:
                _PENDING_FILL_SCORES[key] = data
            else:
                existing["coins"] += data["coins"]
                existing["puzzles_solved"] += data["puzzles_solved"]
                existing["username"] = data["username"]


async def heartbeat_logger():
    while True:
        try:
            await asyncio.sleep(300)
            rss = _read_rss_mb()
            rss_str = f"{rss:.0f}MB" if rss is not None else "n/a"
            uptime = _format_uptime(time.time() - _BOT_START)
            active_pipes = sum(
                1 for p in _PIPELINES.values()
                if p.worker_task and not p.worker_task.done()
            )
            max_pipe_q = max(
                (p.queue.qsize() for p in _PIPELINES.values()), default=0
            )
            logger.info(
                f"[heartbeat] up={uptime} mem={rss_str} "
                f"games={len(games)} pipes={active_pipes} "
                f"qmax={max_pipe_q} deferred={len(_DEFERRED_SCORE_QUEUE)} "
                f"pending_users={len(_PENDING_USER_IDS)} "
                f"loop={'uvloop' if _UVLOOP_ENABLED else 'asyncio'}"
            )
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"heartbeat_logger error: {e}")


async def _flush_ftb_pending(deferred_entries: list):
    """Zero-lag database flush for FTB mode."""
    chat_ids_to_clear = [c for _, c in deferred_entries]
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            for pending_scores, chat_id in deferred_entries:
                if pending_scores:
                    await db.executemany(
                        "INSERT OR IGNORE INTO users (user_id) VALUES (?)",
                        [(uid,) for uid in pending_scores],
                    )
                    score_rows = [
                        (uid, chat_id, data["username"], data["score"],
                         data.get("games_played", 0), data.get("words_found", 0),
                         data["score"], data["username"],
                         data.get("games_played", 0), data.get("words_found", 0))
                        for uid, data in pending_scores.items()
                    ]
                    await db.executemany(
                        "INSERT INTO ftb_scores "
                        "(user_id, chat_id, username, score, games_played, words_found) "
                        "VALUES (?, ?, ?, ?, ?, ?) "
                        "ON CONFLICT(user_id, chat_id) DO UPDATE SET "
                        "score = score + ?, username = ?, "
                        "games_played = games_played + ?, words_found = words_found + ?",
                        score_rows,
                    )
                    ts = int(time.time())
                    await db.executemany(
                        "INSERT INTO ftb_history "
                        "(user_id, chat_id, username, score_delta, recorded_at) "
                        "VALUES (?, ?, ?, ?, ?)",
                        [(uid, chat_id, data["username"], data["score"], ts)
                         for uid, data in pending_scores.items()],
                    )
            await db.commit()
    except Exception as e:
        logger.error(f"FTB batch flush failed: {e}")
    finally:
        for cid in chat_ids_to_clear:
            _FLUSHING_CHATS.discard(cid)

async def background_writer():
    while True:
        try:
            await asyncio.sleep(30)
            now = time.time()
            still_waiting = []
            ready_entries = []
            for entry in _DEFERRED_SCORE_QUEUE:
                flush_at, pending_scores, chat_id, set_id = entry
                if chat_id in games:
                    still_waiting.append(entry)
                    continue
                if now >= flush_at and chat_id not in _FLUSHING_CHATS:
                    _FLUSHING_CHATS.add(chat_id)
                    ready_entries.append((pending_scores, chat_id, set_id))
                else:
                    still_waiting.append(entry)
            _DEFERRED_SCORE_QUEUE.clear()
            _DEFERRED_SCORE_QUEUE.extend(still_waiting)

            # Process FTB Queue
            still_waiting_ftb = []
            ready_entries_ftb = []
            for entry in _DEFERRED_FTB_QUEUE:
                flush_at, pending_scores, chat_id = entry
                if chat_id in games:
                    still_waiting_ftb.append(entry)
                    continue
                if now >= flush_at and chat_id not in _FLUSHING_CHATS:
                    _FLUSHING_CHATS.add(chat_id)
                    ready_entries_ftb.append((pending_scores, chat_id))
                else:
                    still_waiting_ftb.append(entry)
            _DEFERRED_FTB_QUEUE.clear()
            _DEFERRED_FTB_QUEUE.extend(still_waiting_ftb)

            pending_users = list(_PENDING_USER_IDS)
            _PENDING_USER_IDS.clear()

            global _PENDING_GAMES_COUNT
            games_to_save = _PENDING_GAMES_COUNT
            _PENDING_GAMES_COUNT = 0

            if ready_entries or pending_users or games_to_save > 0:
                asyncio.create_task(_flush_all_pending(ready_entries, pending_users, games_to_save))
                
            if ready_entries_ftb:
                asyncio.create_task(_flush_ftb_pending(ready_entries_ftb))
                
            if _PENDING_FILL_SCORES:
                asyncio.create_task(_flush_pending_fill_scores())

            if len(_NEWGAME_COOLDOWN) > MAX_COOLDOWN_ENTRIES:
                cutoff = now - NEWGAME_COOLDOWN_SECS
                for k in list(_NEWGAME_COOLDOWN):
                    if _NEWGAME_COOLDOWN[k] < cutoff:
                        del _NEWGAME_COOLDOWN[k]

            if _DM_NEW_COOLDOWN:
                dm_cutoff = now - 10
                for k in list(_DM_NEW_COOLDOWN):
                    if _DM_NEW_COOLDOWN[k] < dm_cutoff:
                        del _DM_NEW_COOLDOWN[k]

            cmd_cutoff = now - 300
            for cd in (_CMD_COOLDOWN, _STATS_COOLDOWN, _TOP10_COOLDOWN, _LB_COOLDOWN, _TOPCHATS_COOLDOWN):
                if cd:
                    for k in list(cd):
                        if cd[k] < cmd_cutoff:
                            del cd[k]

            if _LB_USER_CD:
                lb_cutoff = now - 60
                for k in list(_LB_USER_CD):
                    if _LB_USER_CD[k] < lb_cutoff:
                        del _LB_USER_CD[k]

            global _LAST_HISTORY_CLEANUP
            if now - _LAST_HISTORY_CLEANUP > 86400:
                _LAST_HISTORY_CLEANUP = now
                asyncio.create_task(_cleanup_score_history())

            if len(_ADMIN_CACHE) > ADMIN_CACHE_MAX:
                while len(_ADMIN_CACHE) > ADMIN_CACHE_MAX // 2:
                    _ADMIN_CACHE.popitem(last=False)
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"background_writer error: {e}")

async def global_ticker():
    while True:
        try:
            await asyncio.sleep(TICK_INTERVAL)
            wall_now = time.monotonic()
            for chat_id in list(games.keys()):
                game = games.get(chat_id)
                if not game or game.get("ending"):
                    continue
                if wall_now - game.get("last_activity", wall_now) > INACTIVITY_TIMEOUT:
                    if game.get("game_type") == "ftb":
                        asyncio.create_task(end_ftb_game(chat_id, reason="stopped"))
                    else:
                        asyncio.create_task(end_scramble_game(chat_id, reason="stopped"))
        except asyncio.CancelledError:
            return
        except Exception as e:
            logger.error(f"global_ticker error: {e}")


# ---------------------------------------------------------------------------
# Read-only DB queries
# ---------------------------------------------------------------------------
async def get_top_10(chat_id: int):
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT username, score FROM scramble_scores "
            "WHERE chat_id = ? ORDER BY score DESC LIMIT 10",
            (chat_id,),
        )
        return await cur.fetchall()
    except Exception:
        return []


async def get_global_top_10():
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT user_id, MAX(username) as username, SUM(score) as total_score "
            "FROM scramble_scores GROUP BY user_id "
            "ORDER BY total_score DESC LIMIT 10"
        )
        return await cur.fetchall()
    except Exception:
        return []


async def get_top_chats():
    """Top 10 chats by total score. Excludes private DMs (chat_id < 0)."""
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT chat_id, SUM(score) as total FROM scramble_scores "
            "WHERE chat_id < 0 GROUP BY chat_id "
            "ORDER BY total DESC LIMIT 10"
        )
        return await cur.fetchall()
    except Exception:
        return []




# Chat-info cache for /topchats
_CHAT_INFO_CACHE: "OrderedDict[int, tuple]" = OrderedDict()
CHAT_INFO_TTL = 600.0      # 10 minutes
CHAT_INFO_MAX = 5000


async def _get_chat_info_cached(chat_id: int):
    now = time.monotonic()
    cached = _CHAT_INFO_CACHE.get(chat_id)
    if cached and cached[2] > now:
        _CHAT_INFO_CACHE.move_to_end(chat_id)
        return cached[0], cached[1]
    title = None
    url = None
    try:
        await GLOBAL_RL.acquire()
        chat = await bot.get_chat(chat_id)
        title = chat.title or None
        if getattr(chat, "username", None):
            url = f"https://t.me/{chat.username}"
        elif getattr(chat, "invite_link", None):
            url = chat.invite_link
        else:
            try:
                await GLOBAL_RL.acquire()
                url = await bot.export_chat_invite_link(chat_id)
            except Exception:
                pass
    except (TelegramForbiddenError, TelegramBadRequest) as e:
        logger.debug(f"_get_chat_info_cached drop chat={chat_id}: {e}")
    except Exception as e:
        logger.debug(f"_get_chat_info_cached error chat={chat_id}: {e}")
    _CHAT_INFO_CACHE[chat_id] = (title, url, now + CHAT_INFO_TTL)
    _CHAT_INFO_CACHE.move_to_end(chat_id)
    while len(_CHAT_INFO_CACHE) > CHAT_INFO_MAX:
        _CHAT_INFO_CACHE.popitem(last=False)
    return title, url


async def get_user_stats(user_id: int):
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT SUM(score), SUM(games_played), SUM(words_found) "
            "FROM scramble_scores WHERE user_id = ?", (user_id,))
        row = await cur.fetchone()
        total_score = row[0] if row and row[0] is not None else 0
        games_played = row[1] if row and row[1] is not None else 0
        words_found = row[2] if row and row[2] is not None else 0
        cur = await db.execute(
            "SELECT longest_word FROM scramble_scores "
            "WHERE user_id = ? AND longest_word != '' "
            "ORDER BY length(longest_word) DESC LIMIT 1",
            (user_id,),
        )
        lw_row = await cur.fetchone()
        longest_word = lw_row[0] if lw_row and lw_row[0] else ""
        if total_score > 0:
            cur = await db.execute(
                "SELECT COUNT(*) + 1 FROM ("
                "SELECT SUM(score) AS user_total FROM scramble_scores "
                "GROUP BY user_id HAVING user_total > ?)",
                (total_score,),
            )
            rank_row = await cur.fetchone()
            rank = rank_row[0] if rank_row else 1
        else:
            cur = await db.execute(
                "SELECT COUNT(*) + 1 FROM ("
                "SELECT SUM(score) AS user_total FROM scramble_scores "
                "GROUP BY user_id HAVING user_total > 0)"
            )
            count_row = await cur.fetchone()
            rank = count_row[0] if count_row else 1
        return total_score, rank, games_played, words_found, longest_word
    except Exception:
        return 0, 1, 0, 0, ""


async def _cleanup_score_history():
    try:
        cutoff = int(time.time()) - 365 * 86400
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute(
                "DELETE FROM score_history WHERE recorded_at < ?", (cutoff,))
            await db.commit()
    except Exception as e:
        logger.error(f"_cleanup_score_history error: {e}")


def _period_since(period: str) -> int:
    now = int(time.time())
    if period == "today":
        return now - (now % 86400)
    elif period == "weekly":
        return now - 7 * 86400
    elif period == "monthly":
        return now - 30 * 86400
    elif period == "yearly":
        return now - 365 * 86400
    return 0


async def get_leaderboard_data(scope: str, period: str, chat_id: int):
    try:
        db = await get_read_db()
        if period == "alltime":
            if scope == "global":
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score) as total "
                    "FROM scramble_scores GROUP BY user_id "
                    "ORDER BY total DESC LIMIT 10"
                )
            else:
                cur = await db.execute(
                    "SELECT username, score as total FROM scramble_scores "
                    "WHERE chat_id = ? ORDER BY total DESC LIMIT 10",
                    (chat_id,),
                )
        else:
            since = _period_since(period)
            if scope == "global":
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score_delta) as total "
                    "FROM score_history WHERE recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (since,),
                )
            else:
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score_delta) as total "
                    "FROM score_history WHERE chat_id = ? AND recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (chat_id, since),
                )
        rows = await cur.fetchall()
        return [(row[0], row[1]) for row in rows]
    except Exception:
        return []


async def get_fill_leaderboard_data(scope: str, period: str, chat_id: int):
    try:
        db = await get_read_db()
        if period == "alltime":
            if scope in ("fill_global", "fill"):
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(coins) as total "
                    "FROM fill_blank_scores GROUP BY user_id "
                    "ORDER BY total DESC LIMIT 10"
                )
            else: # "fill_group"
                cur = await db.execute(
                    "SELECT username, coins as total FROM fill_blank_scores "
                    "WHERE chat_id = ? ORDER BY total DESC LIMIT 10",
                    (chat_id,)
                )
        else:
            since = _period_since(period)
            if scope in ("fill_global", "fill"):
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(coins_delta) as total "
                    "FROM fill_blank_history WHERE recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (since,),
                )
            else: # "fill_group"
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(coins_delta) as total "
                    "FROM fill_blank_history WHERE chat_id = ? AND recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (chat_id, since),
                )
        rows = await cur.fetchall()
        return [(row[0], row[1]) for row in rows]
    except Exception:
        return []


async def get_longest_words():
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT username, longest_word FROM scramble_scores "
            "WHERE longest_word != '' "
            "ORDER BY length(longest_word) DESC LIMIT 10"
        )
        rows = await cur.fetchall()
        return [(row[0], row[1]) for row in rows]
    except Exception:
        return []





# ---------------------------------------------------------------------------
# Game text generation
# ---------------------------------------------------------------------------
def generate_scramble_text(game: dict) -> str:
    return (
        f"{P_PENCIL} WORD SCRAMBLE\n\n"
        f"{P_LETTERS} Make words using these letters\n\n"
        f"{P_ARROW} {_boldify_letters(game['letters'])}\n\n"
        f"{P_OK} 3–12 letter words are accepted\n"
        f"Total: {len(game['found'])}/{game['total_words']}"
    )


# ---------------------------------------------------------------------------
# Game log writer (non-blocking — fires and forgets on game end)
# ---------------------------------------------------------------------------
async def _log_game(chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute(
                "INSERT INTO game_log (chat_id, played_at) VALUES (?, ?)",
                (chat_id, int(time.time())),
            )
            await db.commit()
    except Exception as e:
        logger.error(f"_log_game error chat={chat_id}: {e}")


# ---------------------------------------------------------------------------
# Game lifecycle
# ---------------------------------------------------------------------------
async def end_scramble_game(chat_id: int, reason: str = "win"):
    global _PENDING_GAMES_COUNT
    try:
        game = games.pop(chat_id, None)
        if not game:
            return
        game["ending"] = True
        asyncio.create_task(_log_game(chat_id))
        _PENDING_GAMES_COUNT += 1

        pending_scores = game.get("pending_db_scores", {})
        for uid in pending_scores:
            pending_scores[uid]["games_played"] = 1
        set_id = game.get("set_id")
        flush_at = time.time() + 900
        _DEFERRED_SCORE_QUEUE.append((flush_at, pending_scores, chat_id, set_id))

        if len(_DEFERRED_SCORE_QUEUE) > MAX_DEFERRED_QUEUE:
            overflow = _DEFERRED_SCORE_QUEUE[:1000]
            del _DEFERRED_SCORE_QUEUE[:1000]
            asyncio.create_task(
                _flush_all_pending([(ps, c, s) for _, ps, c, s in overflow], [], 0))

        if reason == "stopped":
            end_text = (
                f"<blockquote>{P_OVER} Game over {P_OVER}\n"
                f"Nobody guessed a new word in last 5 minutes ⏰</blockquote>\n\n"
            )
        else:
            end_text = f"<blockquote>{P_OVER} Game over {P_OVER}</blockquote>\n\n"

        round_scores = game.get("user_scores", {})
        if not round_scores:
            end_text += f"<blockquote>{P_SCORES} Scores\n\nNo words found.</blockquote>\n\n"
        else:
            scores_text = f"{P_SCORES} Scores\n\n"
            sorted_users = sorted(round_scores.items(),
                                  key=lambda kv: kv[1]["score"], reverse=True)
            for i, (uid, entry) in enumerate(sorted_users, start=1):
                scores_text += f"{i}. {html.escape(entry['name'])} - {entry['score']} points {P_DIAMOND}\n"
            end_text += f"<blockquote>{scores_text.strip()}</blockquote>\n\n"

            longest_map = game.get("user_words", {})
            longest_lines = []
            for uid, entry in sorted_users:
                word = longest_map.get(uid)
                if word:
                    longest_lines.append(
                        f"{html.escape(word.capitalize())} - {html.escape(entry['name'])}"
                    )
            if longest_lines:
                end_text += (
                    "<blockquote>Longest words:\n"
                    + "\n".join(longest_lines)
                    + "</blockquote>\n\n"
                )

        end_text += "<blockquote>/new - Start new game</blockquote>"

        await queue_send(chat_id, end_text, reply_markup=END_GAME_KB)
        if _ADDT_TEXT:
            _addt_snapshot = _ADDT_TEXT
            async def _send_addt(cid=chat_id, txt=_addt_snapshot):
                await asyncio.sleep(3)
                await queue_send(cid, txt)
            asyncio.create_task(_send_addt())
    except Exception as e:
        logger.error(f"end_scramble_game error chat={chat_id}: {e}")


async def start_scramble_game(chat_id: int, starter_id: int):
    if chat_id in games or chat_id in pending_games:
        return
        
    # Never keep two interactive word challenges active in the same group.
    # Marks the puzzle as expired so the background cleaner deletes the message.
    puzzle = fill_puzzles.get(chat_id)
    if puzzle:
        puzzle["expires_at"] = 0
        
    now = time.time()
    if now - _NEWGAME_COOLDOWN.get(chat_id, 0) < NEWGAME_COOLDOWN_SECS:
        return
    _NEWGAME_COOLDOWN[chat_id] = now

    pending_games.add(chat_id)
    try:
        chosen_id, chosen_set = await pick_scramble_set(chat_id)
        letters = chosen_set["letters"]
        target_words = PRECOMPUTED_WORDS.get(chosen_id) or _find_valid_words(letters)
        total_words_count = min(20, len(target_words))

        if chat_id in games:
            return

        game = {
            "game_type": "scramble",
            "set_id": chosen_id,
            "letters": letters,
            "target_words": target_words,
            "total_words": total_words_count,
            "found": [],
            "found_set": set(),
            "user_scores": {},
            "user_words": {},
            "pending_db_scores": {},
            "lock": asyncio.Lock(),
            "starter_id": starter_id,
            "last_activity": time.monotonic(),
            "display_letters": _boldify_letters(letters.replace(",", "")),
            "ending": False,
            "main_msg_id": None,
            "last_hint_time": 0.0,
        }
        games[chat_id] = game

        cache = PLAYED_SETS_CACHE.get(chat_id)
        if cache is None:
            PLAYED_SETS_CACHE[chat_id] = {chosen_id}
        else:
            cache.add(chosen_id)

        text = generate_scramble_text(game)
        sent_msg = await queue_send_and_wait(chat_id, text, protect_content=True)
        if sent_msg:
            game["main_msg_id"] = sent_msg.message_id
        else:
            games.pop(chat_id, None)
    except Exception as e:
        logger.error(f"start_scramble_game error chat={chat_id}: {e}")
        games.pop(chat_id, None)
        await queue_send(chat_id, "❌ Couldn't start the game. Please try again.")
    finally:
        pending_games.discard(chat_id)



async def get_all_group_ids():
    """Return known group IDs with one read-only query for hourly dispatch."""
    try:
        db = await get_read_db()
        cur = await db.execute(
            "SELECT chat_id FROM tracked_groups WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM played_scramble_sets WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM scramble_scores WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM ftb_scores WHERE chat_id < 0"
        )
        return [row[0] for row in await cur.fetchall()]
    except Exception:
        return []

async def send_fill_blank_puzzles():
    """Queue one independent 20-minute puzzle per eligible group and track stats."""
    group_ids = list(set(await get_all_group_ids()))
    
    targeted = len(group_ids)
    sent_count = 0
    skipped = 0
    kicked = 0
    restricted = 0
    other_errors = 0

    for chat_id in group_ids:
        # Skips if admin turned puzzles off, OR if a Scramble/FTB game is active (chat_id in games)
        if chat_id in _PUZZLES_OFF or chat_id in games or chat_id in pending_games or chat_id in fill_puzzles:
            skipped += 1
            continue

        puzzle = _create_fill_puzzle()
        if puzzle is None:
            continue

        try:
            sent_msg = await rate_limited_call(
                bot.send_message(chat_id, _fill_puzzle_text(puzzle))
            )
            fill_puzzles[chat_id] = puzzle
            puzzle["message_id"] = sent_msg.message_id
            sent_count += 1
        except TelegramForbiddenError:
            kicked += 1 
        except TelegramBadRequest:
            restricted += 1 
        except TelegramRetryAfter as e:
            await asyncio.sleep(e.retry_after + 0.5)
            try:
                sent_msg = await rate_limited_call(
                    bot.send_message(chat_id, _fill_puzzle_text(puzzle))
                )
                fill_puzzles[chat_id] = puzzle
                puzzle["message_id"] = sent_msg.message_id
                sent_count += 1
            except Exception:
                other_errors += 1
        except Exception:
            other_errors += 1

        await asyncio.sleep(FILL_SEND_DELAY)

    global _LAST_PUZZLE_STATS
    _LAST_PUZZLE_STATS["targeted"] = targeted
    _LAST_PUZZLE_STATS["sent"] = sent_count
    _LAST_PUZZLE_STATS["skipped"] = skipped
    _LAST_PUZZLE_STATS["kicked"] = kicked
    _LAST_PUZZLE_STATS["restricted"] = restricted
    _LAST_PUZZLE_STATS["other"] = other_errors

    report = (
        f"📊 Puzzle Broadcast Targeted: {targeted}\n\n"
        f"✅ Sent: {sent_count}\n"
        f"⏭ Skipped (active game or turned off): {skipped}\n"
        f"🚫 Kicked/Blocked: {kicked}\n"
        f"🔒 Restricted/Upgraded: {restricted}\n"
        f"⚠️ Network/Other errors: {other_errors}"
    )
    
    if NOTIFICATION_GROUP:
        asyncio.create_task(queue_send(NOTIFICATION_GROUP, report))
    elif ADMIN_IDS:
        admin_id = list(ADMIN_IDS)[0]
        asyncio.create_task(queue_send(admin_id, report))


async def fill_blank_scheduler():
    """Run the challenge broadcast 5 mins after restart, then exactly at the top of the hour in IST."""
    
    # 1. FIRST RUN: Wait exactly 5 minutes (300 seconds) after turning the server on
    try:
        await asyncio.sleep(300)
        await send_fill_blank_puzzles()
    except asyncio.CancelledError:
        return
    except Exception as e:
        logger.error(f"Initial puzzle broadcast error: {e}")

    # 2. CONTINUOUS RUN: Fall into the permanent top-of-the-hour loop for all future puzzles
    while True:
        try:
            now = time.time()
            # Add 5 hours and 30 minutes (19,800 seconds) to sync to IST
            ist_now = now + 19800 
            
            # Calculate seconds until the next IST hour mark (XX:00)
            next_ist_hour = (int(ist_now) // 3600 + 1) * 3600
            sleep_seconds = next_ist_hour - ist_now
            
            await asyncio.sleep(sleep_seconds)
            await send_fill_blank_puzzles()
            
        except asyncio.CancelledError:
            return
        except Exception as e:
            logger.error(f"fill_blank_scheduler error: {e}")
            await asyncio.sleep(60)  # Fallback to prevent rapid looping on error


async def fill_puzzle_cleanup():
    """Delete unanswered challenge messages without blocking message handling."""
    while True:
        try:
            await asyncio.sleep(FILL_CLEANUP_INTERVAL)
            now = time.monotonic()
            expired = []
            for chat_id, puzzle in list(fill_puzzles.items()):
                if now >= puzzle.get("expires_at", 0):
                    # Remove the state before awaiting Telegram so a late
                    # answer cannot win while the cleanup request is in flight.
                    if fill_puzzles.get(chat_id) is puzzle:
                        fill_puzzles.pop(chat_id, None)
                        expired.append((chat_id, puzzle))

            for chat_id, puzzle in expired:
                message_id = puzzle.get("message_id")
                if message_id is not None:
                    try:
                        await GLOBAL_RL.acquire()
                        await bot.delete_message(
                            chat_id=chat_id,
                            message_id=message_id,
                        )
                    except Exception:
                        # Missing delete permission, an already-deleted
                        # message, or any other Telegram error must not stop
                        # cleanup for the remaining groups.
                        pass
                await asyncio.sleep(FILL_DELETE_DELAY)
        except asyncio.CancelledError:
            return
        except Exception as e:
            logger.error(f"fill_puzzle_cleanup error: {e}")


# ---------------------------------------------------------------------------
# Single global ticker (replaces per-game timer task)
# ---------------------------------------------------------------------------
TICK_INTERVAL = 30.0
INACTIVITY_TIMEOUT = 300  # 5 minutes


async def global_ticker():
    while True:
        try:
            await asyncio.sleep(TICK_INTERVAL)
            wall_now = time.monotonic()
            for chat_id in list(games.keys()):
                game = games.get(chat_id)
                if not game or game.get("ending"):
                    continue
                if wall_now - game.get("last_activity", wall_now) > INACTIVITY_TIMEOUT:
                    asyncio.create_task(end_scramble_game(chat_id, reason="stopped"))
        except asyncio.CancelledError:
            return
        except Exception as e:
            logger.error(f"global_ticker error: {e}")


# ---------------------------------------------------------------------------
# Admin status cache
# ---------------------------------------------------------------------------
async def is_user_admin(chat_id: int, user_id: int) -> bool:
    key = (chat_id, user_id)
    now = time.monotonic()
    cached = _ADMIN_CACHE.get(key)
    if cached and now - cached[1] < ADMIN_CACHE_TTL:
        _ADMIN_CACHE.move_to_end(key)
        return cached[0]
    try:
        member = await asyncio.wait_for(
            rate_limited_call(bot.get_chat_member(chat_id, user_id)),
            timeout=5.0,
        )
        is_admin = member.status in ("administrator", "creator")
    except Exception:
        return False
    _ADMIN_CACHE[key] = (is_admin, now)
    if len(_ADMIN_CACHE) > ADMIN_CACHE_MAX:
        _ADMIN_CACHE.popitem(last=False)
    return is_admin


# ---------------------------------------------------------------------------
# Admin score-update background task
# ---------------------------------------------------------------------------
async def _background_update_score(user_id: int, new_score: int, admin_chat_id: int):
    try:
        db_read = await get_read_db()
        cur = await db_read.execute(
            "SELECT username FROM scramble_scores WHERE user_id = ? LIMIT 1",
            (user_id,),
        )
        row = await cur.fetchone()
        username = row[0] if row else "Unknown Player"
        try:
            chat = await rate_limited_call(bot.get_chat(user_id))
            username = chat.first_name or chat.username or username
        except Exception:
            pass
        async with _DB_WRITE_LOCK:
            db = await get_db()
            cur = await db.execute(
                "SELECT rowid FROM scramble_scores WHERE user_id = ? ORDER BY score DESC LIMIT 1",
                (user_id,),
            )
            existing = await cur.fetchone()
            if existing:
                target_rowid = existing[0]
                await db.execute(
                    "UPDATE scramble_scores SET score = 0 WHERE user_id = ?", (user_id,))
                await db.execute(
                    "UPDATE scramble_scores SET score = ?, username = ? WHERE rowid = ?",
                    (new_score, username, target_rowid),
                )
            else:
                await db.execute(
                    "INSERT INTO scramble_scores (user_id, chat_id, username, score) "
                    "VALUES (?, ?, ?, ?)",
                    (user_id, admin_chat_id, username, new_score),
                )
            await db.commit()
        await queue_send(
            admin_chat_id,
            f"✅ Background update complete.\n"
            f"👤 <a href='tg://user?id={user_id}'>{html.escape(username)}</a>'s "
            f"score is now {new_score}.",
        )
    except Exception as e:
        logger.error(f"background score update error user={user_id}: {e}")
        await queue_send(admin_chat_id, f"❌ Failed to update score for {user_id}.")


# ---------------------------------------------------------------------------
# Reset user background task
# ---------------------------------------------------------------------------
async def _background_del_group(gid: int, admin_chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM scramble_scores WHERE chat_id = ?", (gid,))
            await db.execute("DELETE FROM ftb_scores WHERE chat_id = ?", (gid,))
            await db.execute("DELETE FROM played_scramble_sets WHERE chat_id = ?", (gid,))
            await db.execute("DELETE FROM tracked_groups WHERE chat_id = ?", (gid,))
            await db.commit()
        await queue_send(
            admin_chat_id,
            f"✅ All data for group <code>{gid}</code> has been deleted.\n"
            f"(scores, played sets, tracking record)",
        )
    except Exception as e:
        logger.error(f"_background_del_group error: {e}")
        await queue_send(admin_chat_id, f"❌ Delete failed: {e}")


async def _background_reset_user(user_id: int, admin_chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM scramble_scores WHERE user_id = ?", (user_id,))
            await db.execute("DELETE FROM score_history WHERE user_id = ?", (user_id,))
            await db.execute("DELETE FROM ftb_scores WHERE user_id = ?", (user_id,))
            await db.execute("DELETE FROM ftb_history WHERE user_id = ?", (user_id,))
            await db.commit()
        await queue_send(
            admin_chat_id,
            f"✅ Reset complete.\n"
            f"All scores and history for <code>{user_id}</code> have been wiped.",
        )
    except Exception as e:
        logger.error(f"_background_reset_user error: {e}")
        await queue_send(admin_chat_id, f"❌ Reset failed: {e}")



# ---------------------------------------------------------------------------
# Delete group data background task
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Transfer user ID background task
# ---------------------------------------------------------------------------
async def _background_transfer_user(user_id_a: int, user_id_b: int, admin_chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("INSERT OR IGNORE INTO users (user_id) VALUES (?)", (user_id_b,))
            cur = await db.execute(
                "SELECT chat_id, username, score, games_played, words_found, longest_word "
                "FROM scramble_scores WHERE user_id = ?", (user_id_a,))
            a_rows = await cur.fetchall()
            if not a_rows:
                await db.commit()
                await queue_send(admin_chat_id, f"⚠️ User <code>{user_id_a}</code> has no score records.")
                return
            for row in a_rows:
                chat_id_r = row[0]
                username = row[1]
                score_a = row[2] or 0
                gp_a = row[3] or 0
                wf_a = row[4] or 0
                lw_a = row[5] or ""
                cur2 = await db.execute(
                    "SELECT score, games_played, words_found, longest_word "
                    "FROM scramble_scores WHERE user_id = ? AND chat_id = ?",
                    (user_id_b, chat_id_r))
                b_row = await cur2.fetchone()
                if b_row:
                    new_score = (b_row[0] or 0) + score_a
                    new_gp = (b_row[1] or 0) + gp_a
                    new_wf = (b_row[2] or 0) + wf_a
                    lw_b = b_row[3] or ""
                    new_lw = lw_a if len(lw_a) > len(lw_b) else lw_b
                    await db.execute(
                        "UPDATE scramble_scores SET score = ?, games_played = ?, "
                        "words_found = ?, longest_word = ? "
                        "WHERE user_id = ? AND chat_id = ?",
                        (new_score, new_gp, new_wf, new_lw, user_id_b, chat_id_r))
                else:
                    await db.execute(
                        "INSERT INTO scramble_scores "
                        "(user_id, chat_id, username, score, games_played, words_found, longest_word) "
                        "VALUES (?, ?, ?, ?, ?, ?, ?)",
                        (user_id_b, chat_id_r, username, score_a, gp_a, wf_a, lw_a))
            await db.execute("DELETE FROM scramble_scores WHERE user_id = ?", (user_id_a,))
            await db.execute(
                "UPDATE score_history SET user_id = ? WHERE user_id = ?",
                (user_id_b, user_id_a))
            await db.commit()
        await queue_send(
            admin_chat_id,
            f"✅ Transfer complete.\n"
            f"Scores of <code>{user_id_a}</code> have been transferred to "
            f"<code>{user_id_b}</code>.\n"
            f"Affected {len(a_rows)} chat record(s).",
        )
    except Exception as e:
        logger.error(f"_background_transfer_user error: {e}")
        await queue_send(admin_chat_id, f"❌ Transfer failed: {e}")


# ---------------------------------------------------------------------------
# Group tracking
# ---------------------------------------------------------------------------
async def _async_track_group(chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute(
                "INSERT OR IGNORE INTO tracked_groups (chat_id) VALUES (?)", (chat_id,))
            await db.commit()
    except Exception as e:
        logger.error(f"track_group error chat={chat_id}: {e}")


async def _async_untrack_group(chat_id: int):
    try:
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM tracked_groups WHERE chat_id = ?", (chat_id,))
            await db.commit()
    except Exception as e:
        logger.error(f"untrack_group error chat={chat_id}: {e}")


# ---------------------------------------------------------------------------
# Handlers
# ---------------------------------------------------------------------------
@dp.my_chat_member()
async def on_bot_added_to_group(event: ChatMemberUpdated):
    try:
        chat = event.chat
        if (event.new_chat_member.status in ("member", "administrator")
                and event.old_chat_member.status not in ("member", "administrator")):
            if chat.id < 0:
                asyncio.create_task(_async_track_group(chat.id))
            if chat.username:
                link = f"@{chat.username}"
            else:
                try:
                    full_chat = await rate_limited_call(bot.get_chat(chat.id))
                    link = full_chat.invite_link or "Private Group (No public link)"
                except Exception:
                    link = "Private Group (No public link)"
            try:
                member_count = await rate_limited_call(bot.get_chat_member_count(chat.id))
            except Exception:
                member_count = "Unknown"
            adder_name = html.escape(event.from_user.first_name or "Unknown")
            text = (
                f"🟢 NEW GROUP ADDED\n\n"
                f"@Shivansh771\n\n"
                f"Name: {html.escape(chat.title or '')}\n"
                f"ID: <code>{chat.id}</code>\n"
                f"Link: {link}\n"
                f"Total group members: {member_count}\n"
                f"Added by: <a href='tg://user?id={event.from_user.id}'>{adder_name}</a> [<code>{event.from_user.id}</code>]"
            )
            if NOTIFICATION_GROUP:
                await queue_send(NOTIFICATION_GROUP, text)
        elif event.new_chat_member.status in ("left", "kicked"):
            if chat.id < 0:
                asyncio.create_task(_async_untrack_group(chat.id))
    except Exception as e:
        logger.error(f"on_bot_added_to_group error: {e}")


def _is_admin_only(message: Message) -> bool:
    # Allows both the .env owner AND promoted admins
    return bool(message.from_user and message.from_user.id in (ADMIN_IDS | _PROMOTED_ADMINS))

def _is_bot_creator(message: Message) -> bool:
    # Strictly limits access to the .env owner only
    return bool(message.from_user and message.from_user.id in ADMIN_IDS)


@dp.message(Command("addt", ignore_case=True))
async def cmd_addt(message: Message):
    global _ADDT_TEXT
    try:
        if not _is_admin_only(message):
            return
        text = message.text or ""
        parts = text.split(None, 1)
        if len(parts) < 2 or not parts[1].strip():
            await queue_send(message.chat.id, "⚠️ Usage: /addt <text to send after results>")
            return
        _ADDT_TEXT = parts[1].strip()
        await queue_send(message.chat.id, f"✅ Trailer text set:\n\n{_ADDT_TEXT}")
    except Exception as e:
        logger.error(f"cmd_addt error: {e}")


@dp.message(Command("rmt", ignore_case=True))
async def cmd_rmt(message: Message):
    global _ADDT_TEXT
    try:
        if not _is_admin_only(message):
            return
        _ADDT_TEXT = ""
        await queue_send(message.chat.id, "✅ Trailer text removed. Nothing will be sent after results.")
    except Exception as e:
        logger.error(f"cmd_rmt error: {e}")


@dp.message(Command("banit", ignore_case=True))
async def cmd_banit(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /banit <user_id>")
            return
        uid = int(parts[1])
        _BANNED_USERS.add(uid)
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute(
                "INSERT OR IGNORE INTO banned_users (user_id) VALUES (?)", (uid,))
            await db.commit()
        await queue_send(message.chat.id, f"✅ User {uid} has been banned from the bot.")
    except ValueError:
        await queue_send(message.chat.id, "⚠️ Invalid user ID.")
    except Exception as e:
        logger.error(f"cmd_banit error: {e}")


@dp.message(Command("unbanit", ignore_case=True))
async def cmd_unbanit(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /unbanit <user_id>")
            return
        uid = int(parts[1])
        _BANNED_USERS.discard(uid)
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM banned_users WHERE user_id = ?", (uid,))
            await db.commit()
        await queue_send(message.chat.id, f"✅ User {uid} has been unbanned.")
    except ValueError:
        await queue_send(message.chat.id, "⚠️ Invalid user ID.")
    except Exception as e:
        logger.error(f"cmd_unbanit error: {e}")


@dp.message(Command("banitg", ignore_case=True))
async def cmd_banitg(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /banitg <chat_id>")
            return
        cid = int(parts[1])
        _BANNED_GROUPS.add(cid)
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute(
                "INSERT OR IGNORE INTO banned_groups (chat_id) VALUES (?)", (cid,))
            await db.commit()
        await queue_send(message.chat.id, f"✅ Group {cid} has been banned from the bot.")
    except ValueError:
        await queue_send(message.chat.id, "⚠️ Invalid chat ID.")
    except Exception as e:
        logger.error(f"cmd_banitg error: {e}")


@dp.message(Command("unbanitg", ignore_case=True))
async def cmd_unbanitg(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /unbanitg <chat_id>")
            return
        cid = int(parts[1])
        _BANNED_GROUPS.discard(cid)
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM banned_groups WHERE chat_id = ?", (cid,))
            await db.commit()
        await queue_send(message.chat.id, f"✅ Group {cid} has been unbanned.")
    except ValueError:
        await queue_send(message.chat.id, "⚠️ Invalid chat ID.")
    except Exception as e:
        logger.error(f"cmd_unbanitg error: {e}")


def _read_rss_mb():
    try:
        with open("/proc/self/status", "r") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) / 1024.0
    except Exception:
        return None
    return None


def _format_uptime(secs: float) -> str:
    secs = int(secs)
    d, r = divmod(secs, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    if d:
        return f"{d}d {h}h {m}m"
    if h:
        return f"{h}h {m}m {s}s"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


@dp.message(Command("health", ignore_case=True))
async def cmd_health(message: Message):
    try:
        if not _is_admin_only(message):
            return
        rss = _read_rss_mb()
        rss_str = f"{rss:.1f} MB" if rss is not None else "n/a"
        loop_str = "uvloop (fast)" if _UVLOOP_ENABLED else "asyncio (default)"
        uptime = _format_uptime(time.time() - _BOT_START)

        active_pipes = sum(
            1 for p in _PIPELINES.values()
            if p.worker_task and not p.worker_task.done()
        )
        max_pipe_q = max((p.queue.qsize() for p in _PIPELINES.values()), default=0)

        text = (
            f"<b>Wordly — Health</b>\n\n"
            f"<blockquote>"
            f"⏱ Uptime: {html.escape(uptime)}\n"
            f"💾 Memory (RSS): {rss_str}\n"
            f"⚙️ Event loop: {loop_str}\n"
            f"</blockquote>\n"
            f"<blockquote>"
            f"🎮 Active games: {len(games)}\n"
            f"🕐 Pending starts: {len(pending_games)}\n"
            f"📤 Active pipelines: {active_pipes}\n"
            f"📦 Largest pipeline queue: {max_pipe_q}\n"
            f"</blockquote>\n"
            f"<blockquote>"
            f"🗄 DB read pool: {len(_DB_READ_POOL)} conns\n"
            f"💽 SQLite cache: 10 MB / mmap: 32 MB\n"
            f"📚 Words loaded: {len(GLOBAL_WORDS_CACHE)}\n"
            f"🧮 Precomputed sets: {len(PRECOMPUTED_WORDS)}\n"
            f"</blockquote>\n"
            f"<blockquote>"
            f"⏳ Deferred score batches: {len(_DEFERRED_SCORE_QUEUE)}\n"
            f"👤 Pending users to flush: {len(_PENDING_USER_IDS)}\n"
            f"🛡 Admin cache: {len(_ADMIN_CACHE)} / {ADMIN_CACHE_MAX}\n"
            f"🎯 Played-sets cache: {len(PLAYED_SETS_CACHE)} / {MAX_PLAYED_SETS_CACHE}\n"
            f"🏷 Chat-info cache: {len(_CHAT_INFO_CACHE)} / {CHAT_INFO_MAX}\n"
            f"🚫 Banned users: {len(_BANNED_USERS)} / groups: {len(_BANNED_GROUPS)}\n"
            f"</blockquote>"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_health error: {e}")


@dp.message(Command("total", ignore_case=True))
async def cmd_total(message: Message):
    try:
        if not _is_admin_only(message):
            return
        db = await get_read_db()
        cur = await db.execute("SELECT COUNT(*) FROM users")
        row = await cur.fetchone()
        total_users = row[0] if row else 0
        cur = await db.execute(
            "SELECT stat_value FROM bot_stats WHERE stat_name = 'total_games'")
        row = await cur.fetchone()
        db_total_games = row[0] if row else 0
        global _PENDING_GAMES_COUNT
        real_total_games = db_total_games + _PENDING_GAMES_COUNT
        await queue_send(
            message.chat.id,
            f"📊 <b>Bot Statistics</b>\n\n"
            f"👥 Total unique users tracked: {total_users}\n"
            f"🎮 Total games played: {real_total_games}",
        )
    except Exception as e:
        logger.error(f"cmd_total error: {e}")

@dp.message(Command("groupstat", ignore_case=True))
async def cmd_groupstat(message: Message):
    try:
        # Security: Only Bot Creators can use this command
        if not _is_bot_creator(message):
            return
        
        # If the bot was just restarted and hasn't run a puzzle broadcast yet
        if not _LAST_PUZZLE_STATS:
            db = await get_read_db()
            cur = await db.execute(
                "SELECT COUNT(*) FROM ("
                "SELECT chat_id FROM tracked_groups WHERE chat_id < 0 UNION "
                "SELECT chat_id FROM played_scramble_sets WHERE chat_id < 0 UNION "
                "SELECT chat_id FROM scramble_scores WHERE chat_id < 0"
                ")"
            )
            row = await cur.fetchone()
            total = row[0] if row else 0
            await queue_send(
                message.chat.id,
                f"👑 Total groups in database: {total}\n\n"
                f"⏳ <i>Detailed stats will appear here after the first hourly puzzle broadcast runs.</i>"
            )
            return

        # Fetch stats from the latest background run
        targeted = _LAST_PUZZLE_STATS.get("targeted", 0)
        sent = _LAST_PUZZLE_STATS.get("sent", 0)
        skipped = _LAST_PUZZLE_STATS.get("skipped", 0)
        kicked = _LAST_PUZZLE_STATS.get("kicked", 0)
        restricted = _LAST_PUZZLE_STATS.get("restricted", 0)
        other = _LAST_PUZZLE_STATS.get("other", 0)

        # Math: The bot is currently alive and well in groups where it successfully sent 
        # a puzzle PLUS groups where it skipped sending because a game was already running.
        bot_in_groups = sent + skipped
        
        text = (
            f"👑 Total groups in database: {targeted}\n"
            f"🔥 Bot in total groups: {bot_in_groups}\n"
            f"🚫 Bot not in group: {kicked}\n"
            f"🔒 Bot restricted: {restricted}\n"
            f"⚠️ Other errors: {other}"
        )
        await queue_send(message.chat.id, text)
        
    except Exception as e:
        logger.error(f"cmd_groupstat error: {e}")



@dp.message(Command("groups", ignore_case=True))
async def cmd_groups(message: Message):
    try:
        if not _is_admin_only(message):
            return
        db = await get_read_db()
        cur = await db.execute(
            "SELECT COUNT(*) FROM ("
            "SELECT chat_id FROM played_scramble_sets UNION "
            "SELECT chat_id FROM scramble_scores UNION "
            "SELECT chat_id FROM tracked_groups"
            ") WHERE chat_id < 0"
        )
        row = await cur.fetchone()
        total_groups = row[0] if row else 0
        await queue_send(message.chat.id,
                         f"📈 The bot is currently active in <b>{total_groups}</b> groups.")
    except Exception as e:
        logger.error(f"cmd_groups error: {e}")


@dp.message(Command("ping", ignore_case=True))
async def cmd_ping(message: Message):
    try:
        now = time.time()
        if now - _CMD_COOLDOWN.get((message.chat.id, "ping"), 0) < 5:
            return
        _CMD_COOLDOWN[(message.chat.id, "ping")] = now
        await queue_send(message.chat.id, "Bot is running successfully. 🧩✨🤚")
    except Exception as e:
        logger.error(f"cmd_ping error: {e}")


@dp.message(Command("start", ignore_case=True))
async def cmd_start(message: Message):
    try:
        if not message.from_user:
            return
        now = time.time()
        if now - _CMD_COOLDOWN.get((message.chat.id, "start"), 0) < 30:
            return
        _CMD_COOLDOWN[(message.chat.id, "start")] = now
        track_user_ram(message.from_user.id)
        text = (
            "🎉 Welcome to Wordly Bot! 🧠✨\n\n"
            "An addictive word-guess game where you create words using the given letters 📚🔤\n\n"
            "🎮 /new — Start a game and challenge yourself\n"
            "📖 /help — View all available commands and how to play\n\n"
            "🚀 Sharpen your vocabulary, think fast, and climb the leaderboard! 🏆🔥"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_start error: {e}")


@dp.message(Command("help", ignore_case=True))
async def cmd_help(message: Message):
    try:
        now = time.time()
        chat_id = message.chat.id
        if now - _CMD_COOLDOWN.get((chat_id, "help"), 0) < 10:
            return
        _CMD_COOLDOWN[(chat_id, "help")] = now
        text = (
            "<blockquote>"
            "🔖 <b>How to Play</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "🔹 Send /new to start a round.\n"
            "🔹 Create valid English words using the letters provided.\n"
            "🔹 Words must be between 3 to 12 letters long.\n"
            "🔹 <b>Pro Tip:</b> Letter repetition is completely allowed!\n\n"
            "⚽ <b>Points System</b>\n"
            "━━━━━━━━━━━━━━━━━━\n"
            "<i>We use a Progressive Curve scoring system to keep gameplay fair and rewarding. "
            "The longer the word, the bigger the payout!</i>\n\n"
            "🔸 3 letters: 1 point\n"
            "🔸 4 letters: 2 points\n"
            "🔸 5 letters: 3 points\n"
            "🔸 6 letters: 5 points\n"
            "🔸 7 letters: 7 points\n"
            "🎯 8 to 12 letters: 10 points <b>(Max reward)</b>"
            "</blockquote>"
        )
        await queue_send(chat_id, text)
    except Exception as e:
        logger.error(f"cmd_help error: {e}")




@dp.message(Command("resetuser", ignore_case=True))
async def cmd_resetuser(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /resetuser <user_id>")
            return
        try:
            target_id = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid user ID.")
            return
        asyncio.create_task(_background_reset_user(target_id, message.chat.id))
        await queue_send(
            message.chat.id,
            f"⏳ Reset queued for <code>{target_id}</code> (background).",
        )
    except Exception as e:
        logger.error(f"cmd_resetuser error: {e}")


@dp.message(Command("ck", ignore_case=True))
async def cmd_ck(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /ck <user_id>")
            return
        try:
            target_id = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid user ID.")
            return
        score, rank, games_played, words_found, longest_word = await get_user_stats(target_id)
        db = await get_read_db()
        cur = await db.execute(
            "SELECT username FROM scramble_scores WHERE user_id = ? LIMIT 1", (target_id,))
        row = await cur.fetchone()
        username = row[0] if row else str(target_id)
        lw_display = longest_word.upper() if longest_word else "—"
        text = (
            f"🥇 <b>WORDLY STATS</b>\n\n"
            f"👤 Player: {html.escape(username)}\n"
            f"🆔 User ID: <code>{target_id}</code>\n"
            f"🏆 Global Rank: #{rank}\n"
            f"💎 Total Score: {score:,}\n\n"
            f"━━━━━━━━━━━━━━\n\n"
            f"🎮 Games Played: {games_played:,}\n"
            f"🔤 Words Found: {words_found:,}\n\n"
            f"━━━━━━━━━━━━━━\n\n"
            f"🏅 Longest Word\n"
            f"✨ {lw_display}"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_ck error: {e}")


@dp.message(Command("transfer", ignore_case=True))
async def cmd_transfer(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) != 4 or parts[2].lower() != "to":
            await queue_send(message.chat.id, "⚠️ Usage: /transfer <user_id_A> to <user_id_B>")
            return
        try:
            user_id_a = int(parts[1])
            user_id_b = int(parts[3])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Both user IDs must be valid numbers.")
            return
        if user_id_a == user_id_b:
            await queue_send(message.chat.id, "⚠️ User IDs must be different.")
            return
        asyncio.create_task(
            _background_transfer_user(user_id_a, user_id_b, message.chat.id))
        await queue_send(
            message.chat.id,
            f"⏳ Transfer queued: scores of <code>{user_id_a}</code> → <code>{user_id_b}</code> (background).",
        )
    except Exception as e:
        logger.error(f"cmd_transfer error: {e}")




@dp.message(Command("new", ignore_case=True))
async def cmd_new(message: Message):
    try:
        if not message.from_user:
            return
        if message.chat.type == "private":
            user_id = message.from_user.id
            now = time.time()
            if now - _DM_NEW_COOLDOWN.get(user_id, 0) < 10:
                return
            _DM_NEW_COOLDOWN[user_id] = now
            
            await queue_send(
                message.chat.id,
                '<tg-emoji emoji-id="6240210026477130678">🔥</tg-emoji> Add me in a group to start playing!',
                reply_markup=_DM_KB,
            )
            return

        track_user_ram(message.from_user.id)
        chat_id = message.chat.id
        if chat_id in games or chat_id in pending_games:
            await queue_send(
                chat_id,
                "A Word Scramble game is already running.\n"
                "Wait for it to finish or use /stop to end it.",
            )
            return

        if NOTIFICATION_GROUP:
            user_name = html.escape(message.from_user.first_name)
            chat_title = html.escape(message.chat.title or "Unknown Group")
            asyncio.create_task(queue_send(
                NOTIFICATION_GROUP,
                f"🟢 New game started\n"
                f"Started by: <a href='tg://user?id={message.from_user.id}'>{user_name}</a> [<code>{message.from_user.id}</code>]\n"
                f"Group: {chat_title} [<code>{chat_id}</code>]",
            ))

        await start_scramble_game(chat_id, message.from_user.id)
    except Exception as e:
        logger.error(f"cmd_new error: {e}")


@dp.callback_query(lambda c: c.data == "start_scramble")
async def handle_new_game_callback(callback: CallbackQuery):
    try:
        try:
            await callback.answer()
        except Exception:
            pass
        chat_id = callback.message.chat.id
        if chat_id in games or chat_id in pending_games:
            return
        await queue_edit_markup(chat_id, callback.message.message_id, None)

        if NOTIFICATION_GROUP:
            user_name = html.escape(callback.from_user.first_name)
            chat_title = html.escape(callback.message.chat.title or "Unknown Group")
            asyncio.create_task(queue_send(
                NOTIFICATION_GROUP,
                f"🟢 New game started\n"
                f"Started by: <a href='tg://user?id={callback.from_user.id}'>{user_name}</a> [<code>{callback.from_user.id}</code>]\n"
                f"Group: {chat_title} [<code>{chat_id}</code>]",
            ))

        await start_scramble_game(chat_id, callback.from_user.id)
    except Exception as e:
        logger.error(f"handle_new_game_callback error: {e}")


@dp.message(Command("hints", ignore_case=True))
async def cmd_hints(message: Message):
    try:
        chat_id = message.chat.id
        if chat_id not in games:
            return
        game = games[chat_id]
        now = time.time()
        if now - game.get("last_hint_time", 0) < 10:
            return
        game["last_hint_time"] = now
        await queue_send(chat_id, generate_scramble_text(game), protect_content=True)
    except Exception as e:
        logger.error(f"cmd_hints error: {e}")


@dp.message(Command("stop", ignore_case=True))
async def cmd_stop(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        if chat_id not in games:
            await queue_send(chat_id, "There is no active game to stop.")
            return
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can stop the game.")
            return
        game = games.get(chat_id)
        if not game or game.get("ending"):
            return
        game["ending"] = True
        await end_scramble_game(chat_id, reason="stopped")
    except Exception as e:
        logger.error(f"cmd_stop error: {e}")


@dp.message(Command("brch", ignore_case=True))
async def cmd_brch(message: Message):
    try:
        # Restricted to bot creators only
        if not _is_bot_creator(message):
            return
        if not message.reply_to_message:
            await queue_send(message.chat.id, "⚠️ Please reply to the message you want to forward broadcast.")
            return

        db = await get_read_db()
        cur = await db.execute(
            "SELECT chat_id FROM tracked_groups WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM played_scramble_sets WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM scramble_scores WHERE chat_id < 0"
        )
        chats = [row[0] for row in await cur.fetchall()]
        if not chats:
            return

        total = len(chats)
        await queue_send(message.chat.id, f"📢 Starting forwarded broadcast to {total} chats...")
        success = 0

        for target in chats:
            for attempt in range(3):
                try:
                    await rate_limited_call(bot.forward_message(
                        chat_id=int(target),
                        from_chat_id=message.chat.id,
                        message_id=message.reply_to_message.message_id,
                    ))
                    success += 1
                    break
                except TelegramRetryAfter as e:
                    # Pause for the required Telegram cooldown before continuing
                    await asyncio.sleep(e.retry_after + 0.5)
                except (TelegramForbiddenError, TelegramBadRequest):
                    # Inactive, kicked, or upgraded group — skip immediately
                    break
                except Exception:
                    break

        failed = total - success
        
        # Update global broadcast stats so /bcast still works accurately
        _LAST_BCAST["targeted"] = total
        _LAST_BCAST["success"] = success
        _LAST_BCAST["failed"] = failed
        _LAST_BCAST["at"] = time.time()

        await queue_send(
            message.chat.id,
            f"✅ Forwarded broadcast complete! Successfully sent to {success}/{total} chats.",
        )
    except Exception as e:
        logger.error(f"cmd_brch error: {e}")


@dp.message(Command("broadcast", ignore_case=True))
async def cmd_broadcast(message: Message):
    try:
        if not _is_admin_only(message):
            return
        if not message.reply_to_message:
            return

        db = await get_read_db()
        cur = await db.execute(
            "SELECT chat_id FROM tracked_groups WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM played_scramble_sets WHERE chat_id < 0 "
            "UNION SELECT chat_id FROM scramble_scores WHERE chat_id < 0"
        )
        chats = [row[0] for row in await cur.fetchall()]
        if not chats:
            return

        total = len(chats)
        await queue_send(message.chat.id, f"📢 Starting broadcast to {total} chats...")
        success = 0

        for target in chats:
            for attempt in range(3):
                try:
                    await rate_limited_call(bot.copy_message(
                        chat_id=int(target),
                        from_chat_id=message.chat.id,
                        message_id=message.reply_to_message.message_id,
                    ))
                    success += 1
                    break
                except TelegramRetryAfter as e:
                    # Pause for the required Telegram cooldown before continuing
                    await asyncio.sleep(e.retry_after + 0.5)
                except (TelegramForbiddenError, TelegramBadRequest):
                    # Inactive, kicked, or upgraded group — skip immediately
                    break
                except Exception:
                    break

        failed = total - success
        _LAST_BCAST["targeted"] = total
        _LAST_BCAST["success"] = success
        _LAST_BCAST["failed"] = failed
        _LAST_BCAST["at"] = time.time()

        await queue_send(
            message.chat.id,
            f"✅ Broadcast complete! Successfully sent to {success}/{total} chats.",
        )
    except Exception as e:
        logger.error(f"cmd_broadcast error: {e}")


@dp.message(Command("bcast", ignore_case=True))
async def cmd_bcast(message: Message):
    try:
        if not _is_admin_only(message):
            return
        if not _LAST_BCAST:
            await queue_send(message.chat.id, "ℹ️ No broadcast has been sent yet this session.")
            return
        import datetime
        ts = datetime.datetime.fromtimestamp(_LAST_BCAST["at"]).strftime("%Y-%m-%d %H:%M:%S")
        targeted = _LAST_BCAST["targeted"]
        success = _LAST_BCAST["success"]
        failed = _LAST_BCAST["failed"]
        pct = f"{(success / targeted * 100):.1f}" if targeted else "0.0"
        text = (
            f"📢 <b>Last Broadcast Stats</b>\n\n"
            f"🕐 Sent at: {ts}\n\n"
            f"🎯 Targeted: {targeted}\n"
            f"✅ Success: {success}\n"
            f"❌ Failed: {failed}\n"
            f"📊 Delivery rate: {pct}%"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_bcast error: {e}")


@dp.message(Command("delg", ignore_case=True))
async def cmd_delg(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /delg <group_id>")
            return
        try:
            gid = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid group ID.")
            return
        asyncio.create_task(_background_del_group(gid, message.chat.id))
        await queue_send(
            message.chat.id,
            f"⏳ Delete queued for group <code>{gid}</code> (background).",
        )
    except Exception as e:
        logger.error(f"cmd_delg error: {e}")


@dp.message(Command("ginfo", ignore_case=True))
async def cmd_ginfo(message: Message):
    try:
        if not _is_admin_only(message):
            return
        parts = message.text.split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /ginfo <group_id>")
            return
        try:
            gid = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid group ID.")
            return

        chat_title = "Unknown"
        member_count = "Unknown"
        chat_link = None
        try:
            chat = await rate_limited_call(bot.get_chat(gid))
            chat_title = chat.title or "Unknown"
            if chat.username:
                chat_link = f"https://t.me/{chat.username}"
            elif chat.invite_link:
                chat_link = chat.invite_link
            member_count = await rate_limited_call(bot.get_chat_member_count(gid))
        except Exception:
            pass

        db = await get_read_db()
        cur = await db.execute(
            "SELECT COALESCE(SUM(score), 0) FROM scramble_scores WHERE chat_id = ?", (gid,))
        row = await cur.fetchone()
        total_score = row[0] if row else 0

        cur = await db.execute(
            "SELECT COUNT(*) FROM played_scramble_sets WHERE chat_id = ?", (gid,))
        row = await cur.fetchone()
        games_count = row[0] if row else 0

        cur = await db.execute(
            "SELECT 1 FROM tracked_groups WHERE chat_id = ?", (gid,))
        tracked = await cur.fetchone() is not None

        is_banned = gid in _BANNED_GROUPS
        ban_str = "🚫 Banned" if is_banned else "✅ Active"

        link_line = chat_link if chat_link else "Private (no link available)"
        text = (
            f"📋 <b>Group Info</b>\n\n"
            f"🏷 Name: {html.escape(chat_title)}\n"
            f"🆔 ID: <code>{gid}</code>\n"
            f"🔗 Link: {html.escape(link_line)}\n"
            f"👥 Members: {member_count}\n"
            f"🔍 Tracked: {'Yes' if tracked else 'No'}\n"
            f"🛡 Status: {ban_str}\n\n"
            f"━━━━━━━━━━━━━━\n\n"
            f"💎 All-time Score: {total_score:,}\n"
            f"🎮 Games Played: {games_count:,}"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_ginfo error: {e}")


def _get_level_badge(score: int) -> str:
    if score >= 500000:
        return "Legend"
    elif score >= 250000:
        return "Mastermind"
    elif score >= 100000:
        return "Prodigy"
    elif score >= 40000:
        return "Wordsmith"
    elif score >= 10000:
        return "Thinker"
    else:
        return "Beginner"


async def get_ftb_leaderboard_data(scope: str, period: str, chat_id: int):
    try:
        db = await get_read_db()
        if period == "alltime":
            if scope in ("ftb_global", "ftb"):
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score) as total "
                    "FROM ftb_scores GROUP BY user_id "
                    "ORDER BY total DESC LIMIT 10"
                )
            else: # "ftb_group"
                cur = await db.execute(
                    "SELECT username, score as total FROM ftb_scores "
                    "WHERE chat_id = ? ORDER BY total DESC LIMIT 10",
                    (chat_id,)
                )
        else:
            since = _period_since(period)
            if scope in ("ftb_global", "ftb"):
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score_delta) as total "
                    "FROM ftb_history WHERE recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (since,),
                )
            else: # "ftb_group"
                cur = await db.execute(
                    "SELECT MAX(username) as username, SUM(score_delta) as total "
                    "FROM ftb_history WHERE chat_id = ? AND recorded_at >= ? "
                    "GROUP BY user_id ORDER BY total DESC LIMIT 10",
                    (chat_id, since),
                )
        rows = await cur.fetchall()
        return [(row[0], row[1]) for row in rows]
    except Exception:
        return []

async def _build_lb_text(scope: str, period: str, chat_id: int, chat_title: str = "") -> str:
    if scope == "longest":
        rows = await get_longest_words()
        title = "🔤 𝗪𝗼𝗿𝗱𝗹𝘆 • Longest Words"
        if not rows:
            body = "No words recorded yet."
        else:
            body = "\n".join(
                f"{i}. {html.escape(str(word).capitalize())} ({len(str(word))} letters) — {html.escape(str(username))}"
                for i, (username, word) in enumerate(rows, 1)
            )
        return f"<blockquote>{title}</blockquote>\n<blockquote>{body}</blockquote>"
        
    if scope in ("fill", "fill_global", "fill_group"):
        rows = await get_fill_leaderboard_data(scope, period, chat_id)
        period_label = {
            "today": "Today", "weekly": "This Week",
            "monthly": "This Month", "yearly": "This Year", "alltime": "All Time",
        }[period]
        
        scope_label = "Global" if scope in ("fill", "fill_global") else (html.escape(chat_title) if chat_title else "This Group")
        title = f"🏆 𝗪𝗼𝗿𝗱𝗹𝘆 • Fill the Blanks • {scope_label}\n📅 {period_label}"
        
        if not rows:
            body = "No fill-the-blanks scores recorded yet."
        else:
            body = "\n".join(
                f"{i}. {html.escape(str(username))} — {total:,} coins"
                for i, (username, total) in enumerate(rows, 1)
            )
        return f"<blockquote>{title}</blockquote>\n<blockquote>{body}</blockquote>"

    if scope in ("ftb", "ftb_global", "ftb_group"):
        rows = await get_ftb_leaderboard_data(scope, period, chat_id)
        period_label = {
            "today": "Today", "weekly": "This Week",
            "monthly": "This Month", "yearly": "This Year", "alltime": "All Time",
        }[period]
        
        scope_label = "Global" if scope in ("ftb", "ftb_global") else (html.escape(chat_title) if chat_title else "This Group")
        title = f"🏆 𝗪𝗼𝗿𝗱𝗹𝘆 • Blanks Mode • {scope_label}\n📅 {period_label}"
        
        if not rows:
            body = "No Blanks Mode scores recorded yet."
        else:
            body = "\n".join(
                f"{i}. {html.escape(str(username))} — {total:,} pts"
                for i, (username, total) in enumerate(rows, 1)
            )
        return f"<blockquote>{title}</blockquote>\n<blockquote>{body}</blockquote>"
        
    rows = await get_leaderboard_data(scope, period, chat_id)
    scope_label = "Global" if scope == "global" else (html.escape(chat_title) if chat_title else "This Group")
    period_label = {
        "today": "Today", "weekly": "This Week",
        "monthly": "This Month", "yearly": "This Year", "alltime": "All Time",
    }[period]
    title = f"🏆 𝗪𝗼𝗿𝗱𝗹𝘆 • {scope_label} • {period_label}"
    if not rows:
        body = "No scores recorded yet."
    else:
        body = "\n".join(
            f"{i}. {html.escape(str(username))} — {total:,} pts"
            for i, (username, total) in enumerate(rows, 1)
        )
    return f"<blockquote>{title}</blockquote>\n<blockquote>{body}</blockquote>"

@functools.lru_cache(maxsize=16)
def _lb_keyboard(scope: str, period: str) -> InlineKeyboardMarkup:
    is_fill = scope in ("fill", "fill_global", "fill_group")
    is_ftb = scope in ("ftb_global", "ftb_group", "ftb")
    
    target_global = "fill_global" if is_fill else ("ftb_global" if is_ftb else "global")
    target_group = "fill_group" if is_fill else ("ftb_group" if is_ftb else "group")
    
    def s_btn(label: str, target_s: str, match_s: tuple, eid: str) -> InlineKeyboardButton:
        if scope in match_s:
            return InlineKeyboardButton(text=label, callback_data=f"lb:{target_s}:{period}", style="success", icon_custom_emoji_id=eid)
        return InlineKeyboardButton(text=label, callback_data=f"lb:{target_s}:{period}", icon_custom_emoji_id=eid)

    def p_btn(label: str, p: str, eid: str) -> InlineKeyboardButton:
        if period == p:
            return InlineKeyboardButton(text=label, callback_data=f"lb:{scope}:{p}", style="primary", icon_custom_emoji_id=eid)
        return InlineKeyboardButton(text=label, callback_data=f"lb:{scope}:{p}", icon_custom_emoji_id=eid)
        
    fill_btn_target = "fill_global"
    fill_btn_style = "success" if is_fill else "primary"

    ws_btn_target = "global" if scope in ("group", "fill_group", "ftb_group") else "global"
    ws_btn_style = "success" if not is_fill and not is_ftb and scope != "longest" else "secondary"

    ftb_btn_target = "ftb_global"
    ftb_btn_style = "success" if is_ftb else "secondary"

    return InlineKeyboardMarkup(inline_keyboard=[
        [s_btn("𝗚𝗹𝗼𝗯𝗮𝗹", target_global, ("global", "fill_global", "fill", "ftb_global", "ftb"), "5204271353565300127"), 
         s_btn("𝗧𝗵𝗶𝘀 𝗚𝗿𝗼𝘂𝗽", target_group, ("group", "fill_group", "ftb_group"), "5258513401784573443")],
        [p_btn("𝗧𝗼𝗱𝗮𝘆", "today", "5249442259056744272"), p_btn("𝗪𝗲𝗲𝗸𝗹𝘆", "weekly", "5256020181859196776")],
        [p_btn("𝗠𝗼𝗻𝘁𝗵𝗹𝘆", "monthly", "5256118867322756306"), p_btn("𝗬𝗲𝗮𝗿𝗹𝘆", "yearly", "5782831906789791547")],
        [p_btn("𝗔𝗹𝗹 𝗧𝗶𝗺𝗲", "alltime", "5265209659525980056")],
        [InlineKeyboardButton(text="𝗟𝗼𝗻𝗴𝗲𝘀𝘁 𝗪𝗼𝗿𝗱𝘀", callback_data="lb:longest:alltime", icon_custom_emoji_id="5258500400918587241")],
        [InlineKeyboardButton(text="𝗙𝗶𝗹𝗹 𝘁𝗵𝗲 𝗯𝗹𝗮𝗻𝗸𝘀", callback_data=f"lb:{fill_btn_target}:{period}", style=fill_btn_style, icon_custom_emoji_id="5373098009640836781")],
        [InlineKeyboardButton(text="𝙒𝙊𝙍𝘿 𝙎𝘾𝙍𝘼𝙈𝘽𝙇𝙀", callback_data=f"lb:{ws_btn_target}:{period}", style=ws_btn_style, icon_custom_emoji_id="5258334872878980409"),
         InlineKeyboardButton(text="𝗕𝗹𝗮𝗻𝗸𝘀 𝗠𝗼𝗱𝗲", callback_data=f"lb:{ftb_btn_target}:{period}", style=ftb_btn_style, icon_custom_emoji_id="5258334872878980409")]
    ])

@dp.callback_query(lambda c: c.data and c.data.startswith("lb:"))
async def handle_lb_callback(callback: CallbackQuery):
    try:
        if not callback.message:
            try:
                await callback.answer()
            except Exception:
                pass
            return
        parts = (callback.data or "").split(":")
        if len(parts) != 3:
            try:
                await callback.answer()
            except Exception:
                pass
            return
        _, scope, period = parts
        
        # CHANGED: Include FTB scopes in validation
        if scope not in ("global", "group", "longest", "fill", "fill_global", "fill_group", "ftb", "ftb_global", "ftb_group") or period not in ("today", "weekly", "monthly", "yearly", "alltime"):
            try:
                await callback.answer()
            except Exception:
                pass
            return
            
        if scope in ("group", "fill_group", "ftb_group") and callback.message.chat.type == "private":
            try:
                await callback.answer("Group leaderboard is only available in groups.", show_alert=True)
            except Exception:
                pass
            return
            
        chat_id = callback.message.chat.id
        msg_id = callback.message.message_id
        user_id = callback.from_user.id
        now = time.time()
        user_key = (user_id, chat_id, msg_id)
        if now - _LB_USER_CD.get(user_key, 0) < 2.0:
            try:
                await callback.answer()
            except Exception:
                pass
            return
        _LB_USER_CD[user_key] = now
        try:
            await callback.answer()
        except Exception:
            pass
        edit_key = (chat_id, msg_id)
        if edit_key in _LB_EDITING:
            return
        _LB_EDITING.add(edit_key)
        try:
            chat_title = (callback.message.chat.title or "") if scope in ("group", "fill_group", "ftb_group") else ""
            text = await _build_lb_text(scope, period, chat_id, chat_title)
            kb = _lb_keyboard(scope, period)
            await rate_limited_call(
                bot.edit_message_text(
                    chat_id=chat_id,
                    message_id=msg_id,
                    text=text,
                    reply_markup=kb,
                )
            )
        except TelegramBadRequest as e:
            if "message is not modified" not in str(e).lower():
                logger.debug(f"handle_lb_callback edit drop chat={chat_id}: {e}")
        except Exception as e:
            logger.error(f"handle_lb_callback error chat={chat_id}: {e}")
        finally:
            _LB_EDITING.discard(edit_key)
    except Exception as e:
        logger.error(f"handle_lb_callback outer error: {e}")

@dp.message(Command("stats", ignore_case=True))
async def cmd_stats(message: Message):
    try:
        if not message.from_user:
            return
        now = time.time()
        if now - _STATS_COOLDOWN.get(message.chat.id, 0) < 5:
            return
        _STATS_COOLDOWN[message.chat.id] = now
        track_user_ram(message.from_user.id)
        
        user_id = message.from_user.id
        
        # Fetch Scramble Stats
        score, rank, games_played, words_found, longest_word = await get_user_stats(user_id)
        
        db = await get_read_db()
        
        # Fetch Hourly Puzzle Stats
        cur = await db.execute(
            "SELECT SUM(coins), SUM(puzzles_solved) "
            "FROM fill_blank_scores WHERE user_id = ?", (user_id,)
        )
        p_row = await cur.fetchone()
        puzzle_score = p_row[0] if p_row and p_row[0] is not None else 0
        puzzle_words = p_row[1] if p_row and p_row[1] is not None else 0
        
        # Fetch FTB Mode Stats
        cur = await db.execute(
            "SELECT SUM(score), SUM(games_played), SUM(words_found) "
            "FROM ftb_scores WHERE user_id = ?", (user_id,)
        )
        f_row = await cur.fetchone()
        ftb_score = f_row[0] if f_row and f_row[0] is not None else 0
        ftb_games = f_row[1] if f_row and f_row[1] is not None else 0
        ftb_words = f_row[2] if f_row and f_row[2] is not None else 0

        player_name = html.escape(message.from_user.first_name)
        lw_display = longest_word.upper() if longest_word else "—"
        level = _get_level_badge(score)
        
        text = (
            f'<tg-emoji emoji-id="5440539497383087970">🥇</tg-emoji> <b>WORDLY STATS</b>\n\n'
            f'<tg-emoji emoji-id="5316887736823591263">👤</tg-emoji> Player: {player_name}\n'
            f'<tg-emoji emoji-id="5280769763398671636">🏆</tg-emoji> Global Rank: #{rank}\n'
            f'<tg-emoji emoji-id="5409079854077330762">🥰</tg-emoji> Level: {level}\n\n'
            f"━━━━━━━━━━━━━━\n\n"
            f"Word Scramble:\n\n"
            f'<tg-emoji emoji-id="5359719332542718652">💎</tg-emoji> Total Score: {score:,}\n'
            f'<tg-emoji emoji-id="5463023453609150398">🤍</tg-emoji> Words Found: {words_found:,}\n'
            f'<tg-emoji emoji-id="5309950797704865693">🎮</tg-emoji> Games Played: {games_played:,}\n\n'
            f"Fill The Blanks mode:\n\n"
            f'<tg-emoji emoji-id="5359719332542718652">💎</tg-emoji> Total Score: {ftb_score:,}\n'
            f'<tg-emoji emoji-id="5463023453609150398">🤍</tg-emoji> Words Found: {ftb_words:,}\n'
            f'<tg-emoji emoji-id="5309950797704865693">🎮</tg-emoji> Games Played: {ftb_games:,}\n\n'
            f"Puzzles:\n\n"
            f'<tg-emoji emoji-id="5359719332542718652">💎</tg-emoji> Total Score: {puzzle_score:,}\n'
            f'<tg-emoji emoji-id="5463023453609150398">🤍</tg-emoji> Words Found: {puzzle_words:,}\n\n'
            f"━━━━━━━━━━━━━━\n\n"
            f'<tg-emoji emoji-id="5260413856093598223">❤️</tg-emoji> Longest Word\n'
            f'<tg-emoji emoji-id="6280703708288262104">⌨</tg-emoji> {lw_display}'
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_stats error: {e}")



@dp.message(Command("leaderboard", ignore_case=True))
async def cmd_leaderboard(message: Message):
    try:
        if not message.from_user:
            return
        now = time.time()
        if now - _LB_COOLDOWN.get(message.chat.id, 0) < 5:
            return
        _LB_COOLDOWN[message.chat.id] = now
        track_user_ram(message.from_user.id)
        text = await _build_lb_text("global", "alltime", message.chat.id)
        kb = _lb_keyboard("global", "alltime")
        await queue_send(message.chat.id, text, reply_markup=kb)
    except Exception as e:
        logger.error(f"cmd_leaderboard error: {e}")




@dp.message(Command("topchats", ignore_case=True))
async def cmd_topchats(message: Message):
    try:
        if not message.from_user:
            return
        now = time.time()
        if now - _TOPCHATS_COOLDOWN.get(message.chat.id, 0) < 10:
            return
        _TOPCHATS_COOLDOWN[message.chat.id] = now
        track_user_ram(message.from_user.id)
        top = await get_top_chats()
        if not top:
            await queue_send(message.chat.id, "No chat scores recorded yet!")
            return
        infos = await asyncio.gather(
            *[_get_chat_info_cached(cid) for cid, _ in top]
        )
        text = "🏆 <b>Wordly Top 10 Chats</b>\n\n"
        for i, ((cid, total), (title, url)) in enumerate(zip(top, infos), 1):
            name = html.escape(title) if title else f"Chat {cid}"
            if url:
                text += f"{i}) <a href=\"{html.escape(url)}\">{name}</a> — {total} pts\n"
            else:
                text += f"{i}) {name} — {total} pts\n"
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_topchats error: {e}")


# ---------------------------------------------------------------------------
# The hot path: word check
# ---------------------------------------------------------------------------
@dp.message(Command("emojion", ignore_case=True))
async def cmd_emojion(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        now = time.time()
        if now - _CMD_COOLDOWN.get((chat_id, "emojion"), 0) < 5:
            return
        _CMD_COOLDOWN[(chat_id, "emojion")] = now
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can use this command.")
            return
        _EMOJI_MODE[chat_id] = True
        emoji = _CHAT_EMOJI.get(chat_id, "👀")
        await queue_send(chat_id, f"✅ Emoji mode ON — already-found words will get a {emoji} reaction.")
    except Exception as e:
        logger.error(f"cmd_emojion error: {e}")


@dp.message(Command("emojioff", ignore_case=True))
async def cmd_emojioff(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        now = time.time()
        if now - _CMD_COOLDOWN.get((chat_id, "emojioff"), 0) < 5:
            return
        _CMD_COOLDOWN[(chat_id, "emojioff")] = now
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can use this command.")
            return
        _EMOJI_MODE[chat_id] = False
        await queue_send(chat_id, "✅ Emoji mode OFF — already-found words will show a text message.")
    except Exception as e:
        logger.error(f"cmd_emojioff error: {e}")


@dp.message(Command("changeemoji", ignore_case=True))
async def cmd_changeemoji(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        now = time.time()
        if now - _CMD_COOLDOWN.get((chat_id, "changeemoji"), 0) < 5:
            return
        _CMD_COOLDOWN[(chat_id, "changeemoji")] = now
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can use this command.")
            return
        parts = (message.text or "").split(None, 1)
        if len(parts) < 2 or not parts[1].strip():
            current = _CHAT_EMOJI.get(chat_id, "👀")
            await queue_send(chat_id, f"⚠️ Usage: /changeemoji <emoji>\nCurrent emoji: {current}")
            return
        new_emoji = parts[1].strip()
        _CHAT_EMOJI[chat_id] = new_emoji
        await queue_send(
            chat_id,
            f"✅ Emoji changed to {new_emoji} — will be used for already-found words in this group.",
        )
    except Exception as e:
        logger.error(f"cmd_changeemoji error: {e}")


@dp.message(Command("turnoff", ignore_case=True))
async def cmd_turnoff(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        now = time.time()
        if now - _CMD_COOLDOWN.get((chat_id, "turnoff"), 0) < 5:
            return
        _CMD_COOLDOWN[(chat_id, "turnoff")] = now
        
        # Security: Only group admins can use this
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can use this command.")
            return
            
        _PUZZLES_OFF.add(chat_id)
        await queue_send(
            chat_id, 
            "❌ Puzzles are turned off for this chat.\n\nTo turn on again, use /turnon"
        )
    except Exception as e:
        logger.error(f"cmd_turnoff error: {e}")


@dp.message(Command("turnon", ignore_case=True))
async def cmd_turnon(message: Message):
    try:
        if not message.from_user:
            return
        chat_id = message.chat.id
        now = time.time()
        if now - _CMD_COOLDOWN.get((chat_id, "turnon"), 0) < 5:
            return
        _CMD_COOLDOWN[(chat_id, "turnon")] = now
        
        # Security: Only group admins can use this
        if not await is_user_admin(chat_id, message.from_user.id):
            await queue_send(chat_id, "⚠️ Only group admins can use this command.")
            return
            
        _PUZZLES_OFF.discard(chat_id)
        await queue_send(
            chat_id, 
            "Bot will send Puzzles for this chat now. ✅"
        )
    except Exception as e:
        logger.error(f"cmd_turnon error: {e}")


# ---------------------------------------------------------------------------
# Bot-creator commands: /today, /adminp, /rmp
# ---------------------------------------------------------------------------
@dp.message(Command("today", ignore_case=True))
async def cmd_today(message: Message):
    try:
        if not _is_bot_creator(message):
            return
        today_start = int(time.time()) - (int(time.time()) % 86400)
        db = await get_read_db()
        cur = await db.execute(
            "SELECT COUNT(*) FROM game_log WHERE played_at >= ?", (today_start,))
        row = await cur.fetchone()
        total_today = row[0] if row else 0
        cur = await db.execute(
            "SELECT chat_id, COUNT(*) as cnt FROM game_log "
            "WHERE played_at >= ? GROUP BY chat_id ORDER BY cnt DESC LIMIT 1",
            (today_start,),
        )
        top_row = await cur.fetchone()
        if top_row:
            top_group_id = top_row[0]
            top_group_count = top_row[1]
        else:
            top_group_id = "—"
            top_group_count = 0
        text = (
            f"📊 <b>Today's Game Statistics</b>\n\n"
            f"🎮 <b>Total Games Played Today</b>\n"
            f"➤ 🔢 {total_today}\n\n"
            f"🏆 <b>Most Active Group Today</b>\n"
            f"➤ 🆔 Group ID: <code>{top_group_id}</code> ({top_group_count} games)"
        )
        await queue_send(message.chat.id, text)
    except Exception as e:
        logger.error(f"cmd_today error: {e}")





@dp.message(Command("resetpuz", ignore_case=True))
async def cmd_resetpuz(message: Message):
    try:
        # Security: Only Bot Creators can use this
        if not _is_bot_creator(message):
            return
            
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM fill_blank_scores")
            await db.execute("DELETE FROM fill_blank_history")
            await db.commit()
            
        # Clear any unsaved puzzle scores from RAM to prevent them from saving after reset
        _PENDING_FILL_SCORES.clear()
        
        await queue_send(
            message.chat.id,
            "✅ All puzzle scores and history have been successfully reset to 0."
        )
    except Exception as e:
        logger.error(f"cmd_resetpuz error: {e}")


@dp.message(Command("adminp", ignore_case=True))
async def cmd_adminp(message: Message):
    try:
        if not _is_bot_creator(message):
            return
        parts = (message.text or "").split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /adminp <telegram_id>")
            return
        try:
            target_id = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid Telegram ID.")
            return
            
        _PROMOTED_ADMINS.add(target_id)
        
        # Save to database
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("INSERT OR IGNORE INTO promoted_admins (user_id) VALUES (?)", (target_id,))
            await db.commit()
            
        await queue_send(
            message.chat.id,
            f"✅ <code>{target_id}</code> has been added to the bot creator list permanently.",
        )
    except Exception as e:
        logger.error(f"cmd_adminp error: {e}")

@dp.message(Command("rmp", ignore_case=True))
async def cmd_rmp(message: Message):
    try:
        if not _is_bot_creator(message):
            return
        parts = (message.text or "").split()
        if len(parts) < 2:
            await queue_send(message.chat.id, "⚠️ Usage: /rmp <telegram_id>")
            return
        try:
            target_id = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid Telegram ID.")
            return
            
        _PROMOTED_ADMINS.discard(target_id)
        
        # Remove from database
        async with _DB_WRITE_LOCK:
            db = await get_db()
            await db.execute("DELETE FROM promoted_admins WHERE user_id = ?", (target_id,))
            await db.commit()
            
        await queue_send(
            message.chat.id,
            f"✅ <code>{target_id}</code> has been removed from the bot creator list.",
        )
    except Exception as e:
        logger.error(f"cmd_rmp error: {e}")



@dp.message(Command("puz", ignore_case=True))
async def cmd_puz(message: Message):
    try:
        # Security: Only Bot Creators can use this
        if not _is_bot_creator(message):
            return
            
        chat_id = message.chat.id
        if chat_id in games or chat_id in pending_games or chat_id in fill_puzzles:
            await queue_send(chat_id, "⚠️ A game or puzzle is already active here.")
            return

        puzzle = _create_fill_puzzle()
        if puzzle is None:
            return

        # Modify the puzzle for 'fun' mode: 5 min expiry and a special flag
        puzzle["is_fun"] = True
        puzzle["expires_at"] = time.monotonic() + 300.0  # 300 seconds = 5 minutes

        text = _fill_puzzle_text(puzzle) + "\n\n<i>(Practice Puzzle — No Coins)</i>"
        sent_msg = await queue_send_and_wait(chat_id, text)
        
        if sent_msg:
            puzzle["message_id"] = sent_msg.message_id
            fill_puzzles[chat_id] = puzzle
            
    except Exception as e:
        logger.error(f"cmd_puz error: {e}")


@dp.message(Command("hi", ignore_case=True))
async def cmd_hi(message: Message):
    try:
        # Security: Only Bot Creators can use this
        if not _is_bot_creator(message):
            return
        
        parts = (message.text or "").split(maxsplit=2)
        if len(parts) < 3:
            await queue_send(message.chat.id, "⚠️ Usage: /hi <chat_id> <message>")
            return
            
        try:
            target_chat_id = int(parts[1])
        except ValueError:
            await queue_send(message.chat.id, "⚠️ Invalid chat ID.")
            return
            
        text_to_send = parts[2]
        
        # Send message directly using the rate limiter
        try:
            await rate_limited_call(bot.send_message(target_chat_id, text_to_send))
            await queue_send(message.chat.id, f"✅ Message sent to <code>{target_chat_id}</code>")
        except Exception as e:
            await queue_send(message.chat.id, f"❌ Failed to send message: {e}")
            
    except Exception as e:
        logger.error(f"cmd_hi error: {e}")


def _create_ftb_round() -> dict | None:
    if not PUZZLE_WORDS:
        return None
    
    word = random.choice(PUZZLE_WORDS)
    word_len = len(word)
    
    if 4 <= word_len <= 7:
        reveal_count = 2
    elif 8 <= word_len <= 10:
        reveal_count = 3
    else:
        reveal_count = 2 

    revealed = set(random.sample(range(word_len), reveal_count))
    scrambled = list(word)
    random.shuffle(scrambled)
    
    attempts = 0
    while "".join(scrambled) == word and attempts < 10:
        random.shuffle(scrambled)
        attempts += 1
        
    letters = " ".join(scrambled)
    pattern = " ".join(char if index in revealed else "_" for index, char in enumerate(word))

    return {
        "word": word,
        "letters": letters,
        "pattern": pattern
    }

async def start_ftb_game(chat_id: int, starter_id: int):
    if chat_id in games or chat_id in pending_games:
        return

    puzzle = fill_puzzles.get(chat_id)
    if puzzle:
        puzzle["expires_at"] = 0

    now = time.time()
    if now - _NEWGAME_COOLDOWN.get(chat_id, 0) < NEWGAME_COOLDOWN_SECS:
        return
    _NEWGAME_COOLDOWN[chat_id] = now

    pending_games.add(chat_id)
    try:
        if chat_id in games:
            return

        rnd = _create_ftb_round()
        if not rnd:
            await queue_send(chat_id, "❌ Not enough words in fill.txt to start FTB mode.")
            return

        game = {
            "game_type": "ftb",
            "current_round": rnd,
            "word_start_time": time.monotonic(),
            "found_count": 0,
            "total_words": 20,
            "user_scores": {},
            "pending_db_scores": {},
            "lock": asyncio.Lock(),
            "starter_id": starter_id,
            "last_activity": time.monotonic(),
            "ending": False,
        }
        games[chat_id] = game

        text = (
            f"Word Scramble◾️\n\n"
            f"Find the hidden word! \n\n"
            f"📚 Letters: {rnd['letters']}\n"
            f"🎲 {rnd['pattern']}\n\n"
            f"Total words found: 0/20"
        )
        await queue_send_and_wait(chat_id, text, protect_content=True)
    except Exception as e:
        logger.error(f"start_ftb_game error chat={chat_id}: {e}")
        games.pop(chat_id, None)
        await queue_send(chat_id, "❌ Couldn't start the game.")
    finally:
        pending_games.discard(chat_id)

async def end_ftb_game(chat_id: int, reason: str = "win"):
    global _PENDING_GAMES_COUNT
    try:
        game = games.pop(chat_id, None)
        if not game:
            return
        game["ending"] = True
        asyncio.create_task(_log_game(chat_id))
        _PENDING_GAMES_COUNT += 1

        pending_scores = game.get("pending_db_scores", {})
        for uid in pending_scores:
            pending_scores[uid]["games_played"] = 1
        flush_at = time.time() + 900
        _DEFERRED_FTB_QUEUE.append((flush_at, pending_scores, chat_id))

        if len(_DEFERRED_FTB_QUEUE) > MAX_DEFERRED_QUEUE:
            overflow = _DEFERRED_FTB_QUEUE[:1000]
            del _DEFERRED_FTB_QUEUE[:1000]
            asyncio.create_task(_flush_ftb_pending([(ps, c) for _, ps, c in overflow]))

        if reason == "stopped":
            end_text = (
                f"<blockquote>{P_OVER} Game over {P_OVER}\n"
                f"Nobody guessed the word in last 5 minutes ⏰</blockquote>\n\n"
            )
        else:
            end_text = f"<blockquote>{P_OVER} Game over {P_OVER}</blockquote>\n\n"

        round_scores = game.get("user_scores", {})
        if not round_scores:
            end_text += f"<blockquote>{P_SCORES} Scores\n\nNo words found.</blockquote>\n\n"
        else:
            scores_text = f"{P_SCORES} Scores\n\n"
            sorted_users = sorted(round_scores.items(), key=lambda kv: kv[1]["score"], reverse=True)
            for i, (uid, entry) in enumerate(sorted_users, start=1):
                scores_text += f"{i}. {html.escape(entry['name'])} - {entry['score']} points {P_DIAMOND}\n"
            end_text += f"<blockquote>{scores_text.strip()}</blockquote>\n\n"

        end_text += "<blockquote>/new2 - Start new Fill the blanks game</blockquote>"

        await queue_send(chat_id, end_text, reply_markup=InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(
                text="New FTB Game",
                callback_data="start_ftb",
                icon_custom_emoji_id=P1_ID,
                style="primary",
            )
        ]]))
    except Exception as e:
        logger.error(f"end_ftb_game error chat={chat_id}: {e}")

@dp.message(Command("new2", ignore_case=True))
async def cmd_new2(message: Message):
    try:
        if not message.from_user:
            return
        if message.chat.type == "private":
            user_id = message.from_user.id
            now = time.time()
            if now - _DM_NEW_COOLDOWN.get(user_id, 0) < 10:
                return
            _DM_NEW_COOLDOWN[user_id] = now
            
            await queue_send(
                message.chat.id,
                '<tg-emoji emoji-id="6240210026477130678">🔥</tg-emoji> Add me in a group to start playing!',
                reply_markup=_DM_KB,
            )
            return

        track_user_ram(message.from_user.id)
        chat_id = message.chat.id
        if chat_id in games or chat_id in pending_games:
            await queue_send(
                chat_id,
                "A game is already running.\n"
                "Wait for it to finish or use /stop to end it.",
            )
            return

        if NOTIFICATION_GROUP:
            user_name = html.escape(message.from_user.first_name)
            chat_title = html.escape(message.chat.title or "Unknown Group")
            asyncio.create_task(queue_send(
                NOTIFICATION_GROUP,
                f"🟢 New FTB game started\n"
                f"Started by: <a href='tg://user?id={message.from_user.id}'>{user_name}</a> [<code>{message.from_user.id}</code>]\n"
                f"Group: {chat_title} [<code>{chat_id}</code>]",
            ))

        await start_ftb_game(chat_id, message.from_user.id)
    except Exception as e:
        logger.error(f"cmd_new2 error: {e}")

@dp.callback_query(lambda c: c.data == "start_ftb")
async def handle_new_ftb_callback(callback: CallbackQuery):
    try:
        try:
            await callback.answer()
        except Exception:
            pass
        chat_id = callback.message.chat.id
        if chat_id in games or chat_id in pending_games:
            return
        await queue_edit_markup(chat_id, callback.message.message_id, None)

        if NOTIFICATION_GROUP:
            user_name = html.escape(callback.from_user.first_name)
            chat_title = html.escape(callback.message.chat.title or "Unknown Group")
            asyncio.create_task(queue_send(
                NOTIFICATION_GROUP,
                f"🟢 New FTB game started\n"
                f"Started by: <a href='tg://user?id={callback.from_user.id}'>{user_name}</a> [<code>{callback.from_user.id}</code>]\n"
                f"Group: {chat_title} [<code>{chat_id}</code>]",
            ))

        await start_ftb_game(chat_id, callback.from_user.id)
    except Exception as e:
        logger.error(f"handle_new_ftb_callback error: {e}")

@dp.message(F.text)
async def check_word(message: Message):
    chat_id = message.chat.id
    try:
        if not message.from_user:
            return
        attempt = message.text.strip().upper()

        # Handle Hourly Challenge Puzzles 
        puzzle = _claim_fill_puzzle(chat_id, attempt)
        if puzzle:
            first_name = message.from_user.first_name or "Player"
            user_id = message.from_user.id
            P_TROPHY_NEW = '<tg-emoji emoji-id="5280769763398671636">🏆</tg-emoji>'
            P_CLOCK = '<tg-emoji emoji-id="5413704112220949842">⏰</tg-emoji>'
            P_COIN = '<tg-emoji emoji-id="5199552030615558774">🪙</tg-emoji>'

            mention_name = f'<b><a href="tg://user?id={user_id}">{html.escape(first_name)}</a></b>'

            if puzzle.get("is_fun"):
                await queue_send(
                    chat_id,
                    f"{P_TROPHY_NEW} {mention_name} found the word!\n\n"
                    f"➜ <b>{html.escape(puzzle['word'].capitalize())}</b>\n\n"
                    f"<i>(Practice mode — no coins awarded)</i>"
                )
                return

            solve_time = int(time.monotonic() - puzzle["created_at"])
            
            if solve_time <= 10:
                reward = 100
            elif solve_time <= 30:
                reward = 80
            elif solve_time <= 60:
                reward = 50
            else:
                reward = 30

            if solve_time < 60:
                time_str = f"{solve_time}s"
            else:
                minutes = solve_time // 60
                seconds = solve_time % 60
                time_str = f"{minutes}m" if seconds == 0 else f"{minutes}m {seconds}s"

            track_user_ram(user_id)
            _queue_fill_score(user_id, chat_id, first_name, reward)
            
            text = (
                f"{P_TROPHY_NEW} {mention_name} found the word!\n\n"
                f"➜ <b>{html.escape(puzzle['word'].capitalize())}</b>\n\n"
                f"<blockquote>{P_CLOCK} Time: {time_str}\n"
                f"{P_COIN} {reward} coins added</blockquote>"
            )
            await queue_send(chat_id, text)
            return

        # Game Modes (Scramble / FTB)
        if chat_id not in games:
            return
        game = games[chat_id]
        if game.get("ending"):
            return

        # --- Fill The Blanks Mode Logic ---
        if game.get("game_type") == "ftb":
            if attempt != game["current_round"]["word"]:
                return

            lock = game["lock"]
            try:
                await asyncio.wait_for(lock.acquire(), timeout=2.0)
            except asyncio.TimeoutError:
                return
            try:
                if chat_id not in games or game.get("ending") or attempt != game["current_round"]["word"]:
                    return

                first_name = message.from_user.first_name
                user_id = message.from_user.id
                solve_time = time.monotonic() - game["word_start_time"]

                if solve_time <= 5.0:
                    points = 50
                elif solve_time <= 15.0:
                    points = 35
                elif solve_time <= 30.0:
                    points = 20
                elif solve_time <= 40.0:
                    points = 10
                else:
                    points = 0

                if solve_time < 60:
                    time_str = f"{int(solve_time)}s"
                else:
                    time_str = f"{int(solve_time)//60}m {int(solve_time)%60}s"

                scores = game["user_scores"]
                bucket = scores.get(user_id)
                if bucket is None:
                    scores[user_id] = {"name": first_name, "score": points}
                else:
                    bucket["score"] += points
                    bucket["name"] = first_name

                pending = game["pending_db_scores"]
                pbucket = pending.get(user_id)
                if pbucket is None:
                    pending[user_id] = {"username": first_name, "score": points, "words_found": 1}
                else:
                    pbucket["score"] += points
                    pbucket["words_found"] += 1
                    pbucket["username"] = first_name

                game["found_count"] += 1
                game["last_activity"] = time.monotonic()

                if game["found_count"] >= game["total_words"]:
                    game["ending"] = True
                    is_game_over = True
                else:
                    is_game_over = False
                    game["current_round"] = _create_ftb_round()
                    game["word_start_time"] = time.monotonic()
            finally:
                lock.release()

            if is_game_over:
                await end_ftb_game(chat_id, reason="win")
            else:
                nxt = game["current_round"]
                found_msg = (
                    f"{html.escape(first_name)} found '{html.escape(attempt.capitalize())}'\n\n"
                    f"⏰ Time: {time_str}\n"
                    f"🪙 +{points} points\n\n"
                    f"📚 Letters: {nxt['letters']}\n"
                    f"🎲 {nxt['pattern']}\n\n"
                    f"Total words found: {game['found_count']}/{game['total_words']}"
                )
                await queue_send(chat_id, found_msg)
            return

        # --- Standard Word Scramble Logic ---
        if len(attempt) < 3 or len(attempt) > 12:
            return
        if attempt not in game["target_words"]:
            return

        already_found = False
        is_game_over = False
        found_count = 0

        lock = game["lock"]
        try:
            await asyncio.wait_for(lock.acquire(), timeout=2.0)
        except asyncio.TimeoutError:
            logger.warning(f"check_word lock timeout chat={chat_id}, dropping attempt")
            return
        try:
            if chat_id not in games or game.get("ending"):
                return
            if attempt in game["found_set"]:
                already_found = True
            else:
                game["found_set"].add(attempt)
                game["found"].append(attempt)
                found_count = len(game["found"])
                if found_count >= game["total_words"]:
                    game["ending"] = True
                    is_game_over = True
        finally:
            lock.release()

        if already_found:
            if _EMOJI_MODE.get(chat_id, False):
                _em = _CHAT_EMOJI.get(chat_id, "👀")
                _mid = message.message_id
                async def _react(cid=chat_id, mid=_mid, em=_em):
                    await GLOBAL_RL.acquire()
                    try:
                        await bot.set_message_reaction(
                            chat_id=cid,
                            message_id=mid,
                            reaction=[ReactionTypeEmoji(emoji=em)],
                        )
                    except Exception:
                        pass
                asyncio.create_task(_react())
            else:
                await queue_send(
                    chat_id,
                    f"{P_ALREADY} {html.escape(attempt.capitalize())} is already found",
                )
            return

        first_name = message.from_user.first_name
        user_id = message.from_user.id
        wlen = len(attempt)
        points = _POINTS[wlen] if wlen < len(_POINTS) else 10

        scores = game["user_scores"]
        bucket = scores.get(user_id)
        if bucket is None:
            scores[user_id] = {"name": first_name, "score": points}
        else:
            bucket["score"] += points
            bucket["name"] = first_name

        pending = game["pending_db_scores"]
        pbucket = pending.get(user_id)
        if pbucket is None:
            pending[user_id] = {"username": first_name, "score": points,
                                "words_found": 1, "longest_word": attempt}
        else:
            pbucket["score"] += points
            pbucket["words_found"] += 1
            pbucket["username"] = first_name
            if wlen > len(pbucket["longest_word"]):
                pbucket["longest_word"] = attempt

        if wlen >= 5:
            longest_map = game["user_words"]
            cur_longest = longest_map.get(user_id)
            if cur_longest is None or wlen > len(cur_longest):
                longest_map[user_id] = attempt

        game["last_activity"] = time.monotonic()
        found_msg = (
            f'{html.escape(first_name)} found "{html.escape(attempt.capitalize())}"\n'
            f'+{points} <tg-emoji emoji-id="5041796412954641308">💎</tg-emoji>\n\n'
            f'<tg-emoji emoji-id="5936111781981197900">⭐</tg-emoji>  {game["display_letters"]}\n\n'
            f'Total words found: {found_count}/{game["total_words"]}'
        )
        await queue_send(chat_id, found_msg)

        if is_game_over:
            await end_scramble_game(chat_id, reason="win")
    except Exception as e:
        logger.error(f"check_word error chat={chat_id}: {e}")


# ---------------------------------------------------------------------------
# Bot bootstrap
# ---------------------------------------------------------------------------
async def set_bot_commands():
    commands = [
        BotCommand(command="new", description="Start a new Word Scramble game"),
        BotCommand(command="hints", description="Show current letters and found words"),
        BotCommand(command="stats", description="View your stats, score and rank"),
        BotCommand(command="leaderboard", description="View the global top 10"),
        BotCommand(command="topchats", description="View the top 10 chats"),
        BotCommand(command="stop", description="Stop the current game (admins only)"),
        BotCommand(command="help", description="View all commands and how to play"),
    ]
    await bot.set_my_commands(commands)


_BG_TASKS: list = []


async def on_startup(dispatcher: Dispatcher):
    global _BOT_USERNAME, _BG_TASKS
    try:
        me = await bot.get_me()
        _BOT_USERNAME = me.username or ""
        logger.info(f"Bot username cached: @{_BOT_USERNAME}")
    except Exception as e:
        logger.error(f"Failed to fetch bot username: {e}")
        
    for t in _BG_TASKS:
        if not t.done():
            t.cancel()
    _BG_TASKS.clear()
    
    await load_bans()
    
    # --- NEW: Restore Active Puzzles from Backup ---
    try:
        import json, os
        if os.path.exists("puzzles_backup.json"):
            with open("puzzles_backup.json", "r") as f:
                backed_up_puzzles = json.load(f)
                # Convert string keys back to integers
                for cid_str, p_data in backed_up_puzzles.items():
                    fill_puzzles[int(cid_str)] = p_data
            os.remove("puzzles_backup.json")
            logger.info(f"Restored {len(fill_puzzles)} active puzzles.")
    except Exception as e:
        logger.error(f"Failed to restore puzzles: {e}")

    _BG_TASKS.append(asyncio.create_task(background_writer()))
    _BG_TASKS.append(asyncio.create_task(global_ticker()))
    _BG_TASKS.append(asyncio.create_task(fill_blank_scheduler()))
    _BG_TASKS.append(asyncio.create_task(fill_puzzle_cleanup()))
    _BG_TASKS.append(asyncio.create_task(heartbeat_logger()))


@dp.message(Command("shutdown", ignore_case=True))
async def cmd_shutdown(message: Message):
    try:
        if not _is_bot_creator(message):
            return
            
        await queue_send(message.chat.id, "⏳ Initiating shutdown sequence. Securing data...")
        
        active_chats = list(games.keys())
        for chat_id in active_chats:
            game_type = games[chat_id].get("game_type", "scramble")
            if game_type == "ftb":
                await end_ftb_game(chat_id, reason="stopped")
            else:
                await end_scramble_game(chat_id, reason="stopped")
            
        if active_chats:
            await asyncio.sleep(2.0)
            
        # Flush Scramble
        all_entries = [(ps, cid, sid) for _, ps, cid, sid in _DEFERRED_SCORE_QUEUE]
        _DEFERRED_SCORE_QUEUE.clear()
        pending_users = list(_PENDING_USER_IDS)
        _PENDING_USER_IDS.clear()
        
        global _PENDING_GAMES_COUNT
        if all_entries or pending_users or _PENDING_GAMES_COUNT > 0:
            await _flush_all_pending(all_entries, pending_users, _PENDING_GAMES_COUNT)
            
        # Flush FTB
        all_ftb_entries = [(ps, cid) for _, ps, cid in _DEFERRED_FTB_QUEUE]
        _DEFERRED_FTB_QUEUE.clear()
        if all_ftb_entries:
            await _flush_ftb_pending(all_ftb_entries)
            
        await _flush_pending_fill_scores()
        
        try:
            import json
            with open("puzzles_backup.json", "w") as f:
                json.dump(fill_puzzles, f)
        except Exception as e:
            logger.error(f"Failed to backup puzzles early: {e}")
            
        text = (
            "✅ <b>Shutdown Preparation Complete!</b>\n\n"
            f"• {len(active_chats)} active games forcefully stopped and saved.\n"
            "• All pending scores flushed to database.\n"
            "• Puzzles backed up.\n\n"
            "🛑 <b>You may now safely stop or restart the server.</b>"
        )
        await queue_send(message.chat.id, text)
        
    except Exception as e:
        logger.error(f"cmd_shutdown error: {e}")
        await queue_send(message.chat.id, f"❌ Error during shutdown prep: {e}")


async def on_shutdown(dispatcher: Dispatcher):
    logger.info("Graceful shutdown: stopping background tasks…")
    for t in _BG_TASKS:
        t.cancel()
    for t in _BG_TASKS:
        try:
            await t
        except Exception:
            pass

    logger.info("Auto-ending active games to save scores...")
    for chat_id in list(games.keys()):
        game_type = games[chat_id].get("game_type", "scramble")
        if game_type == "ftb":
            await end_ftb_game(chat_id, reason="stopped")
        else:
            await end_scramble_game(chat_id, reason="stopped")

    logger.info("Backing up active puzzles...")
    try:
        import json
        with open("puzzles_backup.json", "w") as f:
            json.dump(fill_puzzles, f)
    except Exception as e:
        logger.error(f"Failed to backup puzzles: {e}")

    logger.info("Draining chat pipelines…")
    pipes = list(_PIPELINES.values())
    for p in pipes:
        try:
            p.queue.put_nowait(None)
        except Exception:
            pass
    for p in pipes:
        if p.worker_task:
            try:
                await asyncio.wait_for(p.worker_task, timeout=3.0)
            except Exception:
                p.worker_task.cancel()

    logger.info("Flushing pending scores…")
    all_entries = [(ps, cid, sid) for _, ps, cid, sid in _DEFERRED_SCORE_QUEUE]
    _DEFERRED_SCORE_QUEUE.clear()
    pending_users = list(_PENDING_USER_IDS)
    _PENDING_USER_IDS.clear()
    global _PENDING_GAMES_COUNT
    if all_entries or pending_users or _PENDING_GAMES_COUNT > 0:
        await _flush_all_pending(all_entries, pending_users, _PENDING_GAMES_COUNT)
        
    all_ftb_entries = [(ps, cid) for _, ps, cid in _DEFERRED_FTB_QUEUE]
    _DEFERRED_FTB_QUEUE.clear()
    if all_ftb_entries:
        await _flush_ftb_pending(all_ftb_entries)
        
    await _flush_pending_fill_scores()

    if _DB_CONN:
        try:
            await _DB_CONN.execute("PRAGMA wal_checkpoint(TRUNCATE)")
            await _DB_CONN.close()
        except Exception:
            pass
    for conn in _DB_READ_POOL:
        try:
            await conn.close()
        except Exception:
            pass

    _log_listener.stop()
    await bot.session.close()


def _handle_task_exception(loop, context):
    exc = context.get("exception")
    msg = context.get("message", "Unknown async error")
    if exc:
        logger.error(f"Unhandled async task exception: {msg}", exc_info=exc)
    else:
        logger.error(f"Unhandled async task context: {msg}")


async def main():
    if _UVLOOP_ENABLED:
        logger.info("Event loop: uvloop (fast)")
    else:
        logger.info("Event loop: asyncio default (install uvloop for ~2-4x speedup)")

    load_words()
    load_puzzle_words()
    precompute_all_sets()

    logger.info("Initializing database…")
    await init_db()
    await set_bot_commands()

    loop = asyncio.get_event_loop()
    loop.set_exception_handler(_handle_task_exception)

    dp.startup.register(on_startup)
    dp.shutdown.register(on_shutdown)

    await bot.delete_webhook(drop_pending_updates=True)
    while True:
        try:
            await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
        except asyncio.CancelledError:
            break
        except Exception as e:
            logger.error(f"Polling loop error: {e}. Restarting in 5s…")
            await asyncio.sleep(5)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("Bot stopped.")
