import asyncio
import html
import io
import json
import logging
import os
import re
import secrets
import string
import psycopg2
from psycopg2.extras import RealDictCursor
import tempfile
import threading
import time
from datetime import datetime, timedelta
from decimal import Decimal, InvalidOperation
from difflib import SequenceMatcher
from typing import Any, Dict, Optional

from aiogram import Bot, Dispatcher, F
from aiogram.filters import Command
from aiogram.types import (
    CallbackQuery,
    ForceReply,
    FSInputFile,
    InputMediaPhoto,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
)
from dotenv import load_dotenv
from constants.emoji_ids import CUSTOM_EMOJI
from constants.translations import I18N, LANG_LABELS, SUPPORTED_LANGS

load_dotenv()

logging.basicConfig(
    level=(os.getenv("LOG_LEVEL") or "INFO").upper(),
    format="%(asctime)s %(levelname)s [%(name)s] %(message)s",
)
logger = logging.getLogger("shop_bot")

SHOP_BOT_TOKEN = os.getenv("SHOP_BOT_TOKEN") or os.getenv("TOKEN")
LOG_BOT_TOKEN = os.getenv("LOG_BOT_TOKEN")
OWNER_CHAT_ID = os.getenv("OWNER_CHAT_ID")
LOG_CHANNEL_ID = os.getenv("LOG_CHANNEL_ID")
REVIEW_CHAT_ID = os.getenv("REVIEW_CHAT_ID")
REVIEW_MESSAGE_ID = os.getenv("REVIEW_MESSAGE_ID")
try:
    CLEANUP_OWNER = (os.getenv("CLEANUP_OWNER") or "1") == "1"
except Exception:
    CLEANUP_OWNER = True
ORDER_BOT_USERNAME = os.getenv("ORDER_BOT_USERNAME") or "NalichieMm2Vexsento_Bot"
BANNED_WORDS_RAW = os.getenv("BANNED_WORDS") or ""
PAYMENT_STICKERS_RAW = os.getenv("PAYMENT_STICKERS") or ""
try:
    FLOOD_REPEAT_LIMIT = int(os.getenv("FLOOD_REPEAT_LIMIT") or 5)
except Exception:
    FLOOD_REPEAT_LIMIT = 5
try:
    MAX_WARNINGS = int(os.getenv("MAX_WARNINGS") or 3)
except Exception:
    MAX_WARNINGS = 3
try:
    FLOOD_WINDOW_SEC = int(os.getenv("FLOOD_WINDOW_SEC") or 60)
except Exception:
    FLOOD_WINDOW_SEC = 60
try:
    ORDERS_KEEP_DAYS = int(os.getenv("ORDERS_KEEP_DAYS") or 30)
except Exception:
    ORDERS_KEEP_DAYS = 30
try:
    RESERVATION_TTL_SEC = int(os.getenv("RESERVATION_TTL_SEC") or 600)
except Exception:
    RESERVATION_TTL_SEC = 600
try:
    RESERVATION_WARN_LIMIT = int(os.getenv("RESERVATION_WARN_LIMIT") or 3)
except Exception:
    RESERVATION_WARN_LIMIT = 3
DB_URL = os.getenv("DATABASE_URL") or os.getenv("DB_URL")

if not SHOP_BOT_TOKEN:
    raise SystemExit("Ошибка: SHOP_BOT_TOKEN/TOKEN не найден в файле .env")
if not OWNER_CHAT_ID or not OWNER_CHAT_ID.lstrip("-").isdigit():
    raise SystemExit("Ошибка: OWNER_CHAT_ID не найден или не число в .env")
if not DB_URL:
    raise SystemExit("Ошибка: DATABASE_URL не найден в .env")

OWNER_CHAT_ID = int(OWNER_CHAT_ID)
LOG_CHANNEL_ID = (
    int(LOG_CHANNEL_ID)
    if LOG_CHANNEL_ID and LOG_CHANNEL_ID.lstrip("-").isdigit()
    else None
)
REVIEW_CHAT_ID = (
    int(REVIEW_CHAT_ID)
    if REVIEW_CHAT_ID and REVIEW_CHAT_ID.lstrip("-").isdigit()
    else None
)
REVIEW_MESSAGE_ID = int(REVIEW_MESSAGE_ID) if REVIEW_MESSAGE_ID and REVIEW_MESSAGE_ID.isdigit() else None

bot = Bot(SHOP_BOT_TOKEN)
log_bot = Bot(LOG_BOT_TOKEN) if LOG_BOT_TOKEN else None
dp = Dispatcher()

print("Бот успешно запущен — токены загружены из .env")

# -------------------- Конфиг --------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
INVENTORY_FILE = os.path.join(BASE_DIR, "inventory.json")
IMAGES_DIR = os.path.join(BASE_DIR, "images")
MAX_PER_ITEM = 100
BANNED_WORDS = [w.strip().lower() for w in BANNED_WORDS_RAW.split(",") if w.strip()]
PAYMENT_STICKERS = [s.strip() for s in PAYMENT_STICKERS_RAW.split(",") if s.strip()]
PAYMENT_DIRECT_TEXT = "💳 Оплата прямая"
PAYMENT_BALANCE_TEXT = "💰 Оплата балансом"
PAYMENT_CANCEL_TEXT = "❌ Отмена"
SUSPICIOUS_CHECK_KEYWORDS = [
    "тип перевода",
    "квитанц",
    "дата и время по астане",
    "дата",
    "время",
    "астан",
    "комис",
    "отправител",
    "откуда",
    "сумм",
    "перевод совершен",
]
SUSPICIOUS_CHECK_KEYWORDS_EN = [
    "transfer type",
    "receipt",
    "date",
    "time",
    "commission",
    "sender",
    "from",
    "amount",
    "transfer completed",
]
SUSPICIOUS_CHECK_KEYWORDS_KZ = [
    "аударым турі",
    "түбіртек",
    "күні",
    "уақыты",
    "комиссия",
    "жіберуші",
    "қайдан",
    "сома",
    "аударым орындалды",
]
OCR_LANG = os.getenv("OCR_LANG") or "rus+eng"
try:
    OCR_MAX_PAGES = int(os.getenv("OCR_MAX_PAGES") or 5)
except Exception:
    OCR_MAX_PAGES = 5
try:
    OCR_TIMEOUT_SEC = int(os.getenv("OCR_TIMEOUT_SEC") or 30)
except Exception:
    OCR_TIMEOUT_SEC = 30
try:
    OCR_MAX_CONCURRENT = int(os.getenv("OCR_MAX_CONCURRENT") or 2)
except Exception:
    OCR_MAX_CONCURRENT = 2
VOICE_RECOGNITION_LANG = os.getenv("VOICE_RECOGNITION_LANG") or "ru-RU"
GROUP_CHAT_TYPES = {"group", "supergroup"}
LINK_RE = re.compile(r"(https?://|t\.me/|www\.)", re.IGNORECASE)

_inventory_lock = threading.RLock()
_inventory_cache: Dict[str, Any] = {}
_inventory_mtime = 0.0

_banned_lock = threading.RLock()

user_cart: Dict[int, Dict[str, int]] = {}
user_states: Dict[int, Dict[str, Any]] = {}
moderation_state: Dict[tuple, Dict[str, Any]] = {}
order_states: Dict[str, Dict[str, Any]] = {}
review_pending: Dict[int, str] = {}
_order_seq = 0
user_last_bot_message: Dict[int, Dict[str, Any]] = {}
active_views: Dict[int, Dict[str, Any]] = {}
order_reminder_tasks: Dict[str, asyncio.Task] = {}
order_locks: Dict[str, asyncio.Lock] = {}
reservations: Dict[int, Dict[str, Any]] = {}
reservation_tasks: Dict[int, asyncio.Task] = {}
reservation_warnings: Dict[int, int] = {}
topup_states: Dict[str, Dict[str, Any]] = {}
_topup_seq = 0
check_view_map: Dict[str, Dict[str, Any]] = {}
user_locale: Dict[int, str] = {}
mini_games: Dict[int, Dict[str, Any]] = {}
game_stats: Dict[int, Dict[str, int]] = {}
ocr_semaphore = asyncio.Semaphore(max(1, OCR_MAX_CONCURRENT))
checkers_invites: Dict[str, Dict[str, Any]] = {}
checkers_invite_tasks: Dict[str, asyncio.Task] = {}
checkers_last_sticker: Dict[int, str] = {}


def h(text: Any) -> str:
    return html.escape(str(text))


def get_user_lang(user_id: int) -> str:
    lang = (user_locale.get(user_id) or "ru").lower()
    return lang if lang in SUPPORTED_LANGS else "ru"


def set_user_lang(user_id: int, lang_code: str) -> None:
    lang = (lang_code or "").lower()
    if lang in SUPPORTED_LANGS:
        user_locale[user_id] = lang


def tr(user_id: int, key: str, **kwargs) -> str:
    lang = get_user_lang(user_id)
    template = I18N.get(lang, {}).get(key) or I18N["ru"].get(key) or key
    try:
        return template.format(**kwargs)
    except Exception:
        return template


def build_lang_keyboard() -> InlineKeyboardMarkup:
    rows = []
    for code in SUPPORTED_LANGS:
        rows.append(
            [InlineKeyboardButton(text=LANG_LABELS.get(code, code), callback_data=f"lang_set:{code}")]
        )
    return InlineKeyboardMarkup(inline_keyboard=rows)


def should_cleanup(chat_id: int) -> bool:
    if chat_id < 0:
        return False
    if chat_id == OWNER_CHAT_ID and not CLEANUP_OWNER:
        return False
    if LOG_CHANNEL_ID and chat_id == LOG_CHANNEL_ID:
        return False
    if REVIEW_CHAT_ID and chat_id == REVIEW_CHAT_ID:
        return False
    return True


def log_exception(context: str, exc: Optional[BaseException] = None) -> None:
    if exc is not None:
        logger.exception("%s: %s", context, exc)
        return
    logger.exception("%s", context)


async def run_blocking(func, *args, **kwargs):
    return await asyncio.to_thread(func, *args, **kwargs)


async def send_clean_message(chat_id: int, text: str, **kwargs):
    view_type = kwargs.pop("_view_type", "other")
    view_key = kwargs.pop("_view_key", None)
    view_kind = kwargs.pop("_view_kind", None)
    if should_cleanup(chat_id):
        last = user_last_bot_message.get(chat_id)
        if last and last.get("type") == "text":
            try:
                msg = await bot.edit_message_text(
                    text, chat_id=chat_id, message_id=last["id"], **kwargs
                )
                user_last_bot_message[chat_id] = {"id": last["id"], "type": "text"}
                msg_id = getattr(msg, "message_id", None) or last.get("id")
                set_active_view(chat_id, msg_id, view_type, view_key, view_kind)
                return msg
            except Exception:
                pass
        if last:
            try:
                await bot.delete_message(chat_id, last["id"])
            except Exception:
                pass
    msg = await bot.send_message(chat_id, text, **kwargs)
    if should_cleanup(chat_id):
        user_last_bot_message[chat_id] = {"id": msg.message_id, "type": "text"}
    msg_id = getattr(msg, "message_id", None) or (
        user_last_bot_message.get(chat_id, {}).get("id") if should_cleanup(chat_id) else None
    )
    set_active_view(chat_id, msg_id, view_type, view_key, view_kind)
    return msg


async def send_clean_photo(chat_id: int, photo, caption: str, **kwargs):
    view_type = kwargs.pop("_view_type", "other")
    view_key = kwargs.pop("_view_key", None)
    view_kind = kwargs.pop("_view_kind", None)
    if should_cleanup(chat_id):
        last = user_last_bot_message.get(chat_id)
        if last and last.get("type") == "photo":
            try:
                media = InputMediaPhoto(
                    media=photo,
                    caption=caption,
                    parse_mode=kwargs.get("parse_mode"),
                )
                msg = await bot.edit_message_media(
                    chat_id=chat_id,
                    message_id=last["id"],
                    media=media,
                    reply_markup=kwargs.get("reply_markup"),
                )
                user_last_bot_message[chat_id] = {"id": last["id"], "type": "photo"}
                msg_id = getattr(msg, "message_id", None) or last.get("id")
                set_active_view(chat_id, msg_id, view_type, view_key, view_kind)
                return msg
            except Exception:
                pass
        if last:
            try:
                await bot.delete_message(chat_id, last["id"])
            except Exception:
                pass
    msg = await bot.send_photo(chat_id, photo=photo, caption=caption, **kwargs)
    if should_cleanup(chat_id):
        user_last_bot_message[chat_id] = {"id": msg.message_id, "type": "photo"}
    msg_id = getattr(msg, "message_id", None) or (
        user_last_bot_message.get(chat_id, {}).get("id") if should_cleanup(chat_id) else None
    )
    set_active_view(chat_id, msg_id, view_type, view_key, view_kind)
    return msg


def get_db_conn():
    return psycopg2.connect(DB_URL, cursor_factory=RealDictCursor)


def init_db() -> None:
    conn = get_db_conn()
    try:
        with conn.cursor() as cur:
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS orders (
                    order_id TEXT PRIMARY KEY,
                    user_id BIGINT,
                    username TEXT,
                    nick TEXT,
                    total INTEGER,
                    created_ts BIGINT,
                    status TEXT,
                    items_json TEXT,
                    check_json TEXT
                )
                """
            )
            cur.execute(
                "CREATE INDEX IF NOT EXISTS idx_orders_created ON orders(created_ts)"
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS bans (
                    id BIGSERIAL PRIMARY KEY,
                    user_id BIGINT,
                    reason TEXT,
                    created_ts BIGINT,
                    actor_id BIGINT
                )
                """
            )
            cur.execute(
                "CREATE INDEX IF NOT EXISTS idx_bans_created ON bans(created_ts)"
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS banned (
                    user_id BIGINT PRIMARY KEY,
                    reason TEXT,
                    created_ts BIGINT,
                    actor_id BIGINT
                )
                """
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS users (
                    user_id BIGINT PRIMARY KEY,
                    internal_id TEXT UNIQUE,
                    username TEXT,
                    nick TEXT,
                    balance_cents BIGINT,
                    created_ts BIGINT
                )
                """
            )
            cur.execute(
                "CREATE INDEX IF NOT EXISTS idx_users_internal_id ON users(internal_id)"
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS topups (
                    topup_id TEXT PRIMARY KEY,
                    user_id BIGINT,
                    internal_id TEXT,
                    username TEXT,
                    amount_cents BIGINT,
                    created_ts BIGINT,
                    status TEXT,
                    check_json TEXT
                )
                """
            )
            cur.execute(
                "CREATE INDEX IF NOT EXISTS idx_topups_created ON topups(created_ts)"
            )
            cur.execute(
                """
                CREATE TABLE IF NOT EXISTS admin_tx_logs (
                    id BIGSERIAL PRIMARY KEY,
                    order_id TEXT,
                    user_id BIGINT,
                    username TEXT,
                    nick TEXT,
                    total INTEGER,
                    created_ts BIGINT,
                    check_json TEXT,
                    note_text TEXT
                )
                """
            )
            cur.execute(
                "CREATE INDEX IF NOT EXISTS idx_admin_tx_logs_created ON admin_tx_logs(created_ts)"
            )
        conn.commit()
    finally:
        conn.close()


def prune_old_orders() -> None:
    if ORDERS_KEEP_DAYS <= 0:
        return
    cutoff = int(time.time()) - (ORDERS_KEEP_DAYS * 86400)
    conn = get_db_conn()
    try:
        with conn.cursor() as cur:
            cur.execute("DELETE FROM orders WHERE created_ts < %s", (cutoff,))
        conn.commit()
    finally:
        conn.close()


def record_order(order: Dict[str, Any], status: str, created_ts: int) -> None:
    try:
        items_json = json.dumps(order.get("items", []), ensure_ascii=False)
        check_json = json.dumps(order.get("check", {}), ensure_ascii=False)
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                if ORDERS_KEEP_DAYS > 0:
                    cutoff = int(time.time()) - (ORDERS_KEEP_DAYS * 86400)
                    cur.execute("DELETE FROM orders WHERE created_ts < %s", (cutoff,))
                cur.execute(
                    """
                    INSERT INTO orders
                    (order_id, user_id, username, nick, total, created_ts, status, items_json, check_json)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (order_id) DO UPDATE SET
                        user_id = EXCLUDED.user_id,
                        username = EXCLUDED.username,
                        nick = EXCLUDED.nick,
                        total = EXCLUDED.total,
                        created_ts = EXCLUDED.created_ts,
                        status = EXCLUDED.status,
                        items_json = EXCLUDED.items_json,
                        check_json = EXCLUDED.check_json
                    """,
                    (
                        order.get("order_id"),
                        order.get("user_id"),
                        order.get("username"),
                        order.get("nick"),
                        int(order.get("total", 0)),
                        int(created_ts),
                        status,
                        items_json,
                        check_json,
                    ),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def update_order_status_db(order_id: str, status: str) -> None:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE orders SET status = %s WHERE order_id = %s",
                    (status, order_id),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def record_ban_history(user_id: int, reason: str, actor_id: Optional[int]) -> None:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO bans (user_id, reason, created_ts, actor_id)
                    VALUES (%s, %s, %s, %s)
                    """,
                    (user_id, reason, int(time.time()), actor_id),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def month_range_ts(year: int, month: int) -> tuple[int, int]:
    start = datetime(year, month, 1)
    if month == 12:
        end = datetime(year + 1, 1, 1)
    else:
        end = datetime(year, month + 1, 1)
    return int(start.timestamp()), int(end.timestamp())


def month_start_ts_now() -> int:
    now = datetime.now()
    return int(datetime(now.year, now.month, 1).timestamp())


def prune_admin_tx_logs() -> None:
    cutoff = month_start_ts_now()
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute("DELETE FROM admin_tx_logs WHERE created_ts < %s", (cutoff,))
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def record_admin_tx_log(order: Dict[str, Any], note_text: str, created_ts: Optional[int] = None) -> None:
    try:
        check_json = json.dumps(order.get("check", {}), ensure_ascii=False)
        ts = int(created_ts or time.time())
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO admin_tx_logs
                    (order_id, user_id, username, nick, total, created_ts, check_json, note_text)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    """,
                    (
                        order.get("order_id"),
                        order.get("user_id"),
                        order.get("username"),
                        order.get("nick"),
                        int(order.get("total") or 0),
                        ts,
                        check_json,
                        note_text,
                    ),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


async def admin_tx_prune_loop() -> None:
    while True:
        try:
            prune_admin_tx_logs()
        except Exception:
            pass
        now = datetime.now()
        next_day = datetime(now.year, now.month, now.day) + timedelta(days=1, minutes=5)
        delay = max(60.0, (next_day - now).total_seconds())
        await asyncio.sleep(delay)


def format_money(cents: int) -> str:
    try:
        cents = int(cents)
    except Exception:
        cents = 0
    sign = "-" if cents < 0 else ""
    cents = abs(cents)
    whole = cents // 100
    frac = cents % 100
    whole_str = f"{whole:,}".replace(",", " ")
    return f"{sign}{whole_str},{frac:02d}"


def parse_amount_to_cents(text: str) -> Optional[int]:
    if not text:
        return None
    cleaned = text.strip().replace(" ", "").replace(",", ".")
    if not re.fullmatch(r"\d+(\.\d{1,2})?", cleaned):
        return None
    try:
        dec = Decimal(cleaned)
    except InvalidOperation:
        return None
    if dec <= 0:
        return None
    return int(dec * 100)


def next_topup_id() -> str:
    global _topup_seq
    _topup_seq += 1
    return f"topup-{int(time.time())}-{_topup_seq}"


def record_topup(topup: Dict[str, Any], status: str, created_ts: int) -> None:
    try:
        check_json = json.dumps(topup.get("check", {}), ensure_ascii=False)
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO topups
                    (topup_id, user_id, internal_id, username, amount_cents, created_ts, status, check_json)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (topup_id) DO UPDATE SET
                        user_id = EXCLUDED.user_id,
                        internal_id = EXCLUDED.internal_id,
                        username = EXCLUDED.username,
                        amount_cents = EXCLUDED.amount_cents,
                        created_ts = EXCLUDED.created_ts,
                        status = EXCLUDED.status,
                        check_json = EXCLUDED.check_json
                    """,
                    (
                        topup.get("topup_id"),
                        topup.get("user_id"),
                        topup.get("internal_id"),
                        topup.get("username"),
                        int(topup.get("amount_cents", 0)),
                        int(created_ts),
                        status,
                        check_json,
                    ),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def update_topup_status_db(topup_id: str, status: str) -> None:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE topups SET status = %s WHERE topup_id = %s",
                    (status, topup_id),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def topup_status_label(status: str) -> str:
    if status == "accepted":
        return "✅ Принято"
    if status == "rejected":
        return "❌ Отклонено"
    return "⏳ Ожидание"


def build_topup_admin_keyboard(topup_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="⏳ В ожидании", callback_data=f"topup_status:{topup_id}:pending"
                ),
                InlineKeyboardButton(
                    text="✅ Принято", callback_data=f"topup_status:{topup_id}:accepted"
                ),
                InlineKeyboardButton(
                    text="❌ Отклонено", callback_data=f"topup_status:{topup_id}:rejected"
                ),
            ]
        ]
    )


def build_topup_admin_text(topup: Dict[str, Any], status: str) -> str:
    amount = format_money(int(topup.get("amount_cents", 0)))
    return (
        "#баланс\n"
        "<b>ПОПОЛНЕНИЕ БАЛАНСА</b>\n"
        f"<b>Статус:</b> {topup_status_label(status)}\n"
        f"<b>ID:</b> <code>{topup.get('topup_id')}</code>\n"
        f"<b>Сумма:</b> {amount}₸\n"
        f"<b>Время:</b> {h(topup.get('time', ''))}\n"
        f"<b>Покупатель:</b> @{h(topup.get('username', ''))} ({topup.get('user_id')})\n"
        f"<b>Внутр. ID:</b> <code>{h(topup.get('internal_id', ''))}</code>\n"
        f"<b>Чек:</b> {check_summary(topup.get('check'))}"
    )


def get_or_create_user(user: Any) -> Dict[str, Any]:
    user_id = int(getattr(user, "id", 0))
    username = getattr(user, "username", None) or ""
    now = int(time.time())
    conn = get_db_conn()
    try:
        with conn.cursor() as cur:
            cur.execute("SELECT * FROM users WHERE user_id = %s", (user_id,))
            row = cur.fetchone()
            if row:
                updated = False
                if not row.get("internal_id"):
                    internal_id = f"{secrets.randbelow(10**12):012d}"
                    cur.execute(
                        "UPDATE users SET internal_id = %s WHERE user_id = %s",
                        (internal_id, user_id),
                    )
                    row["internal_id"] = internal_id
                    updated = True
                if username and row.get("username") != username:
                    cur.execute(
                        "UPDATE users SET username = %s WHERE user_id = %s",
                        (username, user_id),
                    )
                    row["username"] = username
                    updated = True
                if updated:
                    conn.commit()
                return row
            internal_id = None
            for _ in range(6):
                candidate = f"{secrets.randbelow(10**12):012d}"
                cur.execute(
                    "SELECT 1 FROM users WHERE internal_id = %s", (candidate,)
                )
                if not cur.fetchone():
                    internal_id = candidate
                    break
            if not internal_id:
                internal_id = f"{int(time.time()) % (10**12):012d}"
            cur.execute(
                """
                INSERT INTO users (user_id, internal_id, username, nick, balance_cents, created_ts)
                VALUES (%s, %s, %s, %s, %s, %s)
                """,
                (user_id, internal_id, username, "", 0, now),
            )
            conn.commit()
            return {
                "user_id": user_id,
                "internal_id": internal_id,
                "username": username,
                "nick": "",
                "balance_cents": 0,
                "created_ts": now,
            }
    except Exception as e:
        print(f"DB error in get_or_create_user: {e}")
        return {
            "user_id": user_id,
            "internal_id": f"{secrets.randbelow(10**12):012d}",
            "username": username,
            "nick": "",
            "balance_cents": 0,
            "created_ts": now,
        }
    finally:
        try:
            conn.close()
        except Exception:
            pass


def update_user_nick(user_id: int, nick: str) -> None:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE users SET nick = %s WHERE user_id = %s",
                    (nick, user_id),
                )
            conn.commit()
        finally:
            conn.close()
    except Exception:
        pass


def add_user_balance(user_id: int, delta_cents: int) -> Optional[int]:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    UPDATE users
                    SET balance_cents = COALESCE(balance_cents, 0) + %s
                    WHERE user_id = %s
                    RETURNING balance_cents
                    """,
                    (int(delta_cents), user_id),
                )
                row = cur.fetchone()
            conn.commit()
            if row and "balance_cents" in row:
                return int(row["balance_cents"])
        finally:
            conn.close()
    except Exception:
        pass
    return None


def get_user_by_internal_id(internal_id: str) -> Optional[Dict[str, Any]]:
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute("SELECT * FROM users WHERE internal_id = %s", (internal_id,))
                return cur.fetchone()
        finally:
            conn.close()
    except Exception:
        return None


def get_user_by_username(username: str) -> Optional[Dict[str, Any]]:
    name = (username or "").strip().lstrip("@")
    if not name:
        return None
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT * FROM users WHERE lower(username) = lower(%s) LIMIT 1",
                    (name,),
                )
                return cur.fetchone()
        finally:
            conn.close()
    except Exception:
        return None


def format_order_items_short(items: Any) -> str:
    if not items:
        return "—"
    parts = []
    for it in items:
        if not isinstance(it, dict):
            continue
        name = it.get("name") or it.get("key") or ""
        qty = int(it.get("qty") or it.get("count") or 0)
        if name:
            parts.append(f"{name}×{qty}")
    return ", ".join(parts) if parts else "—"


def format_order_items_short_html(items: Any) -> str:
    if not items:
        return "—"
    parts = []
    for it in items:
        if not isinstance(it, dict):
            continue
        name_raw = it.get("name") or it.get("key") or ""
        qty = int(it.get("qty") or it.get("count") or 0)
        if not name_raw:
            continue
        emoji_id = emoji_id_for_item(it.get("key") or name_raw, it)
        emoji = emoji_html(emoji_id)
        name = h(name_raw)
        if emoji:
            name = f"{emoji} {name}"
        parts.append(f"{name}×{qty}")
    return ", ".join(parts) if parts else "—"


def get_user_transactions(user_id: int, limit: int = 10) -> list[Dict[str, Any]]:
    txs: list[Dict[str, Any]] = []
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT order_id, total, created_ts, status, items_json, check_json
                    FROM orders
                    WHERE user_id = %s
                    ORDER BY created_ts DESC
                    LIMIT %s
                    """,
                    (user_id, limit),
                )
                for r in cur.fetchall():
                    try:
                        items = json.loads(r.get("items_json") or "[]")
                    except Exception:
                        items = []
                    try:
                        check = json.loads(r.get("check_json") or "{}")
                    except Exception:
                        check = {}
                    txs.append(
                        {
                            "created_ts": int(r.get("created_ts") or 0),
                            "type": "order",
                            "id": r.get("order_id"),
                            "amount": f"{int(r.get('total') or 0)}₸",
                            "status": r.get("status") or "pending",
                            "what": format_order_items_short(items),
                            "items": items,
                            "check": check,
                        }
                    )
                cur.execute(
                    """
                    SELECT topup_id, amount_cents, created_ts, status, check_json
                    FROM topups
                    WHERE user_id = %s
                    ORDER BY created_ts DESC
                    LIMIT %s
                    """,
                    (user_id, limit),
                )
                for r in cur.fetchall():
                    try:
                        check = json.loads(r.get("check_json") or "{}")
                    except Exception:
                        check = {}
                    txs.append(
                        {
                            "created_ts": int(r.get("created_ts") or 0),
                            "type": "topup",
                            "id": r.get("topup_id"),
                            "amount": f"{format_money(int(r.get('amount_cents') or 0))}₸",
                            "status": r.get("status") or "pending",
                            "what": "пополнение баланса",
                            "check": check,
                        }
                    )
        finally:
            conn.close()
    except Exception:
        return []
    txs.sort(key=lambda x: x.get("created_ts", 0), reverse=True)
    return txs[:limit]


def build_profile_text(user: Dict[str, Any]) -> str:
    username = user.get("username") or ""
    nick = user.get("nick") or "—"
    internal_id = user.get("internal_id") or "—"
    user_id = user.get("user_id") or 0
    if username:
        uname = f"@{h(username)}"
        link = f"https://t.me/{username}"
    else:
        uname = "—"
        link = f"tg://user?id={user_id}"
    link_html = f'<a href="{link}">ссылка</a>'
    balance = format_money(int(user.get("balance_cents") or 0))
    return (
        "<b>👤 Профиль</b>\n"
        f"<b>Юзернейм:</b> {uname}\n"
        f"<b>Ник:</b> {h(nick)}\n"
        f"<b>Ссылка:</b> {link_html}\n"
        f"<b>ID:</b> <code>{h(internal_id)}</code>\n\n"
        f"<b>💰 Баланс:</b> <u>{balance} ₸</u>"
    )


def build_profile_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="💰 Пополнить", callback_data="balance_topup"),
                InlineKeyboardButton(text="🛒 Каталог", callback_data="catalog"),
            ],
            [InlineKeyboardButton(text="⚡ Возможности", callback_data="menu_power")],
        ]
    )


async def show_profile(chat_id: int, user: Dict[str, Any]) -> None:
    await send_clean_message(
        chat_id,
        build_profile_text(user),
        reply_markup=build_profile_keyboard(),
        parse_mode="HTML",
        _view_type="profile",
    )


def is_private_chat(chat: Any) -> bool:
    return getattr(chat, "type", None) == "private"


def is_group_chat(chat: Any) -> bool:
    return getattr(chat, "type", None) in GROUP_CHAT_TYPES


def emoji_id_for_item(key: str, item: Optional[Dict[str, Any]] = None) -> Optional[str]:
    candidates = [key]
    if item:
        name = item.get("name")
        image = item.get("image")
        if name:
            candidates.append(name)
        if image:
            base = image[:-4] if image.lower().endswith(".png") else image
            candidates.append(base)
    for c in candidates:
        if not c:
            continue
        norm = safe_key(str(c)).lower()
        if norm in CUSTOM_EMOJI:
            return CUSTOM_EMOJI[norm]
    return None


def emoji_html(emoji_id: Optional[str]) -> str:
    if not emoji_id:
        return ""
    return f'<tg-emoji emoji-id="{emoji_id}">⭐</tg-emoji>'


def build_payment_method_keyboard() -> ReplyKeyboardMarkup:
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text=PAYMENT_DIRECT_TEXT)],
            [KeyboardButton(text=PAYMENT_BALANCE_TEXT)],
            [KeyboardButton(text=PAYMENT_CANCEL_TEXT)],
        ],
        resize_keyboard=True,
        one_time_keyboard=True,
    )


async def send_payment_sticker(chat_id: int) -> None:
    if not PAYMENT_STICKERS:
        return
    try:
        sticker_id = PAYMENT_STICKERS[secrets.randbelow(len(PAYMENT_STICKERS))]
        await bot.send_sticker(chat_id, sticker_id)
    except Exception:
        pass


def set_active_view(
    chat_id: int,
    message_id: Optional[int],
    view_type: str,
    view_key: Optional[str] = None,
    view_kind: Optional[str] = None,
) -> None:
    if not message_id:
        return
    data = {"type": view_type, "message_id": message_id}
    if view_key:
        data["item_key"] = view_key
    if view_kind:
        data["kind"] = view_kind
    active_views[chat_id] = data


def mention_short(user: Any) -> str:
    if user and getattr(user, "username", None):
        return f"@{user.username}"
    name = h(getattr(user, "full_name", "") or getattr(user, "first_name", "") or "пользователь")
    return name


def contains_link(text: str) -> bool:
    return bool(LINK_RE.search(text))


def contains_banned_words(text: str) -> bool:
    if not BANNED_WORDS:
        return False
    lower = text.lower()
    return any(word in lower for word in BANNED_WORDS)


def is_faq_question(text: str) -> bool:
    t = text.lower()
    return "как заказать" in t or "как оформить заказ" in t or "как купить" in t


def get_mod_state(chat_id: int, user_id: int) -> Dict[str, Any]:
    key = (chat_id, user_id)
    state = moderation_state.get(key)
    if not state:
        state = {"last_text": "", "count": 0, "warnings": 0, "last_ts": 0.0}
        moderation_state[key] = state
    return state


async def warn_user(message: Message, state: Dict[str, Any], reason: str) -> None:
    state["warnings"] = int(state.get("warnings", 0)) + 1
    warn_count = state["warnings"]
    text = (
        f"Нарушение! {reason} в канале {warn_count}/{MAX_WARNINGS} предупреждений "
        f"{mention_short(message.from_user)}"
    )
    try:
        await message.answer(text, parse_mode="HTML")
    except Exception:
        pass
    if warn_count >= MAX_WARNINGS:
        ban_user(message.from_user.id, reason, None)
        record_ban_history(message.from_user.id, reason, None)
        try:
            await bot.ban_chat_member(message.chat.id, message.from_user.id)
        except Exception:
            pass
        try:
            await message.answer(
                f"Пользователь {mention_short(message.from_user)} забанен. Причина: {reason}",
                parse_mode="HTML",
            )
        except Exception:
            pass


def next_order_id() -> str:
    global _order_seq
    _order_seq += 1
    return f"{int(time.time())}-{_order_seq}"


def status_label(status: str) -> str:
    if status == "accepted":
        return "✅ Принято"
    if status == "rejected":
        return "❌ Отклонено"
    return "⏳ Ожидание"


def check_summary(check: Any) -> str:
    if isinstance(check, dict):
        ctype = check.get("type")
        if ctype == "photo":
            return "Фото"
        if ctype == "document":
            name = check.get("name") or "файл"
            return f"Файл: {h(name)}"
        if ctype == "balance":
            return "Баланс"
        return "Файл"
    if check:
        return h(check)
    return "—"


def cleanup_check_views(max_age_sec: int = 3600, max_items: int = 300) -> None:
    now = time.time()
    for key, item in list(check_view_map.items()):
        created_ts = float(item.get("created_ts") or 0)
        if now - created_ts > max_age_sec:
            check_view_map.pop(key, None)
    if len(check_view_map) > max_items:
        by_ts = sorted(
            check_view_map.items(),
            key=lambda kv: float(kv[1].get("created_ts") or 0),
        )
        for key, _ in by_ts[: max(0, len(check_view_map) - max_items)]:
            check_view_map.pop(key, None)


def next_check_view_id() -> str:
    for _ in range(5):
        token = secrets.token_hex(4)
        if token not in check_view_map:
            return token
    return f"{int(time.time())}{secrets.token_hex(2)}"


def register_check_view(check: Any) -> Optional[str]:
    if not isinstance(check, dict):
        return None
    if not check.get("file_id"):
        return None
    cleanup_check_views()
    token = next_check_view_id()
    check_view_map[token] = {"check": check, "created_ts": time.time()}
    return token


def build_admin_keyboard(order_id: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="⏳ В ожидании", callback_data=f"order_status:{order_id}:pending"),
                InlineKeyboardButton(text="✅ Принято", callback_data=f"order_status:{order_id}:accepted"),
                InlineKeyboardButton(text="❌ Отклонено", callback_data=f"order_status:{order_id}:rejected"),
            ],
            [InlineKeyboardButton(text="🚫 Бан", callback_data=f"order_ban:{order_id}")],
        ]
    )


def format_items_text(items: Any) -> str:
    if not items:
        return "—"
    lines = []
    for it in items:
        if isinstance(it, dict):
            name = h(it.get("name") or it.get("key") or "")
            qty = int(it.get("qty") or it.get("count") or 0)
            price = int(it.get("price") or 0)
            line_total = int(it.get("line_total") or (price * qty))
            lines.append(f"• {name} × {qty} — {line_total}₸")
        else:
            lines.append(str(it))
    return "\n".join(lines) if lines else "—"


def build_admin_text(order: Dict[str, Any], status: str) -> str:
    items = order.get("items", [])
    items_text = format_items_text(items)
    check = order.get("check")
    paid_with = order.get("paid_with")
    pay_line = ""
    if paid_with == "balance" or (isinstance(check, dict) and check.get("type") == "balance"):
        pay_line = "<b>Оплата:</b> Баланс\n"
    return (
        "#годли\n"
        "<b>НОВАЯ ПОКУПКА</b>\n"
        f"<b>Статус:</b> {status_label(status)}\n"
        f"<b>Заказ ID:</b> <code>{order.get('order_id')}</code>\n"
        f"<b>Сумма:</b> {order.get('total')}₸\n"
        f"{pay_line}"
        f"<b>Время:</b> {h(order.get('time', ''))}\n"
        f"<b>Ник в Roblox:</b> {h(order.get('nick', ''))}\n"
        f"<b>Покупатель:</b> @{h(order.get('username', ''))} ({order.get('user_id')})\n\n"
        f"<b>Товары:</b>\n{items_text}\n\n"
        f"<b>Чек:</b> {check_summary(order.get('check'))}\n\n"
        "Выдача через Aslan_ShRa666\n"
        "Лучший шоп в СНГ — 900+ отзывов"
    )


async def send_review_prompt(user_id: int) -> None:
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="Отказаться от отзыва", callback_data="review_decline")]
        ]
    )
    await send_clean_message(
        user_id,
        "<b>Отлично!</b> Ваш заказ выполнен.\n"
        "Оставьте отзыв с подписью <b>@Vexsento</b>.\n"
        "Напишите отзыв сюда — я опубликую под постом.",
        reply_markup=kb,
        parse_mode="HTML",
    )


async def send_check_to_admin(check: Any, chat_id: int, reply_to: Optional[int] = None) -> Optional[int]:
    if not isinstance(check, dict):
        return None
    ctype = check.get("type")
    file_id = check.get("file_id")
    if not file_id:
        return None
    try:
        if ctype == "photo":
            msg = await bot.send_photo(
                chat_id,
                photo=file_id,
                caption="Чек",
                reply_to_message_id=reply_to,
            )
            return msg.message_id
        elif ctype == "document":
            msg = await bot.send_document(
                chat_id,
                document=file_id,
                caption="Чек",
                reply_to_message_id=reply_to,
            )
            return msg.message_id
    except Exception:
        return None
    return None


def normalize_check_text(text: str) -> str:
    normalized = (text or "").lower().replace("ё", "е")
    normalized = re.sub(r"[\u200b\u200c\u200d\ufeff]", "", normalized)
    normalized = re.sub(r"[^\w\s]+", " ", normalized, flags=re.UNICODE)
    normalized = re.sub(r"\s+", " ", normalized)
    return normalized.strip()


def all_check_keywords() -> list[str]:
    merged = (
        list(SUSPICIOUS_CHECK_KEYWORDS)
        + list(SUSPICIOUS_CHECK_KEYWORDS_EN)
        + list(SUSPICIOUS_CHECK_KEYWORDS_KZ)
    )
    out: list[str] = []
    seen: set[str] = set()
    for raw in merged:
        kw = normalize_check_text(raw)
        if not kw or kw in seen:
            continue
        seen.add(kw)
        out.append(kw)
    return out


def matched_suspicious_keywords(text: str) -> list[str]:
    normalized = normalize_check_text(text)
    if not normalized:
        return []
    found: list[str] = []
    words = normalized.split()
    for kw in all_check_keywords():
        if kw in normalized:
            found.append(kw)
            continue
        # Fuzzy fallback for OCR noise in single-word keys.
        if " " in kw or len(kw) < 5:
            continue
        hit = False
        for word in words:
            if kw in word or word in kw:
                hit = True
                break
            if SequenceMatcher(a=kw, b=word).ratio() >= 0.86:
                hit = True
                break
        if hit:
            found.append(kw)
    return found


async def download_telegram_file_bytes(file_id: str) -> Optional[bytes]:
    if not file_id:
        return None
    try:
        tg_file = await bot.get_file(file_id)
        if not tg_file.file_path:
            return None
        buf = io.BytesIO()
        await bot.download_file(tg_file.file_path, destination=buf)
        return buf.getvalue()
    except Exception:
        return None


def extract_text_from_image_bytes(data: bytes) -> str:
    if not data:
        return ""
    try:
        from PIL import Image  # type: ignore
        from PIL import ImageEnhance  # type: ignore
        from PIL import ImageFilter  # type: ignore
        from PIL import ImageOps  # type: ignore
        import pytesseract  # type: ignore
    except Exception:
        return ""

    def build_variants(image: Any) -> list[Any]:
        variants: list[Any] = []
        img = image
        if img.mode not in {"RGB", "L"}:
            img = img.convert("RGB")
        gray = ImageOps.grayscale(img)
        auto = ImageOps.autocontrast(gray)
        contrast = ImageEnhance.Contrast(auto).enhance(2.4)
        sharp = contrast.filter(ImageFilter.SHARPEN)
        binary = sharp.point(lambda p: 255 if p > 162 else 0, mode="1")
        inv = ImageOps.invert(contrast)
        variants.extend([img, gray, auto, contrast, sharp, binary, inv])
        return variants

    try:
        with Image.open(io.BytesIO(data)) as img:
            chunks: list[str] = []
            seen: set[str] = set()
            for variant in build_variants(img):
                for psm in (6, 11, 4):
                    try:
                        text = pytesseract.image_to_string(
                            variant,
                            lang=OCR_LANG,
                            config=f"--oem 3 --psm {psm}",
                        )
                    except Exception:
                        continue
                    t = (text or "").strip()
                    if not t:
                        continue
                    if t in seen:
                        continue
                    seen.add(t)
                    chunks.append(t)
            return "\n".join(chunks).strip()
    except Exception:
        return ""


def extract_text_from_pdf_bytes(data: bytes) -> str:
    if not data:
        return ""
    try:
        import fitz  # type: ignore
    except Exception:
        return ""
    chunks: list[str] = []
    try:
        with fitz.open(stream=data, filetype="pdf") as pdf:
            max_pages = min(len(pdf), max(1, OCR_MAX_PAGES))
            for page_idx in range(max_pages):
                page = pdf[page_idx]
                page_text = ""
                try:
                    page_text = page.get_text("text") or ""
                except Exception:
                    page_text = ""
                if page_text.strip():
                    chunks.append(page_text)
                    continue
                try:
                    pix = page.get_pixmap(matrix=fitz.Matrix(3, 3), alpha=False)
                    chunks.append(extract_text_from_image_bytes(pix.tobytes("png")))
                except Exception:
                    pass
    except Exception:
        return ""
    return "\n".join(x for x in chunks if x).strip()


def extract_text_from_check_bytes(check: Dict[str, Any], data: bytes) -> str:
    if not data:
        return ""
    ctype = str(check.get("type") or "").lower()
    if ctype == "photo":
        return extract_text_from_image_bytes(data)
    if ctype != "document":
        return ""
    name = str(check.get("name") or "").lower()
    mime = str(check.get("mime_type") or "").lower()
    is_pdf = name.endswith(".pdf") or "pdf" in mime
    if is_pdf:
        text = extract_text_from_pdf_bytes(data)
        if text:
            return text
    text = extract_text_from_image_bytes(data)
    if text:
        return text
    if "text" in mime or name.endswith(".txt"):
        try:
            return data.decode("utf-8", errors="ignore")
        except Exception:
            return ""
    return ""


async def extract_text_from_check(check: Dict[str, Any]) -> str:
    file_id = str(check.get("file_id") or "")
    raw = await download_telegram_file_bytes(file_id)
    if not raw:
        return ""
    return await asyncio.to_thread(extract_text_from_check_bytes, check, raw)


def ocr_preview(text: str, limit: int = 550) -> str:
    if not text:
        return "—"
    clean = re.sub(r"\s+", " ", text).strip()
    if len(clean) <= limit:
        return h(clean)
    return h(clean[:limit]) + "…"


async def notify_admin_about_suspicious_check(
    user: Any, internal_id: str, check: Dict[str, Any], ocr_text: str = "", note: str = ""
) -> None:
    username = getattr(user, "username", None) or ""
    user_id = int(getattr(user, "id", 0) or 0)
    username_text = f"@{h(username)}" if username else "без_username"
    note_block = f"\n<b>Причина:</b> {h(note)}" if note else ""
    text = (
        "🚨 <b>Новое уведомление! Подозрительный чек!</b>\n"
        f"<b>Пользователь:</b> {username_text} ({user_id})\n"
        f"<b>Внутр. ID:</b> <code>{h(internal_id or '—')}</code>"
        f"{note_block}\n"
        f"<b>OCR фрагмент:</b> {ocr_preview(ocr_text)}"
    )
    msg = await bot.send_message(OWNER_CHAT_ID, text, parse_mode="HTML")
    await send_check_to_admin(check, OWNER_CHAT_ID, msg.message_id)


async def analyze_check_and_report(user: Any, internal_id: str, check: Dict[str, Any]) -> None:
    reason = ""
    text = ""
    try:
        async with ocr_semaphore:
            text = await asyncio.wait_for(
                extract_text_from_check(check),
                timeout=max(5, OCR_TIMEOUT_SEC),
            )
    except asyncio.TimeoutError:
        reason = "OCR timeout"
    except Exception:
        reason = "OCR error"
    try:
        if not reason and matched_suspicious_keywords(text):
            return
        await notify_admin_about_suspicious_check(
            user,
            internal_id,
            check,
            ocr_text=text,
            note=reason or "Ключевые слова не найдены",
        )
    except Exception:
        pass


def clone_message_with_text(message: Message, text: str) -> Optional[Message]:
    try:
        return message.model_copy(update={"text": text})
    except Exception:
        return None


def normalize_game_text(text: str) -> str:
    return re.sub(r"\s+", " ", (text or "").strip().lower())


def cipher_shift_text(text: str, shift: int) -> str:
    out: list[str] = []
    alphabets = [
        "abcdefghijklmnopqrstuvwxyz",
        "ABCDEFGHIJKLMNOPQRSTUVWXYZ",
        "абвгдежзийклмнопрстуфхцчшщъыьэюя",
        "АБВГДЕЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯ",
    ]
    maps: Dict[str, str] = {}
    for alpha in alphabets:
        size = len(alpha)
        for i, ch in enumerate(alpha):
            maps[ch] = alpha[(i + shift) % size]
    for ch in text:
        out.append(maps.get(ch, ch))
    return "".join(out)


def choose_cipher_phrase(user_id: int) -> str:
    phrases = [
        "Безопасность важнее скорости",
        "Проверяй реквизиты дважды",
        "Сильный бот любит чистую архитектуру",
        "Данные побеждают догадки",
        "Шифр раскрывается вниманием",
    ]
    return phrases[(int(time.time()) + user_id) % len(phrases)]


def init_game_stats(user_id: int) -> Dict[str, int]:
    stats = game_stats.get(user_id)
    defaults = {
        "cipher_games": 0,
        "cipher_wins": 0,
        "bulls_games": 0,
        "bulls_wins": 0,
        "checkers_games": 0,
        "checkers_wins": 0,
    }
    if not stats:
        stats = defaults.copy()
        game_stats[user_id] = stats
    else:
        for key, value in defaults.items():
            stats.setdefault(key, value)
    return stats


def start_cipher_game(user_id: int) -> Dict[str, Any]:
    phrase = choose_cipher_phrase(user_id)
    shift = 2 + ((user_id + int(time.time())) % 7)
    encoded = cipher_shift_text(phrase, shift)
    game = {
        "type": "cipher",
        "phrase": phrase,
        "encoded": encoded,
        "attempts": 0,
        "started_ts": int(time.time()),
    }
    mini_games[user_id] = game
    stats = init_game_stats(user_id)
    stats["cipher_games"] = int(stats.get("cipher_games", 0)) + 1
    return game


def bulls_and_cows(secret: str, guess: str) -> tuple[int, int]:
    bulls = sum(1 for i, c in enumerate(guess) if secret[i] == c)
    cows = sum(1 for c in guess if c in secret) - bulls
    return bulls, cows


def start_bulls_game(user_id: int) -> Dict[str, Any]:
    digits = string.digits
    secret_chars: list[str] = []
    while len(secret_chars) < 4:
        ch = digits[secrets.randbelow(10)]
        if ch not in secret_chars:
            secret_chars.append(ch)
    secret = "".join(secret_chars)
    game = {
        "type": "bulls",
        "secret": secret,
        "attempts": 0,
        "max_attempts": 12,
        "started_ts": int(time.time()),
    }
    mini_games[user_id] = game
    stats = init_game_stats(user_id)
    stats["bulls_games"] = int(stats.get("bulls_games", 0)) + 1
    return game


CHECKERS_FILES = "abcdefgh"
CHECKERS_BLANK = "ㅤ"
CHECKERS_LEVEL_DEPTH = {1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6}
CHECKERS_LEVEL_RANDOMNESS = {1: 0.55, 2: 0.35, 3: 0.2, 4: 0.1, 5: 0.04, 6: 0.0}
CHECKERS_LEVEL_TIME_BUDGET = {1: 0.25, 2: 0.5, 3: 1.0, 4: 1.8, 5: 2.8, 6: 4.5}
CHECKERS_MAX_PLIES = 120
CHECKERS_INVITE_TTL_SEC = 180
CHECKERS_LEVEL_LABELS = {
    "ru": {
        1: "Новичок",
        2: "Легкий",
        3: "Средний",
        4: "Сложный",
        5: "Эксперт",
        6: "Экстремальный",
    },
    "en": {
        1: "Novice",
        2: "Easy",
        3: "Normal",
        4: "Hard",
        5: "Expert",
        6: "Extreme",
    },
    "kz": {
        1: "Бастаушы",
        2: "Жеңіл",
        3: "Орташа",
        4: "Қиын",
        5: "Сарапшы",
        6: "Экстремал",
    },
}


def clamp_checkers_level(level: Any) -> int:
    try:
        value = int(level)
    except Exception:
        value = 1
    return max(1, min(6, value))


def checkers_level_label(user_id: int, level: int) -> str:
    lang = get_user_lang(user_id)
    labels = CHECKERS_LEVEL_LABELS.get(lang) or CHECKERS_LEVEL_LABELS["ru"]
    return labels.get(level, str(level))


def build_checkers_level_kb(user_id: int) -> InlineKeyboardMarkup:
    rows = []
    for level in range(1, 7):
        rows.append(
            [
                InlineKeyboardButton(
                    text=f"{level} • {checkers_level_label(user_id, level)}",
                    callback_data=f"game_checkers_level:{level}",
                )
            ]
        )
    rows.append([InlineKeyboardButton(text="↩️ Назад", callback_data="menu_games")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def build_checkers_mode_kb(user_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=tr(user_id, "game_checkers_mode_ai"), callback_data="game_checkers_mode_ai")],
            [InlineKeyboardButton(text=tr(user_id, "game_checkers_mode_friend"), callback_data="game_checkers_mode_friend")],
            [InlineKeyboardButton(text=tr(user_id, "menu_back"), callback_data="menu_games")],
        ]
    )


def build_checkers_end_kb(level: int, user_id: int, opponent_id: Optional[int] = None) -> InlineKeyboardMarkup:
    if opponent_id is not None:
        rematch_text = tr(user_id, "checkers_rematch_friend")
        rematch_cb = f"checkers_rematch_friend:{int(opponent_id)}"
    else:
        rematch_text = tr(user_id, "checkers_rematch")
        rematch_cb = f"checkers_rematch_ai:{clamp_checkers_level(level)}"
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=rematch_text, callback_data=rematch_cb)],
            [
                InlineKeyboardButton(text=tr(user_id, "checkers_other_level"), callback_data="checkers_choose_level"),
                InlineKeyboardButton(text=tr(user_id, "checkers_with_friend_short"), callback_data="game_checkers_mode_friend"),
            ],
            [InlineKeyboardButton(text="👤 Профиль", callback_data="profile")],
        ]
    )


async def send_game_sticker(chat_id: int) -> None:
    if not PAYMENT_STICKERS:
        return
    pool = PAYMENT_STICKERS
    prev = checkers_last_sticker.get(chat_id)
    choices = [s for s in pool if s != prev] or pool
    try:
        sticker_id = choices[secrets.randbelow(len(choices))]
        await bot.send_sticker(chat_id, sticker_id)
        checkers_last_sticker[chat_id] = sticker_id
    except Exception:
        pass


def checkers_format_countdown(seconds_left: int) -> str:
    sec = max(0, int(seconds_left))
    return f"{sec // 60:02d}:{sec % 60:02d}"


def checkers_invite_kb(invite_id: str, user_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text=tr(user_id, "checkers_accept"), callback_data=f"checkers_invite_accept:{invite_id}"),
                InlineKeyboardButton(text=tr(user_id, "checkers_decline"), callback_data=f"checkers_invite_decline:{invite_id}"),
            ]
        ]
    )


def checkers_next_invite_id() -> str:
    return f"inv-{int(time.time())}-{secrets.token_hex(3)}"


def checkers_take_invite(invite_id: str) -> Optional[Dict[str, Any]]:
    invite = checkers_invites.pop(invite_id, None)
    task = checkers_invite_tasks.pop(invite_id, None)
    if task and not task.done() and task is not asyncio.current_task():
        task.cancel()
    return invite


def checkers_player_color(game: Dict[str, Any], user_id: int) -> str:
    players = game.get("players") or {}
    if int(players.get("white") or 0) == int(user_id):
        return "white"
    if int(players.get("black") or 0) == int(user_id):
        return "black"
    return ""


def checkers_side_for_color(color: str) -> str:
    return "human" if color == "white" else "ai"


def checkers_is_pvp(game: Dict[str, Any]) -> bool:
    return game.get("mode") == "pvp"


def checkers_pvp_context(
    game: Dict[str, Any], user_id: int
) -> tuple[
    list[Dict[str, Any]],
    Optional[tuple[int, int]],
    set[tuple[int, int]],
    set[tuple[int, int]],
    bool,
    str,
]:
    board = game.get("board")
    if not isinstance(board, list):
        return [], None, set(), set(), False, ""
    color = checkers_player_color(game, user_id)
    if not color:
        return [], None, set(), set(), False, ""
    side = checkers_side_for_color(color)
    legal_moves = checkers_generate_moves(board, side)
    can_move = game.get("turn") == color
    selectable = {
        tuple(path[0])
        for move in legal_moves
        for path in [list(move.get("path") or [])]
        if len(path) >= 2
    }
    selected_by = game.get("ui_selected_by")
    if not isinstance(selected_by, dict):
        selected_by = {}
        game["ui_selected_by"] = selected_by
    selected_raw = selected_by.get(int(user_id))
    selected: Optional[tuple[int, int]] = None
    if isinstance(selected_raw, (list, tuple)) and len(selected_raw) == 2:
        try:
            candidate = (int(selected_raw[0]), int(selected_raw[1]))
            if candidate in selectable:
                selected = candidate
        except Exception:
            selected = None
    if selected is None:
        selected_by[int(user_id)] = None
    targets: set[tuple[int, int]] = set()
    if can_move and selected is not None:
        for move in legal_moves:
            path = list(move.get("path") or [])
            if len(path) >= 2 and tuple(path[0]) == selected:
                targets.add(tuple(path[1]))
    if not can_move:
        selectable = set()
        targets = set()
        selected = None
    return legal_moves, selected, selectable, targets, can_move, color


def checkers_remove_game(game: Dict[str, Any]) -> None:
    if checkers_is_pvp(game):
        players = game.get("players") or {}
        for uid in (players.get("white"), players.get("black")):
            if uid is None:
                continue
            if mini_games.get(int(uid)) is game:
                mini_games.pop(int(uid), None)
        return
    owner_id = game.get("owner_id")
    if owner_id is not None and mini_games.get(int(owner_id)) is game:
        mini_games.pop(int(owner_id), None)


def start_checkers_pvp_game(white_id: int, black_id: int) -> Dict[str, Any]:
    game = {
        "type": "checkers",
        "mode": "pvp",
        "board": checkers_new_board(),
        "players": {"white": int(white_id), "black": int(black_id)},
        "turn": "white",
        "ui_selected_by": {int(white_id): None, int(black_id): None},
        "ply_count": 0,
        "max_plies": CHECKERS_MAX_PLIES,
        "started_ts": int(time.time()),
    }
    mini_games[int(white_id)] = game
    mini_games[int(black_id)] = game
    stats_white = init_game_stats(int(white_id))
    stats_black = init_game_stats(int(black_id))
    stats_white["checkers_games"] = int(stats_white.get("checkers_games", 0)) + 1
    stats_black["checkers_games"] = int(stats_black.get("checkers_games", 0)) + 1
    return game


def build_checkers_invite_sender_text(invite: Dict[str, Any], left_sec: int, viewer_id: int) -> str:
    to_username = (invite.get("to_username") or "").strip()
    target = f"@{h(to_username)}" if to_username else f"id:{invite.get('to_id')}"
    return tr(viewer_id, "checkers_invite_sender", target=target, left=checkers_format_countdown(left_sec))


def build_checkers_invite_receiver_text(invite: Dict[str, Any], left_sec: int, viewer_id: int) -> str:
    from_username = (invite.get("from_username") or "").strip()
    sender = f"@{h(from_username)}" if from_username else f"id:{invite.get('from_id')}"
    return tr(viewer_id, "checkers_invite_receiver", sender=sender, left=checkers_format_countdown(left_sec))


async def checkers_invite_timer_loop(invite_id: str) -> None:
    while True:
        invite = checkers_invites.get(invite_id)
        if not invite or invite.get("status") != "pending":
            return
        left = int(float(invite.get("expires_ts") or 0) - time.time())
        if left <= 0:
            break
        from_id = int(invite.get("from_id") or 0)
        to_id = int(invite.get("to_id") or 0)
        from_mid = int(invite.get("from_message_id") or 0)
        to_mid = int(invite.get("to_message_id") or 0)
        if from_id and from_mid:
            try:
                await bot.edit_message_text(
                    build_checkers_invite_sender_text(invite, left, from_id),
                    chat_id=from_id,
                    message_id=from_mid,
                    parse_mode="HTML",
                )
            except Exception:
                pass
        if to_id and to_mid:
            try:
                await bot.edit_message_text(
                    build_checkers_invite_receiver_text(invite, left, to_id),
                    chat_id=to_id,
                    message_id=to_mid,
                    parse_mode="HTML",
                    reply_markup=checkers_invite_kb(invite_id, to_id),
                )
            except Exception:
                pass
        await asyncio.sleep(1)
    invite = checkers_take_invite(invite_id)
    if not invite:
        return
    from_id = int(invite.get("from_id") or 0)
    to_id = int(invite.get("to_id") or 0)
    from_mid = int(invite.get("from_message_id") or 0)
    to_mid = int(invite.get("to_message_id") or 0)
    try:
        if from_id and from_mid:
            await bot.edit_message_text(
                tr(from_id, "checkers_invite_expired_sender"),
                chat_id=from_id,
                message_id=from_mid,
            )
    except Exception:
        pass
    try:
        if to_id and to_mid:
            await bot.edit_message_text(
                tr(to_id, "checkers_invite_expired_receiver"),
                chat_id=to_id,
                message_id=to_mid,
            )
    except Exception:
        pass


async def create_checkers_invite(from_user: Any, to_user: Dict[str, Any]) -> tuple[bool, str]:
    from_id = int(getattr(from_user, "id", 0) or 0)
    to_id = int(to_user.get("user_id") or 0)
    if not from_id or not to_id:
        return False, "Не удалось определить участников."
    if from_id == to_id:
        return False, "Нельзя отправить вызов самому себе."
    if from_id in mini_games:
        return False, "Сначала завершите текущую игру."
    if to_id in mini_games:
        return False, "Этот пользователь сейчас в игре."
    for inv in list(checkers_invites.values()):
        if inv.get("status") != "pending":
            continue
        a = int(inv.get("from_id") or 0)
        b = int(inv.get("to_id") or 0)
        if {a, b} == {from_id, to_id}:
            return False, "У вас уже есть активное приглашение."

    invite_id = checkers_next_invite_id()
    expires_ts = time.time() + CHECKERS_INVITE_TTL_SEC
    from_username = getattr(from_user, "username", None) or ""
    to_username = to_user.get("username") or ""
    base = {
        "invite_id": invite_id,
        "status": "pending",
        "from_id": from_id,
        "to_id": to_id,
        "from_username": from_username,
        "to_username": to_username,
        "created_ts": time.time(),
        "expires_ts": expires_ts,
    }
    left = int(expires_ts - time.time())

    await send_game_sticker(from_id)
    sender_msg = await send_clean_message(
        from_id,
        build_checkers_invite_sender_text(base, left, from_id),
        parse_mode="HTML",
    )
    from_mid = int(getattr(sender_msg, "message_id", 0) or 0)

    await send_game_sticker(to_id)
    try:
        receiver_msg = await bot.send_message(
            to_id,
            build_checkers_invite_receiver_text(base, left, to_id),
            parse_mode="HTML",
            reply_markup=checkers_invite_kb(invite_id, to_id),
        )
    except Exception:
        return False, "Не смог отправить приглашение. Друг должен активировать бота и открыть диалог."

    checkers_invites[invite_id] = {
        **base,
        "from_message_id": from_mid,
        "to_message_id": int(getattr(receiver_msg, "message_id", 0) or 0),
    }
    checkers_invite_tasks[invite_id] = asyncio.create_task(checkers_invite_timer_loop(invite_id))
    return True, ""


async def send_checkers_game_over(
    user_id: int,
    text: str,
    level: int,
    opponent_id: Optional[int] = None,
) -> None:
    await send_game_sticker(user_id)
    await send_clean_message(
        user_id,
        text,
        parse_mode="HTML",
        reply_markup=build_checkers_end_kb(level, user_id, opponent_id=opponent_id),
    )


def checkers_new_board() -> list[list[str]]:
    # Human plays from bottom to top, AI plays from top to bottom.
    board = [["." for _ in range(8)] for _ in range(8)]
    for row in range(8):
        for col in range(8):
            if (row + col) % 2 == 0:
                continue
            if row <= 2:
                board[row][col] = "b"
            elif row >= 5:
                board[row][col] = "w"
    return board


def checkers_clone_board(board: list[list[str]]) -> list[list[str]]:
    return [row[:] for row in board]


def checkers_in_bounds(row: int, col: int) -> bool:
    return 0 <= row < 8 and 0 <= col < 8


def checkers_piece_side(piece: str) -> str:
    if piece in {"w", "W"}:
        return "human"
    if piece in {"b", "B"}:
        return "ai"
    return ""


def checkers_is_king(piece: str) -> bool:
    return piece in {"W", "B"}


def checkers_opponent(side: str) -> str:
    return "ai" if side == "human" else "human"


def checkers_promote(piece: str, row: int) -> str:
    if piece == "w" and row == 0:
        return "W"
    if piece == "b" and row == 7:
        return "B"
    return piece


def checkers_forward_dirs(side: str) -> list[tuple[int, int]]:
    if side == "human":
        return [(-1, -1), (-1, 1)]
    return [(1, -1), (1, 1)]


def checkers_capture_dirs(piece: str, side: str) -> list[tuple[int, int]]:
    if checkers_is_king(piece):
        return [(-1, -1), (-1, 1), (1, -1), (1, 1)]
    # Men can capture backward too for a more forgiving ruleset.
    return [(-1, -1), (-1, 1), (1, -1), (1, 1)]


def checkers_path_to_text(path: list[tuple[int, int]]) -> str:
    out: list[str] = []
    for row, col in path:
        if not checkers_in_bounds(row, col):
            continue
        out.append(f"{CHECKERS_FILES[col]}{8 - row}")
    return "-".join(out)


def checkers_cell_to_text(cell: tuple[int, int]) -> str:
    row, col = cell
    if not checkers_in_bounds(row, col):
        return ""
    return f"{CHECKERS_FILES[col]}{8 - row}"


def checkers_cells_to_text(cells: set[tuple[int, int]]) -> str:
    ordered = sorted(cells, key=lambda c: (c[0], c[1]))
    values = [checkers_cell_to_text(c) for c in ordered]
    values = [v for v in values if v]
    return ", ".join(values) if values else "—"


def parse_checkers_path(text: str) -> Optional[list[tuple[int, int]]]:
    tokens = re.findall(r"[a-h][1-8]", (text or "").lower())
    if len(tokens) < 2:
        return None
    path: list[tuple[int, int]] = []
    for tok in tokens:
        col = CHECKERS_FILES.find(tok[0])
        if col < 0:
            return None
        row = 8 - int(tok[1])
        if not checkers_in_bounds(row, col):
            return None
        path.append((row, col))
    return path


def checkers_collect_captures(
    board: list[list[str]],
    row: int,
    col: int,
    piece: str,
    path: list[tuple[int, int]],
    captured: list[tuple[int, int]],
    out: list[Dict[str, Any]],
) -> None:
    side = checkers_piece_side(piece)
    if not side:
        return
    found = False
    is_king = checkers_is_king(piece)
    for dr, dc in checkers_capture_dirs(piece, side):
        if is_king:
            enemy_r = row + dr
            enemy_c = col + dc
            # Flying king: skip empty squares before the captured piece.
            while checkers_in_bounds(enemy_r, enemy_c) and board[enemy_r][enemy_c] == ".":
                enemy_r += dr
                enemy_c += dc
            if not checkers_in_bounds(enemy_r, enemy_c):
                continue
            enemy_piece = board[enemy_r][enemy_c]
            if checkers_piece_side(enemy_piece) != checkers_opponent(side):
                continue
            # Any empty square after the captured piece is a legal landing square.
            to_r = enemy_r + dr
            to_c = enemy_c + dc
            while checkers_in_bounds(to_r, to_c) and board[to_r][to_c] == ".":
                found = True
                next_board = checkers_clone_board(board)
                moving_piece = next_board[row][col]
                next_board[row][col] = "."
                next_board[enemy_r][enemy_c] = "."
                next_board[to_r][to_c] = moving_piece

                next_path = path + [(to_r, to_c)]
                next_captured = captured + [(enemy_r, enemy_c)]
                checkers_collect_captures(
                    next_board, to_r, to_c, moving_piece, next_path, next_captured, out
                )
                to_r += dr
                to_c += dc
            continue

        mid_r = row + dr
        mid_c = col + dc
        to_r = row + dr * 2
        to_c = col + dc * 2
        if not checkers_in_bounds(mid_r, mid_c) or not checkers_in_bounds(to_r, to_c):
            continue
        mid_piece = board[mid_r][mid_c]
        if checkers_piece_side(mid_piece) != checkers_opponent(side):
            continue
        if board[to_r][to_c] != ".":
            continue

        found = True
        next_board = checkers_clone_board(board)
        moving_piece = next_board[row][col]
        next_board[row][col] = "."
        next_board[mid_r][mid_c] = "."
        promoted_piece = checkers_promote(moving_piece, to_r)
        next_board[to_r][to_c] = promoted_piece

        next_path = path + [(to_r, to_c)]
        next_captured = captured + [(mid_r, mid_c)]
        promoted = moving_piece != promoted_piece
        if promoted:
            out.append(
                {
                    "path": next_path,
                    "captures": next_captured,
                    "promote": True,
                }
            )
            continue
        checkers_collect_captures(
            next_board, to_r, to_c, promoted_piece, next_path, next_captured, out
        )
    if not found and captured:
        out.append({"path": path, "captures": captured, "promote": False})


def checkers_piece_moves(board: list[list[str]], row: int, col: int) -> list[Dict[str, Any]]:
    piece = board[row][col]
    side = checkers_piece_side(piece)
    if not side:
        return []

    captures: list[Dict[str, Any]] = []
    checkers_collect_captures(board, row, col, piece, [(row, col)], [], captures)
    if captures:
        for move in captures:
            move["capture"] = True
        return captures

    quiet: list[Dict[str, Any]] = []
    if checkers_is_king(piece):
        for dr, dc in [(-1, -1), (-1, 1), (1, -1), (1, 1)]:
            to_r = row + dr
            to_c = col + dc
            while checkers_in_bounds(to_r, to_c) and board[to_r][to_c] == ".":
                quiet.append(
                    {
                        "path": [(row, col), (to_r, to_c)],
                        "captures": [],
                        "capture": False,
                        "promote": False,
                    }
                )
                to_r += dr
                to_c += dc
    else:
        for dr, dc in checkers_forward_dirs(side):
            to_r = row + dr
            to_c = col + dc
            if not checkers_in_bounds(to_r, to_c):
                continue
            if board[to_r][to_c] != ".":
                continue
            promoted_piece = checkers_promote(piece, to_r)
            quiet.append(
                {
                    "path": [(row, col), (to_r, to_c)],
                    "captures": [],
                    "capture": False,
                    "promote": promoted_piece != piece,
                }
            )
    return quiet


def checkers_generate_moves(board: list[list[str]], side: str) -> list[Dict[str, Any]]:
    captures: list[Dict[str, Any]] = []
    quiet: list[Dict[str, Any]] = []
    for row in range(8):
        for col in range(8):
            piece = board[row][col]
            if checkers_piece_side(piece) != side:
                continue
            for move in checkers_piece_moves(board, row, col):
                if move.get("captures"):
                    captures.append(move)
                else:
                    quiet.append(move)
    return captures if captures else quiet


def checkers_apply_move(board: list[list[str]], move: Dict[str, Any]) -> list[list[str]]:
    path = list(move.get("path") or [])
    if len(path) < 2:
        return checkers_clone_board(board)
    next_board = checkers_clone_board(board)
    from_r, from_c = path[0]
    piece = next_board[from_r][from_c]
    next_board[from_r][from_c] = "."
    cur_r, cur_c = from_r, from_c
    for to_r, to_c in path[1:]:
        step_r = 0 if to_r == cur_r else (1 if to_r > cur_r else -1)
        step_c = 0 if to_c == cur_c else (1 if to_c > cur_c else -1)
        scan_r = cur_r + step_r
        scan_c = cur_c + step_c
        captured_cell: Optional[tuple[int, int]] = None
        while checkers_in_bounds(scan_r, scan_c) and (scan_r != to_r or scan_c != to_c):
            if next_board[scan_r][scan_c] != ".":
                captured_cell = (scan_r, scan_c)
                break
            scan_r += step_r
            scan_c += step_c
        if captured_cell is not None:
            cap_r, cap_c = captured_cell
            next_board[cap_r][cap_c] = "."
        cur_r, cur_c = to_r, to_c
    piece = checkers_promote(piece, cur_r)
    next_board[cur_r][cur_c] = piece
    return next_board


def checkers_board_key(board: list[list[str]]) -> str:
    return "".join("".join(row) for row in board)


def checkers_move_order_score(move: Dict[str, Any]) -> int:
    captures = len(move.get("captures") or [])
    promoted = 1 if move.get("promote") else 0
    path_len = len(move.get("path") or [])
    return captures * 100 + promoted * 20 + path_len


def checkers_eval(board: list[list[str]]) -> int:
    score = 0
    for row in range(8):
        for col in range(8):
            piece = board[row][col]
            if piece == "b":
                score += 100 + row * 4
            elif piece == "B":
                score += 185
            elif piece == "w":
                score -= 100 + (7 - row) * 4
            elif piece == "W":
                score -= 185
            else:
                continue
            if 2 <= row <= 5 and 2 <= col <= 5:
                if piece in {"b", "B"}:
                    score += 2
                else:
                    score -= 2
    return score


def checkers_search_score(
    board: list[list[str]],
    depth: int,
    alpha: int,
    beta: int,
    side: str,
    deadline: float,
    cache: Dict[tuple[str, int, str], int],
) -> int:
    if time.time() >= deadline:
        raise TimeoutError("checkers ai timeout")
    key = (checkers_board_key(board), depth, side)
    cached = cache.get(key)
    if cached is not None:
        return cached

    moves = checkers_generate_moves(board, side)
    if not moves:
        value = -100000 - depth if side == "ai" else 100000 + depth
        cache[key] = value
        return value
    if depth <= 0:
        value = checkers_eval(board)
        cache[key] = value
        return value

    ordered = sorted(moves, key=checkers_move_order_score, reverse=True)
    if side == "ai":
        value = -10**9
        for move in ordered:
            child = checkers_apply_move(board, move)
            value = max(
                value,
                checkers_search_score(
                    child, depth - 1, alpha, beta, "human", deadline, cache
                ),
            )
            alpha = max(alpha, value)
            if alpha >= beta:
                break
    else:
        value = 10**9
        for move in ordered:
            child = checkers_apply_move(board, move)
            value = min(
                value,
                checkers_search_score(
                    child, depth - 1, alpha, beta, "ai", deadline, cache
                ),
            )
            beta = min(beta, value)
            if alpha >= beta:
                break
    cache[key] = value
    return value


def choose_checkers_ai_move(board: list[list[str]], level: int) -> Optional[Dict[str, Any]]:
    moves = checkers_generate_moves(board, "ai")
    if not moves:
        return None
    lvl = clamp_checkers_level(level)
    randomness = CHECKERS_LEVEL_RANDOMNESS.get(lvl, 0.0)
    if randomness > 0 and secrets.randbelow(1000) < int(randomness * 1000):
        return secrets.choice(moves)

    depth_target = CHECKERS_LEVEL_DEPTH.get(lvl, 1)
    deadline = time.time() + CHECKERS_LEVEL_TIME_BUDGET.get(lvl, 1.0)
    best_move = secrets.choice(moves)
    root_moves = sorted(moves, key=checkers_move_order_score, reverse=True)

    for depth in range(1, depth_target + 1):
        cache: Dict[tuple[str, int, str], int] = {}
        best_score = -10**9
        candidate = best_move
        try:
            for move in root_moves:
                child = checkers_apply_move(board, move)
                score = checkers_search_score(
                    child,
                    depth - 1,
                    -10**9,
                    10**9,
                    "human",
                    deadline,
                    cache,
                )
                if score > best_score:
                    best_score = score
                    candidate = move
                elif score == best_score and secrets.randbelow(2) == 0:
                    candidate = move
        except TimeoutError:
            break
        best_move = candidate
    return best_move


def start_checkers_game(user_id: int, level: int) -> Dict[str, Any]:
    lvl = clamp_checkers_level(level)
    game = {
        "type": "checkers",
        "board": checkers_new_board(),
        "level": lvl,
        "ui_selected": None,
        "ply_count": 0,
        "max_plies": CHECKERS_MAX_PLIES,
        "started_ts": int(time.time()),
    }
    mini_games[user_id] = game
    stats = init_game_stats(user_id)
    stats["checkers_games"] = int(stats.get("checkers_games", 0)) + 1
    return game


def checkers_render_board(board: list[list[str]]) -> str:
    symbols = {
        "w": "x",
        "W": "X",
        "b": "o",
        "B": "O",
    }
    lines = ["   a b c d e f g h"]
    for row in range(8):
        rank = 8 - row
        cells: list[str] = []
        for col in range(8):
            piece = board[row][col]
            if piece in symbols:
                cells.append(symbols[piece])
            else:
                cells.append("·" if (row + col) % 2 else ".")
        lines.append(f"{rank}  " + " ".join(cells))
    lines.append("   a b c d e f g h")
    return "\n".join(lines)


def checkers_human_context(
    game: Dict[str, Any]
) -> tuple[list[Dict[str, Any]], Optional[tuple[int, int]], set[tuple[int, int]], set[tuple[int, int]]]:
    board = game.get("board")
    if not isinstance(board, list):
        return [], None, set(), set()
    legal_moves = checkers_generate_moves(board, "human")
    selectable = {
        tuple(path[0])
        for move in legal_moves
        for path in [list(move.get("path") or [])]
        if len(path) >= 2
    }
    raw_sel = game.get("ui_selected")
    selected: Optional[tuple[int, int]] = None
    if isinstance(raw_sel, (list, tuple)) and len(raw_sel) == 2:
        try:
            candidate = (int(raw_sel[0]), int(raw_sel[1]))
            if candidate in selectable:
                selected = candidate
        except Exception:
            selected = None
    if selected is None:
        game["ui_selected"] = None
    targets: set[tuple[int, int]] = set()
    if selected is not None:
        for move in legal_moves:
            path = list(move.get("path") or [])
            if len(path) >= 2 and tuple(path[0]) == selected:
                targets.add(tuple(path[1]))
    return legal_moves, selected, selectable, targets


def build_checkers_board_kb(user_id: int, game: Dict[str, Any]) -> InlineKeyboardMarkup:
    board = game.get("board")
    if not isinstance(board, list):
        return InlineKeyboardMarkup(
            inline_keyboard=[
                [InlineKeyboardButton(text="↩️ Назад", callback_data="menu_games")]
            ]
        )
    _, selected, _, targets = checkers_human_context(game)
    rows: list[list[InlineKeyboardButton]] = []
    for row in range(8):
        row_btns: list[InlineKeyboardButton] = []
        for col in range(8):
            dark = (row + col) % 2 == 1
            if not dark:
                row_btns.append(
                    InlineKeyboardButton(text=CHECKERS_BLANK, callback_data="checkers_noop")
                )
                continue
            piece = board[row][col]
            if piece in {"w", "W"}:
                text = "⚪"
            elif piece in {"b", "B"}:
                text = "⚫"
            elif (row, col) in targets:
                text = "🟩"
            else:
                text = CHECKERS_BLANK
            if selected is not None and (row, col) == selected and piece in {"w", "W"}:
                text = "🟢"
            row_btns.append(
                InlineKeyboardButton(
                    text=text,
                    callback_data=f"checkers_cell:{row}:{col}",
                )
            )
        rows.append(row_btns)
    rows.append(
        [
            InlineKeyboardButton(text="🔄", callback_data="checkers_refresh"),
            InlineKeyboardButton(text="🏳️ Сдаться", callback_data="checkers_resign"),
            InlineKeyboardButton(text="↩️ Назад", callback_data="menu_games"),
        ]
    )
    return InlineKeyboardMarkup(inline_keyboard=rows)


def build_checkers_state_text(
    user_id: int,
    game: Dict[str, Any],
    extra: str = "",
    include_turn_prompt: bool = True,
) -> str:
    level = clamp_checkers_level(game.get("level"))
    _, selected, _, targets = checkers_human_context(game)
    lines = [
        tr(
            user_id,
            "game_checkers_level_set",
            level=level,
            label=checkers_level_label(user_id, level),
        )
    ]
    if extra:
        lines.append(extra)
    lines.append(tr(user_id, "game_checkers_legend"))
    if selected is not None:
        lines.append(
            tr(
                user_id,
                "game_checkers_selected",
                cell=h(checkers_cell_to_text(selected) or "—"),
            )
        )
    if targets:
        lines.append(
            tr(
                user_id,
                "game_checkers_targets",
                cells=h(checkers_cells_to_text(targets)),
            )
        )
    if include_turn_prompt:
        lines.append(tr(user_id, "game_checkers_turn"))
    return "\n\n".join(lines)


def checkers_legal_moves_preview(moves: list[Dict[str, Any]], limit: int = 6) -> str:
    text = [checkers_path_to_text(list(m.get("path") or [])) for m in moves[:limit]]
    return ", ".join([t for t in text if t]) or "—"


def checkers_find_user_move(
    legal_moves: list[Dict[str, Any]], user_path: list[tuple[int, int]]
) -> Optional[Dict[str, Any]]:
    for move in legal_moves:
        if list(move.get("path") or []) == user_path:
            return move
    # Convenience fallback: allow "start-firstjump" when only one full sequence matches.
    if len(user_path) == 2:
        pref = []
        for move in legal_moves:
            path = list(move.get("path") or [])
            if len(path) >= 2 and path[0] == user_path[0] and path[1] == user_path[1]:
                pref.append(move)
        if len(pref) == 1:
            return pref[0]
    return None


async def send_checkers_board(
    chat_id: int,
    user_id: int,
    game: Dict[str, Any],
    extra: str = "",
) -> None:
    await send_clean_message(
        chat_id,
        build_checkers_state_text(user_id, game, extra=extra),
        parse_mode="HTML",
        reply_markup=build_checkers_board_kb(user_id, game),
    )


async def process_checkers_user_path(
    chat_id: int,
    user_id: int,
    game: Dict[str, Any],
    user_path: Optional[list[tuple[int, int]]],
) -> None:
    board = game.get("board")
    if not isinstance(board, list):
        mini_games.pop(user_id, None)
        await send_clean_message(chat_id, "Ошибка игры. Запустите заново.")
        return

    legal_human_moves = checkers_generate_moves(board, "human")
    if not legal_human_moves:
        mini_games.pop(user_id, None)
        await send_clean_message(
            chat_id,
            tr(user_id, "game_checkers_lose") + "\n\n"
            f"<pre>{h(checkers_render_board(board))}</pre>",
            parse_mode="HTML",
        )
        return

    user_move: Optional[Dict[str, Any]] = None
    if user_path:
        user_move = checkers_find_user_move(legal_human_moves, user_path)
    if not user_move:
        game["ui_selected"] = None
        await send_checkers_board(
            chat_id,
            user_id,
            game,
            extra=(
                f"{tr(user_id, 'game_checkers_bad_move')}\n\n"
                f"<code>{h(checkers_legal_moves_preview(legal_human_moves))}</code>"
            ),
        )
        return

    game["ui_selected"] = None
    board = checkers_apply_move(board, user_move)
    game["board"] = board
    game["ply_count"] = int(game.get("ply_count", 0)) + 1
    if int(game.get("ply_count", 0)) >= int(game.get("max_plies", CHECKERS_MAX_PLIES)):
        mini_games.pop(user_id, None)
        await send_clean_message(
            chat_id,
            tr(user_id, "game_checkers_draw") + "\n\n"
            f"<pre>{h(checkers_render_board(board))}</pre>",
            parse_mode="HTML",
        )
        return

    ai_move = await asyncio.to_thread(
        choose_checkers_ai_move,
        board,
        clamp_checkers_level(game.get("level")),
    )
    if not ai_move:
        stats = init_game_stats(user_id)
        stats["checkers_wins"] = int(stats.get("checkers_wins", 0)) + 1
        mini_games.pop(user_id, None)
        await send_clean_message(
            chat_id,
            tr(user_id, "game_checkers_win") + "\n\n"
            f"<pre>{h(checkers_render_board(board))}</pre>",
            parse_mode="HTML",
        )
        return

    board = checkers_apply_move(board, ai_move)
    game["board"] = board
    game["ply_count"] = int(game.get("ply_count", 0)) + 1
    if int(game.get("ply_count", 0)) >= int(game.get("max_plies", CHECKERS_MAX_PLIES)):
        mini_games.pop(user_id, None)
        await send_clean_message(
            chat_id,
            tr(user_id, "game_checkers_draw") + "\n\n"
            f"<pre>{h(checkers_render_board(board))}</pre>",
            parse_mode="HTML",
        )
        return

    if not checkers_generate_moves(board, "human"):
        mini_games.pop(user_id, None)
        await send_clean_message(
            chat_id,
            tr(user_id, "game_checkers_lose") + "\n\n"
            f"<pre>{h(checkers_render_board(board))}</pre>",
            parse_mode="HTML",
        )
        return

    ai_move_text = checkers_path_to_text(list(ai_move.get("path") or []))
    await send_checkers_board(
        chat_id,
        user_id,
        game,
        extra=f"🤖 <code>{h(ai_move_text)}</code>",
    )


def detect_voice_intent(text: str) -> str:
    t = normalize_game_text(text)
    if any(k in t for k in ("каталог", "catalog", "товар")):
        return "catalog"
    if any(k in t for k in ("корзин", "cart")):
        return "cart"
    if any(k in t for k in ("профил", "profile", "баланс")):
        return "profile"
    if any(k in t for k in ("шашк", "checkers", "дойбы")):
        return "games"
    if any(k in t for k in ("игр", "games", "ойын")):
        return "games"
    return ""


def transcribe_voice_ogg_bytes(data: bytes, language_code: str) -> tuple[Optional[str], str]:
    if not data:
        return None, "empty"
    try:
        import speech_recognition as sr  # type: ignore
        from pydub import AudioSegment  # type: ignore
    except Exception:
        return None, "dep_missing"

    ogg_path = None
    wav_path = None
    try:
        with tempfile.NamedTemporaryFile(delete=False, suffix=".ogg") as ogg_file:
            ogg_file.write(data)
            ogg_path = ogg_file.name
        with tempfile.NamedTemporaryFile(delete=False, suffix=".wav") as wav_file:
            wav_path = wav_file.name
        segment = AudioSegment.from_file(ogg_path)
        segment.export(wav_path, format="wav")

        recognizer = sr.Recognizer()
        with sr.AudioFile(wav_path) as source:
            audio = recognizer.record(source)
        try:
            text = recognizer.recognize_google(audio, language=language_code)
            return (text or "").strip(), ""
        except sr.UnknownValueError:
            return "", ""
        except Exception:
            return None, "recognize_error"
    except Exception:
        return None, "convert_error"
    finally:
        for path in (ogg_path, wav_path):
            if not path:
                continue
            try:
                os.remove(path)
            except Exception:
                pass


async def transcribe_voice_message(message: Message, language_code: str) -> tuple[Optional[str], str]:
    if not message.voice:
        return None, "no_voice"
    data = await download_telegram_file_bytes(message.voice.file_id)
    if not data:
        return None, "download_error"
    return await asyncio.to_thread(transcribe_voice_ogg_bytes, data, language_code)


def normalize_image_name(name: str) -> str:
    n = name.strip().lower()
    for ch in [" ", "-", "&", "'", '"']:
        n = n.replace(ch, "_")
    while "__" in n:
        n = n.replace("__", "_")
    return n


def resolve_image_path(image_name: Optional[str]) -> Optional[str]:
    if not image_name:
        return None
    direct = os.path.join(IMAGES_DIR, image_name)
    if os.path.exists(direct):
        return direct
    try:
        files = [
            f
            for f in os.listdir(IMAGES_DIR)
            if os.path.isfile(os.path.join(IMAGES_DIR, f))
        ]
    except Exception:
        return None
    img_lower = image_name.lower()
    for f in files:
        if f.lower() == img_lower:
            return os.path.join(IMAGES_DIR, f)
    img_norm = normalize_image_name(image_name)
    for f in files:
        if normalize_image_name(f) == img_norm:
            return os.path.join(IMAGES_DIR, f)
    return None


def safe_key(name: str) -> str:
    s = name.replace("-", "_").replace(" ", "_").replace("&", "_").replace("'", "_")
    while "__" in s:
        s = s.replace("__", "_")
    return s


def find_key_by_safe(inv: Dict[str, Any], safe: str) -> Optional[str]:
    for k in inv:
        if safe_key(k) == safe:
            return k
    return None


def load_inventory() -> Dict[str, Any]:
    global _inventory_cache, _inventory_mtime
    with _inventory_lock:
        try:
            mtime = os.path.getmtime(INVENTORY_FILE)
        except FileNotFoundError:
            _inventory_cache = {}
            _inventory_mtime = 0.0
            return _inventory_cache

        if mtime != _inventory_mtime:
            with open(INVENTORY_FILE, "r", encoding="utf-8") as f:
                _inventory_cache = json.load(f)
            _inventory_mtime = mtime
        return _inventory_cache


def save_inventory(inv: Dict[str, Any]) -> None:
    global _inventory_cache, _inventory_mtime
    with _inventory_lock:
        dirn = os.path.dirname(os.path.abspath(INVENTORY_FILE)) or "."
        fd, tmp = tempfile.mkstemp(dir=dirn, prefix="inventory_", suffix=".tmp")
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(inv, f, ensure_ascii=False, indent=2)
            os.replace(tmp, INVENTORY_FILE)
            _inventory_cache = inv
            _inventory_mtime = os.path.getmtime(INVENTORY_FILE)
        finally:
            if os.path.exists(tmp):
                try:
                    os.remove(tmp)
                except Exception:
                    pass


def get_banned() -> list:
    with _banned_lock:
        try:
            conn = get_db_conn()
            try:
                with conn.cursor() as cur:
                    cur.execute("SELECT user_id FROM banned")
                    rows = cur.fetchall()
                return [int(r["user_id"]) for r in rows]
            finally:
                conn.close()
        except Exception:
            return []


def ban_user(uid: int, reason: str = "бан", actor_id: Optional[int] = None) -> None:
    with _banned_lock:
        try:
            conn = get_db_conn()
            try:
                with conn.cursor() as cur:
                    cur.execute(
                        """
                        INSERT INTO banned (user_id, reason, created_ts, actor_id)
                        VALUES (%s, %s, %s, %s)
                        ON CONFLICT (user_id) DO UPDATE SET
                            reason = EXCLUDED.reason,
                            created_ts = EXCLUDED.created_ts,
                            actor_id = EXCLUDED.actor_id
                        """,
                        (uid, reason, int(time.time()), actor_id),
                    )
                conn.commit()
            finally:
                conn.close()
        except Exception:
            pass


def unban_user(uid: int) -> None:
    with _banned_lock:
        try:
            conn = get_db_conn()
            try:
                with conn.cursor() as cur:
                    cur.execute("DELETE FROM banned WHERE user_id = %s", (uid,))
                conn.commit()
            finally:
                conn.close()
        except Exception:
            pass


def apply_order_stock(order: Dict[str, Any]) -> tuple[bool, str]:
    items = order.get("items") or []
    if not items:
        return False, "пустой заказ"
    with _inventory_lock:
        try:
            with open(INVENTORY_FILE, "r", encoding="utf-8") as f:
                inv = json.load(f)
        except FileNotFoundError:
            return False, "inventory.json не найден"
        to_apply = []
        for it in items:
            if not isinstance(it, dict):
                return False, "неверный формат товаров"
            key = it.get("key")
            if not key:
                key = find_key_by_safe(inv, safe_key(it.get("name", ""))) if it.get("name") else None
            if not key or key not in inv:
                return False, f"товар не найден: {it.get('name') or it.get('key')}"
            qty = int(it.get("qty") or it.get("count") or 0)
            if qty <= 0:
                return False, "неверное количество"
            stock = int(inv.get(key, {}).get("stock", 0))
            if stock < qty:
                return False, f"не хватает стока: {inv.get(key, {}).get('name', key)}"
            to_apply.append((key, qty))

        for key, qty in to_apply:
            inv[key]["stock"] = max(0, int(inv[key].get("stock", 0)) - qty)

        save_inventory(inv)
        return True, ""


def get_reserved_for_key(key: str, exclude_user_id: Optional[int] = None) -> int:
    now = time.time()
    total = 0
    for uid, res in list(reservations.items()):
        if exclude_user_id is not None and uid == exclude_user_id:
            continue
        if res.get("expires_ts", 0) <= now:
            continue
        total += int(res.get("items", {}).get(key, 0))
    return total


def available_stock(inv: Dict[str, Any], key: str, exclude_user_id: Optional[int] = None) -> int:
    stock = int(inv.get(key, {}).get("stock", 0))
    reserved = get_reserved_for_key(key, exclude_user_id=exclude_user_id)
    return max(0, stock - reserved)


def cancel_reservation(user_id: int, completed: bool = False) -> set[str]:
    res = reservations.pop(user_id, None)
    task = reservation_tasks.pop(user_id, None)
    if task and not task.done():
        task.cancel()
    if not res:
        return set()
    res["completed"] = bool(completed)
    return set(res.get("items", {}).keys())


def mark_reservation_completed(user_id: int) -> None:
    res = reservations.get(user_id)
    if res:
        res["completed"] = True


async def warn_no_purchase(user_id: int) -> None:
    count = int(reservation_warnings.get(user_id, 0)) + 1
    reservation_warnings[user_id] = count
    if count >= RESERVATION_WARN_LIMIT:
        ban_user(user_id, "неоплаченный резерв", None)
        record_ban_history(user_id, "неоплаченный резерв", None)
        user_cart.pop(user_id, None)
        user_states.pop(user_id, None)
        review_pending.pop(user_id, None)
        try:
            await send_clean_message(
                user_id,
                "Вы получили 3 предупреждения за неоплаченные резервы и заблокированы.",
                parse_mode="HTML",
            )
        except Exception:
            pass
        return
    try:
        await send_clean_message(
            user_id,
            f"Предупреждение {count}/{RESERVATION_WARN_LIMIT}: "
            "вы не завершили заказ за 10 минут. Не задерживайте резерв.",
            parse_mode="HTML",
        )
    except Exception:
        pass


async def reservation_timeout_loop(user_id: int) -> None:
    while True:
        res = reservations.get(user_id)
        if not res:
            return
        delay = float(res.get("expires_ts", 0)) - time.time()
        if delay > 0:
            await asyncio.sleep(delay)
        res = reservations.get(user_id)
        if not res:
            return
        if float(res.get("expires_ts", 0)) > time.time():
            continue
        items = res.get("items", {})
        completed = bool(res.get("completed"))
        reservations.pop(user_id, None)
        reservation_tasks.pop(user_id, None)
        if items:
            await broadcast_inventory_update(set(items.keys()))
        if not completed:
            if res.get("paid_with") == "balance":
                amount_cents = int(res.get("amount_cents") or 0)
                if amount_cents > 0:
                    new_balance = await run_blocking(add_user_balance, user_id, amount_cents)
                    try:
                        bal_text = format_money(int(new_balance or 0))
                        await send_clean_message(
                            user_id,
                            f"Резерв истёк. Сумма возвращена на баланс.\nВаш баланс: {bal_text}₸",
                            parse_mode="HTML",
                        )
                    except Exception:
                        pass
            user_states.pop(user_id, None)
            user_cart.pop(user_id, None)
            await warn_no_purchase(user_id)
        return


def start_reservation_timer(user_id: int) -> None:
    task = reservation_tasks.get(user_id)
    if task and not task.done():
        task.cancel()
    reservation_tasks[user_id] = asyncio.create_task(reservation_timeout_loop(user_id))


def reserve_cart_for_user(
    user_id: int, cart: Dict[str, int], inv: Dict[str, Any]
) -> tuple[bool, str, set[str]]:
    if not cart:
        return False, "корзина пуста", set()
    items: Dict[str, int] = {}
    for k, q in cart.items():
        if k not in inv:
            return False, "товар не найден", set()
        qty = int(q)
        if qty <= 0:
            return False, "неверное количество", set()
        avail = available_stock(inv, k, exclude_user_id=user_id)
        if qty > avail:
            return False, "недостаточно стока", set()
        items[k] = qty
    reservations[user_id] = {
        "items": items,
        "expires_ts": time.time() + RESERVATION_TTL_SEC,
        "completed": False,
    }
    start_reservation_timer(user_id)
    return True, "", set(items.keys())


def stop_pending_reminder(order_id: str) -> None:
    task = order_reminder_tasks.pop(order_id, None)
    if task and not task.done():
        task.cancel()


async def pending_reminder_loop(order_id: str) -> None:
    while True:
        await asyncio.sleep(600)
        state = order_states.get(order_id)
        if not state or state.get("status") != "pending":
            break
        try:
            msg = await bot.send_message(
                state.get("admin_chat_id", OWNER_CHAT_ID),
                f"⏳ Напоминание: заказ <code>{order_id}</code> всё ещё в ожидании.",
                parse_mode="HTML",
            )
            ids = state.setdefault("reminder_message_ids", [])
            ids.append(msg.message_id)
        except Exception:
            pass


def start_pending_reminder(order_id: str) -> None:
    stop_pending_reminder(order_id)
    order_reminder_tasks[order_id] = asyncio.create_task(pending_reminder_loop(order_id))


async def delete_order_reminders(order_id: str) -> None:
    state = order_states.get(order_id)
    if not state:
        return
    ids = list(state.get("reminder_message_ids") or [])
    if not ids:
        return
    admin_chat_id = state.get("admin_chat_id", OWNER_CHAT_ID)
    for mid in ids:
        try:
            await bot.delete_message(admin_chat_id, mid)
        except Exception:
            pass
    state["reminder_message_ids"] = []


def get_order_lock(order_id: str) -> asyncio.Lock:
    lock = order_locks.get(order_id)
    if not lock:
        lock = asyncio.Lock()
        order_locks[order_id] = lock
    return lock


def extract_order_keys(order: Dict[str, Any], inv: Optional[Dict[str, Any]] = None) -> set[str]:
    keys: set[str] = set()
    for it in order.get("items") or []:
        if not isinstance(it, dict):
            continue
        key = it.get("key")
        if not key and inv and it.get("name"):
            key = find_key_by_safe(inv, safe_key(it.get("name", "")))
        if key:
            keys.add(key)
    return keys


def normalize_cart_by_stock(
    cart: Dict[str, int], inv: Dict[str, Any], user_id: Optional[int] = None
) -> tuple[bool, bool]:
    changed = False
    removed = False
    for k, q in list(cart.items()):
        item = inv.get(k)
        if not item:
            del cart[k]
            changed = True
            removed = True
            continue
        stock = available_stock(inv, k, exclude_user_id=user_id)
        if stock <= 0:
            del cart[k]
            changed = True
            removed = True
            continue
        if q > stock:
            cart[k] = stock
            changed = True
            removed = True
        if cart.get(k, 0) <= 0:
            cart.pop(k, None)
            changed = True
            removed = True
    return changed, removed


def build_cart_text_and_kb(cart: Dict[str, int], inv: Dict[str, Any]) -> tuple[str, InlineKeyboardMarkup]:
    total = 0
    lines = ["<b>Твоя корзина</b>", ""]
    kb_rows = []
    for k, q in list(cart.items()):
        item = inv.get(k)
        if not item:
            continue
        line_price = int(item.get("price", 0)) * q
        total += line_price
        name = h(item.get("name", ""))
        emoji_id = emoji_id_for_item(k, item)
        emoji = emoji_html(emoji_id)
        if emoji:
            name = f"{emoji} {name}"
        lines.append(f"• {name} × {q} = <b>{line_price}₸</b>")
        safe = safe_key(k)
        kb_rows.append(
            [
                InlineKeyboardButton(text="➕ Добавить", callback_data="catalog"),
                InlineKeyboardButton(text="❌", callback_data=f"del_{safe}"),
            ]
        )

    lines.append(f"\n<b>Итого: {total}₸</b>")
    kb_rows.append(
        [
            InlineKeyboardButton(text="💳 Оформить", callback_data="checkout"),
            InlineKeyboardButton(text="🧹 Очистить", callback_data="clear"),
        ]
    )
    kb_rows.append([InlineKeyboardButton(text="🛒 Каталог", callback_data="catalog")])
    return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=kb_rows)


async def update_cart_message(user_id: int, message_id: int, inv: Dict[str, Any]) -> None:
    cart = user_cart.get(user_id, {})
    if not cart:
        try:
            await bot.edit_message_text(
                "Корзина пуста!", chat_id=user_id, message_id=message_id
            )
            set_active_view(user_id, message_id, "cart")
        except Exception:
            active_views.pop(user_id, None)
            pass
        return
    text, kb = build_cart_text_and_kb(cart, inv)
    try:
        await bot.edit_message_text(
            text, chat_id=user_id, message_id=message_id, reply_markup=kb, parse_mode="HTML"
        )
        set_active_view(user_id, message_id, "cart")
    except Exception:
        active_views.pop(user_id, None)
        pass


async def update_item_message(
    user_id: int, view: Dict[str, Any], key: str, item: Dict[str, Any], inv: Dict[str, Any]
) -> None:
    safe = safe_key(key)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="➕ В корзину", callback_data=f"add_{safe}")],
            [
                InlineKeyboardButton(text="📦 Корзина", callback_data="cart"),
                InlineKeyboardButton(text="🛒 Каталог", callback_data="catalog"),
            ],
        ]
    )
    name = h(item.get("name", ""))
    emoji_id = emoji_id_for_item(key, item)
    emoji = emoji_html(emoji_id)
    if emoji:
        name = f"{name} {emoji}"
    price = int(item.get("price", 0))
    stock = available_stock(inv, key, exclude_user_id=user_id)
    message_id = view.get("message_id")
    if not message_id:
        return
    try:
        if view.get("kind") == "photo":
            caption = (
                f"<b>{name}</b>\n\n"
                f"<b>Цена:</b> {price}₸\n"
                f"<b>В наличии:</b> {stock}"
            )
            await bot.edit_message_caption(
                chat_id=user_id,
                message_id=message_id,
                caption=caption,
                reply_markup=kb,
                parse_mode="HTML",
            )
        else:
            await bot.edit_message_text(
                f"<b>{name}</b>\n\n<b>Цена:</b> {price}₸",
                chat_id=user_id,
                message_id=message_id,
                reply_markup=kb,
                parse_mode="HTML",
            )
        set_active_view(user_id, message_id, "item", view_key=key, view_kind=view.get("kind"))
    except Exception:
        active_views.pop(user_id, None)
        pass


async def broadcast_inventory_update(changed_keys: set[str]) -> None:
    if not changed_keys:
        return
    inv = load_inventory()
    updated_users: set[int] = set()
    update_count = 0

    async def throttle_updates(count: int) -> int:
        count += 1
        if count % 10 == 0:
            await asyncio.sleep(0.5)
        elif count % 3 == 0:
            await asyncio.sleep(0.1)
        return count

    # Обновляем корзины пользователей
    for uid, cart in list(user_cart.items()):
        if not cart or not any(k in changed_keys for k in cart):
            continue
        changed, removed = normalize_cart_by_stock(cart, inv, uid)
        if not cart:
            user_cart.pop(uid, None)
        if changed:
            view = active_views.get(uid)
            if view and view.get("type") == "cart" and uid not in updated_users:
                if cart:
                    await update_cart_message(uid, view.get("message_id"), inv)
                else:
                    await show_inventory(uid, uid, header="⚠️ Товар закончился. Выберите другие товары.")
                updated_users.add(uid)
                update_count = await throttle_updates(update_count)

    # Обновляем активные FSM с корзиной (отменяем, если товар пропал)
    for uid, st in list(user_states.items()):
        cart = st.get("cart")
        if not isinstance(cart, dict) or not cart:
            continue
        if not any(k in changed_keys for k in cart):
            continue
        _, removed = normalize_cart_by_stock(cart, inv, uid)
        if removed:
            user_states.pop(uid, None)
            if uid not in updated_users:
                await show_inventory(uid, uid, header="⚠️ Товар закончился. Выберите другие товары.")
                updated_users.add(uid)
                update_count = await throttle_updates(update_count)
        else:
            total = 0
            for k, q in cart.items():
                total += int(inv.get(k, {}).get("price", 0)) * q
            st["total"] = total

    # Обновляем открытые каталоги и карточки товаров
    for uid, view in list(active_views.items()):
        if uid < 0:
            continue
        if uid in updated_users:
            continue
        vtype = view.get("type")
        if vtype == "catalog":
            try:
                await show_inventory(uid, uid)
                updated_users.add(uid)
                update_count = await throttle_updates(update_count)
            except Exception:
                pass
        elif vtype == "item":
            key = view.get("item_key")
            if not key or key not in changed_keys:
                continue
            item = inv.get(key)
            stock = available_stock(inv, key, exclude_user_id=uid) if item else 0
            try:
                if not item or stock <= 0:
                    await show_inventory(uid, uid, header="⚠️ Товар закончился. Выберите другие товары.")
                else:
                    await update_item_message(uid, view, key, item, inv)
                updated_users.add(uid)
                update_count = await throttle_updates(update_count)
            except Exception:
                pass

def format_datetime_from_message_date(msg_date) -> str:
    try:
        if isinstance(msg_date, (int, float)):
            dt = datetime.fromtimestamp(msg_date)
        else:
            dt = msg_date
        return dt.strftime("%H:%M • %d.%m.%Y")
    except Exception:
        return str(msg_date)


async def show_inventory(
    chat_id: int, user_id: Optional[int] = None, header: Optional[str] = None
) -> None:
    kb_rows = []
    inv = load_inventory()
    has = False
    uid = user_id or chat_id
    cart = user_cart.get(uid, {})
    for k, v in inv.items():
        try:
            stock = available_stock(inv, k, exclude_user_id=uid)
        except Exception:
            stock = 0
        if stock > 0:
            has = True
            cnt = cart.get(k, 0)
            name = v.get("name", k)
            text = f"{name} — {int(v.get('price', 0))}₸"
            if cnt:
                text += f" ({cnt})"
            emoji_id = emoji_id_for_item(k, v)
            btn_kwargs = {"text": text, "callback_data": f"view_{safe_key(k)}"}
            if emoji_id:
                btn_kwargs["icon_custom_emoji_id"] = emoji_id
            kb_rows.append([InlineKeyboardButton(**btn_kwargs)])
    kb_rows.append([InlineKeyboardButton(text="📦 Корзина", callback_data="cart")])
    kb_rows.append([InlineKeyboardButton(text="👤 Профиль", callback_data="profile")])
    kb_rows.append([InlineKeyboardButton(text="⚡ Возможности", callback_data="menu_power")])
    kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)
    try:
        base = (
            "🛍 <b>Каталог</b>\nВыберите товар ниже:"
            if has
            else "🛍 <b>Каталог</b>\nСкоро довезу!"
        )
        text = f"{header}\n\n{base}" if header else base
        await send_clean_message(
            chat_id, text, reply_markup=kb, parse_mode="HTML", _view_type="catalog"
        )
    except Exception as e:
        await bot.send_message(
            OWNER_CHAT_ID,
            f"Ошибка отправки списка товаров пользователю {chat_id}: {e}",
        )


async def send_item_view(call: CallbackQuery, answer: bool = True) -> None:
    if not call.from_user:
        return
    uid = call.from_user.id
    safe = call.data.split("_", 1)[1]
    inv = load_inventory()
    key = find_key_by_safe(inv, safe)
    if not key:
        if answer:
            await call.answer("Товар не найден", show_alert=True)
        else:
            await call.message.answer("Товар не найден")
        return
    item = inv[key]
    try:
        if available_stock(inv, key, exclude_user_id=uid) <= 0:
            if answer:
                await call.answer("Нет в наличии", show_alert=True)
            else:
                await call.message.answer("Нет в наличии")
            return
    except Exception:
        if answer:
            await call.answer("Ошибка данных товара", show_alert=True)
        else:
            await call.message.answer("Ошибка данных товара")
        return

    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="➕ В корзину", callback_data=f"add_{safe}")],
            [
                InlineKeyboardButton(text="📦 Корзина", callback_data="cart"),
                InlineKeyboardButton(text="🛒 Каталог", callback_data="catalog"),
            ],
        ]
    )

    name = h(item.get("name", ""))
    emoji_id = emoji_id_for_item(key, item)
    emoji = emoji_html(emoji_id)
    if emoji:
        name = f"{name} {emoji}"
    price = int(item.get("price", 0))
    stock = available_stock(inv, key, exclude_user_id=uid)

    image_name = item.get("image")
    image_path = resolve_image_path(image_name)
    if image_name and not image_path:
        try:
            await bot.send_message(
                OWNER_CHAT_ID, f"⚠️ Файл изображения не найден: {image_name}"
            )
        except Exception:
            pass
    if image_path:
        try:
            await send_clean_photo(
                call.message.chat.id,
                FSInputFile(image_path),
                caption=(
                    f"<b>{name}</b>\n\n"
                    f"<b>Цена:</b> {price}₸\n"
                    f"<b>В наличии:</b> {stock}"
                ),
                reply_markup=kb,
                parse_mode="HTML",
                _view_type="item",
                _view_key=key,
                _view_kind="photo",
            )
            if answer:
                await call.answer()
            return
        except Exception as e:
            try:
                await bot.send_message(
                    OWNER_CHAT_ID, f"⚠️ Не смог отправить фото {image_name}: {e}"
                )
            except Exception:
                pass

    await send_clean_message(
        call.message.chat.id,
        f"<b>{name}</b>\n\n<b>Цена:</b> {price}₸",
        reply_markup=kb,
        parse_mode="HTML",
        _view_type="item",
        _view_key=key,
        _view_kind="text",
    )
    if answer:
        await call.answer()


async def render_cart(call: CallbackQuery, answer: bool = True) -> None:
    cart = user_cart.get(call.from_user.id, {})
    if not cart:
        if answer:
            await call.answer("Корзина пуста!", show_alert=True)
        else:
            await send_clean_message(
                call.message.chat.id, "Корзина пуста!", _view_type="cart"
            )
        return

    inv = load_inventory()
    normalize_cart_by_stock(cart, inv, call.from_user.id)
    if not cart:
        if answer:
            await call.answer("Корзина пуста!", show_alert=True)
        else:
            await send_clean_message(
                call.message.chat.id, "Корзина пуста!", _view_type="cart"
            )
        return
    total = 0
    lines = ["<b>Твоя корзина</b>", ""]
    kb_rows = []

    for k, q in list(cart.items()):
        item = inv.get(k)
        if not item:
            del cart[k]
            continue
        line_price = int(item.get("price", 0)) * q
        total += line_price
        name = h(item.get("name", ""))
        emoji_id = emoji_id_for_item(k, item)
        emoji = emoji_html(emoji_id)
        if emoji:
            name = f"{emoji} {name}"
        lines.append(f"• {name} × {q} = <b>{line_price}₸</b>")
        safe = safe_key(k)
        kb_rows.append(
            [
                InlineKeyboardButton(text="➕ Добавить", callback_data="catalog"),
                InlineKeyboardButton(text="❌", callback_data=f"del_{safe}"),
            ]
        )

    lines.append(f"\n<b>Итого: {total}₸</b>")
    kb_rows.append(
        [
            InlineKeyboardButton(text="💳 Оформить", callback_data="checkout"),
            InlineKeyboardButton(text="🧹 Очистить", callback_data="clear"),
        ]
    )
    kb_rows.append([InlineKeyboardButton(text="🛒 Каталог", callback_data="catalog")])

    kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)
    text = "\n".join(lines)
    try:
        await call.message.edit_text(text, reply_markup=kb, parse_mode="HTML")
        if should_cleanup(call.message.chat.id):
            user_last_bot_message[call.message.chat.id] = {
                "id": call.message.message_id,
                "type": "text",
            }
        set_active_view(call.message.chat.id, call.message.message_id, "cart")
    except Exception:
        await send_clean_message(
            call.message.chat.id,
            text,
            reply_markup=kb,
            parse_mode="HTML",
            _view_type="cart",
        )
    if answer:
        await call.answer()


# -------------------- Групповой чат --------------------

@dp.message(F.new_chat_members)
async def greet_new_members(message: Message):
    if not is_group_chat(message.chat):
        return
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(
                    text="💬 Написать боту",
                    url=f"https://t.me/{ORDER_BOT_USERNAME}",
                )
            ]
        ]
    )
    for member in message.new_chat_members:
        if member.is_bot:
            continue
        name = h(member.first_name or member.full_name or "друг")
        text = (
            f"Привет, {name}! 👋\n"
            "Рады видеть тебя в нашем уютном чате 🌿\n"
            f"Чтобы оформить заказ — напиши боту в ЛС: @{ORDER_BOT_USERNAME}"
        )
        try:
            await message.answer(text, reply_markup=kb, parse_mode="HTML")
        except Exception:
            pass


@dp.message(F.chat.type.in_(["group", "supergroup"]))
async def moderate_group(message: Message):
    if not message.from_user or message.from_user.is_bot:
        return
    if message.from_user.id == OWNER_CHAT_ID:
        return

    text = (message.text or message.caption or "").strip()
    if not text:
        return

    if contains_link(text) or contains_banned_words(text):
        try:
            await message.delete()
        except Exception:
            pass
        reason = "спам/ссылки" if contains_link(text) else "запрещённые слова"
        state = get_mod_state(message.chat.id, message.from_user.id)
        await warn_user(message, state, reason)
        return

    state = get_mod_state(message.chat.id, message.from_user.id)
    now = time.time()
    if now - float(state.get("last_ts", 0.0)) > FLOOD_WINDOW_SEC:
        state["count"] = 0
        state["last_text"] = ""
    if text == state.get("last_text"):
        state["count"] = int(state.get("count", 0)) + 1
    else:
        state["last_text"] = text
        state["count"] = 1
    state["last_ts"] = now

    if state["count"] >= FLOOD_REPEAT_LIMIT:
        try:
            await message.delete()
        except Exception:
            pass
        await warn_user(message, state, "спам и флуд")
        state["count"] = 0
        return

    if is_faq_question(text):
        kb = InlineKeyboardMarkup(
            inline_keyboard=[
                [
                    InlineKeyboardButton(
                        text="Оформить заказ",
                        url=f"https://t.me/{ORDER_BOT_USERNAME}",
                    )
                ]
            ]
        )
        try:
            await message.answer(
                "Чтобы оформить заказ — напиши боту в ЛС.",
                reply_markup=kb,
            )
        except Exception:
            pass


# -------------------- Команды --------------------

@dp.message(Command("start"))
async def start(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id in get_banned():
        await send_clean_message(message.chat.id, "Забанен.")
        return
    if message.from_user.id not in user_locale:
        user_locale[message.from_user.id] = "ru"
    user_cart.setdefault(message.from_user.id, {})
    profile = await run_blocking(get_or_create_user, message.from_user)
    await show_profile(message.chat.id, profile)


@dp.message(Command("admin"))
async def admin_panel(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="📦 Сток", callback_data="admin_stock"),
                InlineKeyboardButton(text="🚫 Бан", callback_data="admin_ban"),
            ],
            [
                InlineKeyboardButton(text="✅ Разбан", callback_data="admin_unban"),
                InlineKeyboardButton(text="🔎 Поиск ID", callback_data="admin_lookup"),
            ],
            [InlineKeyboardButton(text="📊 Транзакции", callback_data="admin_tx")],
        ]
    )
    await message.answer("🛠 <b>Админ-панель</b>", reply_markup=kb, parse_mode="HTML")


@dp.message(Command("orders"))
async def admin_orders(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    args = (message.text or "").split()
    limit = 10
    days = ORDERS_KEEP_DAYS
    if len(args) >= 2 and args[1].isdigit():
        limit = max(1, min(50, int(args[1])))
    if len(args) >= 3 and args[2].isdigit():
        days = max(1, int(args[2]))
    since_ts = int(time.time()) - (days * 86400)
    rows = []
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT order_id, user_id, username, total, created_ts, status
                    FROM orders
                    WHERE created_ts >= %s
                    ORDER BY created_ts DESC
                    LIMIT %s
                    """,
                    (since_ts, limit),
                )
                rows = cur.fetchall()
        finally:
            conn.close()
    except Exception:
        rows = []
    if not rows:
        await message.answer("Заказов за выбранный период нет.")
        return
    lines = [f"<b>Заказы за {days} дн.</b> (последние {limit})", ""]
    for r in rows:
        dt = format_datetime_from_message_date(r["created_ts"])
        uname = r["username"]
        who = f"@{h(uname)}" if uname else f"id:{r['user_id']}"
        lines.append(
            f"• {dt} | <code>{r['order_id']}</code> | {r['total']}₸ | "
            f"{status_label(r['status'])} | {who}"
        )
    await message.answer("\n".join(lines), parse_mode="HTML")


@dp.message(Command("order"))
async def admin_order_one(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) < 2:
        await message.answer("Использование: /order <order_id>")
        return
    order_id = parts[1].strip()
    row = None
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    "SELECT * FROM orders WHERE order_id = %s",
                    (order_id,),
                )
                row = cur.fetchone()
        finally:
            conn.close()
    except Exception:
        row = None
    if not row:
        await message.answer("Заказ не найден.")
        return
    try:
        items = json.loads(row["items_json"] or "[]")
    except Exception:
        items = []
    try:
        check = json.loads(row["check_json"] or "{}")
    except Exception:
        check = {}
    items_text = format_items_text(items)
    username = row["username"] or ""
    buyer = f"@{h(username)}" if username else f"id:{row['user_id']}"
    text = (
        "<b>Заказ</b>\n"
        f"<b>ID:</b> <code>{h(row['order_id'])}</code>\n"
        f"<b>Статус:</b> {status_label(row['status'])}\n"
        f"<b>Сумма:</b> {row['total']}₸\n"
        f"<b>Время:</b> {format_datetime_from_message_date(row['created_ts'])}\n"
        f"<b>Покупатель:</b> {buyer} ({row['user_id']})\n"
        f"<b>Ник:</b> {h(row['nick'] or '')}\n\n"
        f"<b>Товары:</b>\n{items_text}\n\n"
        f"<b>Чек:</b> {check_summary(check)}"
    )
    await message.answer(text, parse_mode="HTML")


@dp.message(Command("bans"))
async def admin_bans(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    args = (message.text or "").split()
    limit = 10
    if len(args) >= 2 and args[1].isdigit():
        limit = max(1, min(50, int(args[1])))
    rows = []
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT user_id, reason, created_ts, actor_id
                    FROM bans
                    ORDER BY created_ts DESC
                    LIMIT %s
                    """,
                    (limit,),
                )
                rows = cur.fetchall()
        finally:
            conn.close()
    except Exception:
        rows = []
    if not rows:
        await message.answer("История банов пуста.")
        return
    lines = [f"<b>История банов</b> (последние {limit})", ""]
    for r in rows:
        dt = format_datetime_from_message_date(r["created_ts"])
        actor = f"админ {r['actor_id']}" if r["actor_id"] else "авто"
        lines.append(
            f"• {dt} | {r['user_id']} | {h(r['reason'] or '')} | {actor}"
        )
    await message.answer("\n".join(lines), parse_mode="HTML")


# -------------------- Админка --------------------

@dp.callback_query(F.data.in_(["admin_stock", "admin_ban", "admin_unban", "admin_lookup", "admin_tx"]))
async def admin_actions(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        await call.answer("Нет доступа", show_alert=True)
        return

    if call.data == "admin_stock":
        inv = load_inventory()
        kb_rows = []
        for k, v in inv.items():
            name = v.get("name", k)
            emoji_id = emoji_id_for_item(k, v)
            btn_kwargs = {
                "text": f"{name} — {v.get('stock', 0)} шт",
                "callback_data": f"edit_{safe_key(k)}",
            }
            if emoji_id:
                btn_kwargs["icon_custom_emoji_id"] = emoji_id
            kb_rows.append([InlineKeyboardButton(**btn_kwargs)])
        kb_rows.append([InlineKeyboardButton(text="↩️ Назад", callback_data="admin_back")])
        kb = InlineKeyboardMarkup(inline_keyboard=kb_rows)
        try:
            await call.message.edit_text("Выбери товар:", reply_markup=kb)
        except Exception:
            await call.message.answer("Выбери товар:", reply_markup=kb)
        await call.answer()
        return

    if call.data in ["admin_ban", "admin_unban"]:
        user_states[call.from_user.id] = {
            "action": "ban" if call.data == "admin_ban" else "unban"
        }
        await call.message.answer(
            "Пришли Telegram ID или внутренний ID (12 цифр) пользователя для (раз)бана:",
            reply_markup=ForceReply(),
        )
        await call.answer()
        return

    if call.data == "admin_lookup":
        user_states[call.from_user.id] = {"action": "lookup_user"}
        await call.message.answer(
            "Пришли внутренний ID пользователя (12 цифр):",
            reply_markup=ForceReply(),
        )
        await call.answer()
        return

    if call.data == "admin_tx":
        user_states[call.from_user.id] = {"action": "admin_tx_month"}
        now = datetime.now()
        await call.message.answer(
            f"Пришли месяц в формате YYYY-MM (например {now.year}-{now.month:02d}):",
            reply_markup=ForceReply(),
        )
        await call.answer()
        

@dp.callback_query(F.data.startswith("edit_"))
async def edit_stock(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        return
    safe = call.data.split("_", 1)[1]
    inv = load_inventory()
    key = find_key_by_safe(inv, safe)
    if key:
        user_states[call.from_user.id] = {"action": "set_stock", "key": key}
        await call.message.answer(
            f"Новый сток для <b>{h(inv[key].get('name', key))}</b>:",
            reply_markup=ForceReply(),
            parse_mode="HTML",
        )
    await call.answer()


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("action") == "set_stock")
async def set_stock(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    state = user_states.get(message.from_user.id)
    if not state:
        await message.answer("Ошибка состояния")
        return
    k = state.get("key")
    try:
        n = int(message.text.strip())
    except Exception:
        await message.answer("Нужно ввести целое число")
        return
    inv = load_inventory()
    if k not in inv:
        await message.answer("Товар не найден")
        user_states.pop(message.from_user.id, None)
        return
    inv[k]["stock"] = max(0, n)
    save_inventory(inv)
    await message.answer(f"Сток обновлён → {inv[k]['stock']}")
    user_states.pop(message.from_user.id, None)
    asyncio.create_task(broadcast_inventory_update({k}))


@dp.callback_query(F.data == "admin_back")
async def admin_back(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    await admin_panel(call.message)
    await call.answer()


# -------------------- Шоп --------------------

CARD_INFO = (
    "💳 <b>Номер карты:</b>\n"
    "<code>4400 4303 3359 3462</code>\n"
    "<i>(копируется при нажатии)</i>\n"
    "👤 <b>Имя:</b> <code>Аслан Ш.</code>"
)


@dp.callback_query(F.data.startswith("view_"))
async def view_item(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    await send_item_view(call, answer=True)


@dp.callback_query(F.data.startswith("add_"))
async def add_to_cart(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if not call.from_user:
        return
    uid = call.from_user.id
    safe = call.data.split("_", 1)[1]
    inv = load_inventory()
    key = find_key_by_safe(inv, safe)
    if not key:
        await call.answer("Товар не найден", show_alert=True)
        return
    try:
        stock = available_stock(inv, key, exclude_user_id=uid)
    except Exception:
        stock = 0
    cart = user_cart.setdefault(uid, {})
    current = cart.get(key, 0)
    available = stock - current
    if available <= 0:
        await call.answer(
            "Больше этого товара нельзя добавить — нет свободного стока",
            show_alert=True,
        )
        return
    if current >= MAX_PER_ITEM:
        await call.answer(f"Лимит на товар — {MAX_PER_ITEM}", show_alert=True)
        return
    cart[key] = current + 1
    await call.answer("Добавлено!")
    await send_item_view(call, answer=False)


@dp.callback_query(F.data == "cart")
async def show_cart(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    await render_cart(call, answer=True)


@dp.callback_query(F.data.startswith(("rem_", "del_")))
async def rem_item(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    safe = call.data.split("_", 1)[1]
    inv = load_inventory()
    key = find_key_by_safe(inv, safe)
    cart = user_cart.setdefault(call.from_user.id, {})
    if key and key in cart:
        if call.data.startswith("del_") or cart[key] == 1:
            del cart[key]
        else:
            cart[key] -= 1
    await call.answer("Удалено")
    await render_cart(call, answer=False)


@dp.callback_query(F.data.in_(["clear", "checkout", "catalog"]))
async def common_actions(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.data == "clear":
        user_cart.pop(call.from_user.id, None)
        await call.answer("Очищено")
        await show_inventory(call.message.chat.id, call.from_user.id)
        return

    if call.data == "checkout":
        cart = user_cart.get(call.from_user.id, {})
        if not cart:
            await call.answer("Корзина пуста", show_alert=True)
            return
        inv = await run_blocking(load_inventory)
        total = 0
        for k, q in cart.items():
            if k not in inv or available_stock(inv, k, exclude_user_id=call.from_user.id) < q:
                await call.answer(
                    "Некоторые товары больше не доступны в нужном количестве",
                    show_alert=True,
                )
                return
            total += int(inv[k].get("price", 0)) * q
        total_cents = int(total) * 100
        profile = await run_blocking(get_or_create_user, call.from_user)
        balance_cents = int(profile.get("balance_cents") or 0)
        user_states[call.from_user.id] = {
            "cart": cart.copy(),
            "total": total,
            "total_cents": total_cents,
            "step": "payment_method",
            "paid_pressed": False,
        }
        total_text = format_money(total_cents)
        balance_text = format_money(balance_cents)
        extra = ""
        if balance_cents < total_cents:
            extra = "\n<i>На балансе недостаточно для оплаты.</i>"
        await send_payment_sticker(call.message.chat.id)
        await send_clean_message(
            call.message.chat.id,
            "<b>Выберите способ оплаты</b>\n"
            f"Сумма: <b>{total_text}₸</b>\n"
            f"Баланс: <b>{balance_text}₸</b>{extra}",
            reply_markup=build_payment_method_keyboard(),
            parse_mode="HTML",
        )
        await call.answer()
        return

    if call.data == "catalog":
        await show_inventory(call.message.chat.id, call.from_user.id)
        await call.answer()


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("step") == "payment_method")
async def payment_method_choice(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.get(message.from_user.id)
    if not state:
        await send_clean_message(message.chat.id, "Ошибка состояния, начните заново.")
        return
    choice = (message.text or "").strip()
    if choice == PAYMENT_CANCEL_TEXT:
        user_states.pop(message.from_user.id, None)
        await send_clean_message(
            message.chat.id,
            "Покупка отменена.",
            reply_markup=ReplyKeyboardRemove(),
            parse_mode="HTML",
        )
        await show_inventory(message.chat.id, message.from_user.id)
        return
    if choice == PAYMENT_DIRECT_TEXT:
        state["step"] = "waiting_for_payment"
        state["paid_pressed"] = False
        state["paid_with"] = "direct"
        await send_clean_message(
            message.chat.id,
            "Вы выбрали прямую оплату.",
            reply_markup=ReplyKeyboardRemove(),
            parse_mode="HTML",
        )
        kb = InlineKeyboardMarkup(
            inline_keyboard=[
                [InlineKeyboardButton(text="💳 Оплачиваю", callback_data="paid")],
                [InlineKeyboardButton(text="❌ Отмена", callback_data="catalog")],
            ]
        )
        total = int(state.get("total") or 0)
        await send_clean_message(
            message.chat.id,
            f"<b>Заказ</b>\n"
            f"Сумма: <b>{total}₸</b>\n\n"
            f"{CARD_INFO}\n\n"
            "После нажатия <b>Оплачиваю</b> сток резервируется на 10 минут.\n"
            "Жми кнопку после оплаты.",
            reply_markup=kb,
            parse_mode="HTML",
        )
        return
    if choice == PAYMENT_BALANCE_TEXT:
        profile = await run_blocking(get_or_create_user, message.from_user)
        balance_cents = int(profile.get("balance_cents") or 0)
        total_cents = int(state.get("total_cents") or 0)
        if total_cents <= 0:
            total_cents = int(state.get("total") or 0) * 100
            state["total_cents"] = total_cents
        if balance_cents < total_cents:
            await send_clean_message(
                message.chat.id,
                "На балансе недостаточно средств для оплаты.\n"
                f"Нужно: <b>{format_money(total_cents)}₸</b>\n"
                f"Баланс: <b>{format_money(balance_cents)}₸</b>",
                reply_markup=build_payment_method_keyboard(),
                parse_mode="HTML",
            )
            return
        cart = state.get("cart") or {}
        inv = await run_blocking(load_inventory)
        ok, err, changed_keys = reserve_cart_for_user(message.from_user.id, cart, inv)
        if not ok:
            user_states.pop(message.from_user.id, None)
            await send_clean_message(
                message.chat.id,
                "Некоторые товары уже недоступны. Попробуйте оформить заказ заново.",
                reply_markup=ReplyKeyboardRemove(),
                parse_mode="HTML",
            )
            await show_inventory(message.chat.id, message.from_user.id)
            return
        if changed_keys:
            asyncio.create_task(broadcast_inventory_update(changed_keys))
        new_balance = await run_blocking(add_user_balance, message.from_user.id, -total_cents)
        if new_balance is None:
            cancel_reservation(message.from_user.id, completed=False)
            user_states.pop(message.from_user.id, None)
            await send_clean_message(
                message.chat.id,
                "Не удалось списать баланс. Попробуйте позже.",
                reply_markup=ReplyKeyboardRemove(),
                parse_mode="HTML",
            )
            await show_inventory(message.chat.id, message.from_user.id)
            return
        res = reservations.get(message.from_user.id)
        if res is not None:
            res["paid_with"] = "balance"
            res["amount_cents"] = total_cents
        state["step"] = "nick"
        state["check"] = {"type": "balance"}
        state["paid_with"] = "balance"
        state["paid_amount_cents"] = total_cents
        await send_clean_message(
            message.chat.id,
            f"✅ Оплачено балансом.\nВаш баланс: <b>{format_money(int(new_balance))}₸</b>\n\n"
            "<b>Шаг 2 из 2</b>\nТочный ник в игре:",
            reply_markup=ReplyKeyboardRemove(),
            parse_mode="HTML",
        )
        return
    await send_clean_message(
        message.chat.id,
        "Выберите вариант кнопками ниже.",
        reply_markup=build_payment_method_keyboard(),
    )


@dp.callback_query(F.data == "profile")
async def profile_view(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    profile = await run_blocking(get_or_create_user, call.from_user)
    await show_profile(call.message.chat.id, profile)
    await call.answer()


@dp.callback_query(F.data == "balance_topup")
async def balance_topup(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    await run_blocking(get_or_create_user, call.from_user)
    user_states[call.from_user.id] = {"step": "topup_amount"}
    await send_clean_message(
        call.message.chat.id,
        "На какую сумму вы хотите пополнить ваш баланс?\n"
        "<i>(напечатайте цифрами)</i>",
        reply_markup=ForceReply(),
        parse_mode="HTML",
        _view_type="topup",
    )
    await call.answer()


@dp.callback_query(F.data == "paid")
async def paid(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    state = user_states.get(call.from_user.id)
    if not state or state.get("step") != "waiting_for_payment":
        await call.answer("Сначала оформите заказ", show_alert=True)
        return
    if state.get("paid_pressed"):
        await call.answer("Уже нажато — ждите инструкций", show_alert=True)
        return
    state["paid_with"] = state.get("paid_with") or "direct"
    cart = state.get("cart") or {}
    inv = load_inventory()
    ok, err, changed_keys = reserve_cart_for_user(call.from_user.id, cart, inv)
    if not ok:
        user_states.pop(call.from_user.id, None)
        await send_clean_message(
            call.message.chat.id,
            "Некоторые товары уже недоступны. Попробуйте оформить заказ заново.",
            parse_mode="HTML",
        )
        await show_inventory(call.message.chat.id, call.from_user.id)
        await call.answer()
        return
    if changed_keys:
        asyncio.create_task(broadcast_inventory_update(changed_keys))
    state["paid_pressed"] = True
    state["step"] = "check"
    await send_clean_message(
        call.message.chat.id,
        "<b>Шаг 1 из 2</b>\n"
        "Скинь чек <b>фото</b> или <b>файлом</b>:\n\n"
        "⏳ Сток зарезервирован на 10 минут. Если не успеешь — резерв снимется.",
        reply_markup=ForceReply(),
        parse_mode="HTML",
    )
    await call.answer()


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("step") == "topup_amount")
async def topup_amount(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.get(message.from_user.id)
    if not state:
        await send_clean_message(message.chat.id, "Ошибка состояния, начните заново.")
        return
    cents = parse_amount_to_cents(message.text or "")
    if cents is None:
        await send_clean_message(message.chat.id, "Введите сумму цифрами, например: 500 или 200,36")
        return
    state["amount_cents"] = cents
    state["step"] = "topup_waiting_payment"
    state["paid_pressed"] = False
    amount_text = format_money(cents)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="💳 Оплачиваю", callback_data="topup_paid")],
            [InlineKeyboardButton(text="👤 Профиль", callback_data="profile")],
        ]
    )
    await send_clean_message(
        message.chat.id,
        f"<b>Пополнение баланса</b>\n"
        f"Сумма: <b>{amount_text}₸</b>\n\n"
        f"{CARD_INFO}\n\n"
        "После оплаты нажмите <b>Оплачиваю</b> и отправьте чек.",
        reply_markup=kb,
        parse_mode="HTML",
    )


@dp.callback_query(F.data == "topup_paid")
async def topup_paid(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    state = user_states.get(call.from_user.id)
    if not state or state.get("step") != "topup_waiting_payment":
        await call.answer("Сначала укажите сумму", show_alert=True)
        return
    if state.get("paid_pressed"):
        await call.answer("Уже нажато — ждите инструкций", show_alert=True)
        return
    state["paid_pressed"] = True
    state["step"] = "topup_check"
    await send_clean_message(
        call.message.chat.id,
        "<b>Скинь чек</b> фото или файлом:",
        reply_markup=ForceReply(),
        parse_mode="HTML",
    )
    await call.answer()


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("step") == "topup_check")
async def topup_check(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.get(message.from_user.id)
    if not state:
        await send_clean_message(message.chat.id, "Ошибка состояния, начните заново.")
        return
    if message.photo:
        check = {"type": "photo", "file_id": message.photo[-1].file_id}
    elif message.document:
        check = {
            "type": "document",
            "file_id": message.document.file_id,
            "name": message.document.file_name,
            "mime_type": message.document.mime_type,
        }
    else:
        await send_clean_message(message.chat.id, "Пожалуйста, отправьте чек фото или файлом.")
        return

    amount_cents = int(state.get("amount_cents") or 0)
    user_states.pop(message.from_user.id, None)

    profile = await run_blocking(get_or_create_user, message.from_user)
    asyncio.create_task(
        analyze_check_and_report(
            message.from_user,
            str(profile.get("internal_id") or ""),
            check,
        )
    )
    topup_id = next_topup_id()
    created_ts = int(message.date.timestamp()) if message.date else int(time.time())
    topup = {
        "topup_id": topup_id,
        "amount_cents": amount_cents,
        "time": format_datetime_from_message_date(message.date),
        "username": message.from_user.username or "без_username",
        "user_id": message.from_user.id,
        "internal_id": profile.get("internal_id"),
        "check": check,
    }
    record_topup(topup, "pending", created_ts)

    await send_clean_message(
        message.chat.id,
        "<b>Заявка на пополнение принята!</b>\nОжидайте подтверждения.",
        parse_mode="HTML",
    )

    try:
        admin_msg = await bot.send_message(
            OWNER_CHAT_ID,
            build_topup_admin_text(topup, "pending"),
            reply_markup=build_topup_admin_keyboard(topup_id),
            parse_mode="HTML",
            disable_web_page_preview=True,
        )
        topup_states[topup_id] = {
            "status": "pending",
            "user_id": message.from_user.id,
            "admin_chat_id": OWNER_CHAT_ID,
            "admin_message_id": admin_msg.message_id,
            "topup": topup,
        }
        await send_check_to_admin(check, OWNER_CHAT_ID, admin_msg.message_id)
    except Exception as e:
        await bot.send_message(
            OWNER_CHAT_ID,
            f"Не смог отправить лог пополнения. Ошибка: {e}.\nЗаявка:\n{build_topup_admin_text(topup, 'pending')}",
        )


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("step") == "check")
async def get_check(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.get(message.from_user.id)
    if not state:
        await send_clean_message(message.chat.id, "Ошибка состояния, начните заново.")
        return
    if message.photo:
        state["check"] = {"type": "photo", "file_id": message.photo[-1].file_id}
    elif message.document:
        state["check"] = {
            "type": "document",
            "file_id": message.document.file_id,
            "name": message.document.file_name,
            "mime_type": message.document.mime_type,
        }
    else:
        await send_clean_message(
            message.chat.id, "Пожалуйста, отправьте чек фото или файлом."
        )
        return
    profile = await run_blocking(get_or_create_user, message.from_user)
    asyncio.create_task(
        analyze_check_and_report(
            message.from_user,
            str(profile.get("internal_id") or ""),
            state["check"],
        )
    )
    state["step"] = "nick"
    await send_clean_message(
        message.chat.id,
        "<b>Шаг 2 из 2</b>\nТочный ник в игре:",
        reply_markup=ForceReply(),
        parse_mode="HTML",
    )


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("step") == "nick")
async def get_nick(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.pop(message.from_user.id, None)
    if not state:
        await send_clean_message(
            message.chat.id, "Ошибка состояния. Начните заново: /start"
        )
        return
    cart = state.get("cart", {})
    nick = (message.text or "").strip()
    await run_blocking(get_or_create_user, message.from_user)
    if nick:
        await run_blocking(update_user_nick, message.from_user.id, nick)
    total = state.get("total", 0)
    check = state.get("check", "")
    inv = await run_blocking(load_inventory)
    for k, q in cart.items():
        if inv.get(k, {}).get("stock", 0) < q:
            await send_clean_message(
                message.chat.id, "Товар закончился прямо сейчас. Заказ отменён."
            )
            return

    # Сток списываем только после подтверждения админом
    mark_reservation_completed(message.from_user.id)

    items = []
    for k, q in cart.items():
        it = inv.get(k, {})
        price = int(it.get("price", 0))
        items.append(
            {
                "key": k,
                "name": it.get("name", k),
                "qty": int(q),
                "price": price,
                "line_total": price * int(q),
            }
        )

    await send_clean_message(
        message.chat.id,
        "<b>Заказ принят!</b>\n"
        "Скоро выдадим.\n\n"
        "Выдача через <b>Aslan_ShRa666</b>\n"
        "Лучший шоп в СНГ — 900+ отзывов\n\n"
        "<b>Статус:</b> ожидание",
        parse_mode="HTML",
    )

    username = message.from_user.username or "без_username"
    order_id = next_order_id()
    created_ts = int(message.date.timestamp()) if message.date else int(time.time())
    order = {
        "order_id": order_id,
        "total": total,
        "time": format_datetime_from_message_date(message.date),
        "nick": nick,
        "username": username,
        "user_id": message.from_user.id,
        "items": items,
        "check": check,
    }
    if state.get("paid_with"):
        order["paid_with"] = state.get("paid_with")
    if state.get("paid_with") == "balance":
        order["paid_amount_cents"] = int(state.get("paid_amount_cents") or (total * 100))
    log_text = build_admin_text(order, "pending")
    record_order(order, "pending", created_ts)

    try:
        admin_msg = await bot.send_message(
            OWNER_CHAT_ID,
            log_text,
            reply_markup=build_admin_keyboard(order_id),
            parse_mode="HTML",
            disable_web_page_preview=True,
        )
        check_mid = await send_check_to_admin(check, OWNER_CHAT_ID, admin_msg.message_id)
        order_states[order_id] = {
            "status": "pending",
            "user_id": message.from_user.id,
            "admin_chat_id": OWNER_CHAT_ID,
            "admin_message_id": admin_msg.message_id,
            "admin_check_message_id": check_mid,
            "reminder_message_ids": [],
            "order": order,
        }
        start_pending_reminder(order_id)
        if LOG_CHANNEL_ID and log_bot:
            await log_bot.send_message(
                LOG_CHANNEL_ID,
                log_text,
                parse_mode="HTML",
                disable_web_page_preview=True,
            )
    except Exception as e:
        await bot.send_message(
            OWNER_CHAT_ID,
            f"Не смог отправить лог администратору/каналу. Ошибка: {e}.\nЗаказ:\n{log_text}",
        )

    user_cart.pop(message.from_user.id, None)


# -------------------- Статусы заказов --------------------

@dp.callback_query(F.data.startswith("topup_status:"))
async def topup_status(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        await call.answer("Нет доступа", show_alert=True)
        return
    parts = call.data.split(":")
    if len(parts) < 3:
        await call.answer("Неверные данные", show_alert=True)
        return
    topup_id = parts[1]
    status = parts[2]
    if status not in {"pending", "accepted", "rejected"}:
        await call.answer("Неверный статус", show_alert=True)
        return
    state = topup_states.get(topup_id)
    if not state:
        await call.answer("Заявка не найдена", show_alert=True)
        return
    if state.get("status") == "accepted" and status != "accepted":
        await call.answer("Уже подтверждено", show_alert=True)
        return
    if status == "accepted" and state.get("status") == "accepted":
        await call.answer("Уже подтверждено", show_alert=True)
        return

    topup = state["topup"]
    user_id = state["user_id"]
    if status == "accepted":
        new_balance = await run_blocking(
            add_user_balance, user_id, int(topup.get("amount_cents") or 0)
        )
        if new_balance is None:
            await call.answer("Не удалось обновить баланс", show_alert=True)
            return
    state["status"] = status
    await run_blocking(update_topup_status_db, topup_id, status)

    try:
        await bot.edit_message_text(
            build_topup_admin_text(topup, status),
            chat_id=state["admin_chat_id"],
            message_id=state["admin_message_id"],
            reply_markup=build_topup_admin_keyboard(topup_id),
            parse_mode="HTML",
            disable_web_page_preview=True,
        )
    except Exception:
        log_exception(f"topup_status: failed to edit admin message for {topup_id}")

    if status == "accepted":
        amount_text = format_money(int(topup.get("amount_cents") or 0))
        bal_text = format_money(int(new_balance or 0))
        msg = (
            f"✅ Баланс пополнен на {amount_text}₸.\n"
            f"Ваш баланс: {bal_text}₸"
        )
    elif status == "rejected":
        msg = "❌ Пополнение отклонено."
    else:
        msg = "⏳ Пополнение в ожидании."
    try:
        await send_clean_message(user_id, msg, parse_mode="HTML")
    except Exception:
        log_exception(f"topup_status: failed to notify user {user_id}")

    await call.answer("Статус обновлён")


@dp.callback_query(F.data.startswith("order_status:"))
async def order_status(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        await call.answer("Нет доступа", show_alert=True)
        return
    parts = call.data.split(":")
    if len(parts) < 3:
        await call.answer("Неверные данные", show_alert=True)
        return
    order_id = parts[1]
    status = parts[2]
    if status not in {"pending", "accepted", "rejected"}:
        await call.answer("Неверный статус", show_alert=True)
        return
    lock = get_order_lock(order_id)
    async with lock:
        state = order_states.get(order_id)
        if not state:
            await call.answer("Заказ не найден", show_alert=True)
            return
        if state.get("status") == "accepted" and status != "accepted":
            await call.answer("Уже подтверждено", show_alert=True)
            return
        if status == "accepted" and state.get("status") == "accepted":
            await call.answer("Уже подтверждено", show_alert=True)
            return

        order = state["order"]
        user_id = state["user_id"]
        is_balance_payment = (
            order.get("paid_with") == "balance"
            or (
                isinstance(order.get("check"), dict)
                and order.get("check", {}).get("type") == "balance"
            )
        )
        changed_keys: set[str] = set()
        if status == "accepted":
            ok, err = apply_order_stock(order)
            if not ok:
                await call.answer(f"Не удалось списать сток: {err}", show_alert=True)
                return
            changed_keys |= extract_order_keys(order)
        if status in {"accepted", "rejected"}:
            changed_keys |= cancel_reservation(user_id, completed=True)

        state["status"] = status
        await run_blocking(update_order_status_db, order_id, status)
        if status == "pending":
            start_pending_reminder(order_id)
        else:
            stop_pending_reminder(order_id)
            try:
                await delete_order_reminders(order_id)
            except Exception:
                log_exception(f"order_status: failed deleting reminders for {order_id}")

        try:
            await bot.edit_message_text(
                build_admin_text(order, status),
                chat_id=state["admin_chat_id"],
                message_id=state["admin_message_id"],
                reply_markup=build_admin_keyboard(order_id),
                parse_mode="HTML",
                disable_web_page_preview=True,
            )
        except Exception:
            log_exception(f"order_status: failed to edit admin message for {order_id}")

        if changed_keys:
            asyncio.create_task(broadcast_inventory_update(changed_keys))
        if status == "pending":
            msg = "<b>Статус заказа:</b> ожидание"
            review_pending.pop(user_id, None)
        elif status == "rejected":
            refund_text = ""
            if is_balance_payment and not order.get("balance_refunded"):
                amount_cents = int(order.get("paid_amount_cents") or (int(order.get("total") or 0) * 100))
                if amount_cents > 0:
                    new_balance = await run_blocking(add_user_balance, user_id, amount_cents)
                    order["balance_refunded"] = True
                    if new_balance is not None:
                        refund_text = f"\nСумма возвращена на баланс. Баланс: {format_money(int(new_balance))}₸"
                    else:
                        refund_text = "\nСумма будет возвращена на баланс вручную."
            msg = f"К сожалению, ваш заказ был отклонен.{refund_text}"
            review_pending.pop(user_id, None)
        else:
            msg = None
            review_pending[user_id] = order_id

        try:
            if msg is not None:
                await send_clean_message(user_id, msg, parse_mode="HTML")
            else:
                await send_review_prompt(user_id)
        except Exception:
            log_exception(f"order_status: failed to notify user {user_id}")

        if status == "accepted":
            await run_blocking(record_admin_tx_log, order, build_admin_text(order, status))
            admin_chat_id = state.get("admin_chat_id", OWNER_CHAT_ID)
            admin_msg_id = state.get("admin_message_id")
            check_msg_id = state.get("admin_check_message_id")
            if check_msg_id:
                try:
                    await bot.delete_message(admin_chat_id, check_msg_id)
                except Exception:
                    log_exception(
                        f"order_status: failed deleting check message {check_msg_id} for {order_id}"
                    )
            if admin_msg_id:
                try:
                    await bot.delete_message(admin_chat_id, admin_msg_id)
                except Exception:
                    log_exception(
                        f"order_status: failed deleting admin message {admin_msg_id} for {order_id}"
                    )

        await call.answer("Статус обновлён")


@dp.callback_query(F.data.startswith("order_ban:"))
async def order_ban(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        await call.answer("Нет доступа", show_alert=True)
        return
    parts = call.data.split(":")
    if len(parts) < 2:
        await call.answer("Неверные данные", show_alert=True)
        return
    order_id = parts[1]
    state = order_states.get(order_id)
    if not state:
        await call.answer("Заказ не найден", show_alert=True)
        return
    user_id = state["user_id"]
    try:
        await delete_order_reminders(order_id)
    except Exception:
        pass
    changed_keys = cancel_reservation(user_id, completed=True)
    if changed_keys:
        asyncio.create_task(broadcast_inventory_update(changed_keys))
    ban_user(user_id, "бан через заказ", call.from_user.id)
    record_ban_history(user_id, "бан через заказ", call.from_user.id)
    review_pending.pop(user_id, None)
    try:
        await send_clean_message(user_id, "Вы заблокированы.")
    except Exception:
        pass
    await call.answer("Пользователь забанен")


@dp.callback_query(F.data == "review_decline")
async def review_decline(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id not in review_pending:
        await call.answer("Нет активного запроса отзыва", show_alert=True)
        return
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="✅ Да, отказаться", callback_data="review_decline_confirm")],
            [InlineKeyboardButton(text="↩️ Назад", callback_data="review_decline_cancel")],
        ]
    )
    await send_clean_message(
        call.message.chat.id,
        "Если вы не оставите отзыв, вам не выдастся кэшбэк.\nПодтвердить отказ?",
        reply_markup=kb,
        parse_mode="HTML",
    )
    await call.answer()


@dp.callback_query(F.data == "review_decline_confirm")
async def review_decline_confirm(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    review_pending.pop(call.from_user.id, None)
    await send_clean_message(
        call.message.chat.id,
        "Хорошо, без отзыва. Кэшбэк начислен не будет.",
        parse_mode="HTML",
    )
    await call.answer()


@dp.callback_query(F.data == "review_decline_cancel")
async def review_decline_cancel(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id in review_pending:
        try:
            await send_review_prompt(call.from_user.id)
        except Exception:
            pass
    await call.answer()


@dp.message(lambda m: m.from_user.id in review_pending and m.text and not m.text.startswith("/"))
async def handle_review(message: Message):
    if not is_private_chat(message.chat):
        return
    user_id = message.from_user.id
    order_id = review_pending.pop(user_id, None)
    text = (message.text or "").strip()
    if not text:
        await send_clean_message(message.chat.id, "Отправьте отзыв текстом.")
        return
    if "@Vexsento" not in text:
        text = text + "\n\n@Vexsento"
    if REVIEW_CHAT_ID and REVIEW_MESSAGE_ID:
        try:
            await bot.send_message(
                REVIEW_CHAT_ID,
                text,
                reply_to_message_id=REVIEW_MESSAGE_ID,
                disable_web_page_preview=True,
            )
            await send_clean_message(
                message.chat.id, "Спасибо! Отзыв отправлен.", parse_mode="HTML"
            )
            return
        except Exception as e:
            await bot.send_message(OWNER_CHAT_ID, f"Ошибка отправки отзыва (order {order_id}): {e}")
    else:
        await bot.send_message(OWNER_CHAT_ID, "REVIEW_CHAT_ID/REVIEW_MESSAGE_ID не настроены.")

    await send_clean_message(
        message.chat.id,
        "Не смог отправить отзыв автоматически. Напишите вручную под постом:\n"
        "https://t.me/VexsentoMm2ZaTengeShop/179",
        disable_web_page_preview=True,
    )


@dp.message(lambda m: m.from_user.id in review_pending and not m.text)
async def handle_review_nontext(message: Message):
    if not is_private_chat(message.chat):
        return
    await send_clean_message(message.chat.id, "Отправьте отзыв текстом.")


# -------------------- Бан / разбан --------------------

@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("action") in ["ban", "unban"])
async def handle_ban_unban(message: Message):
    if not is_private_chat(message.chat):
        return
    state = user_states.get(message.from_user.id)
    if not state or message.from_user.id != OWNER_CHAT_ID:
        return
    action = state.get("action")
    raw = (message.text or "").strip()
    uid = None
    if re.fullmatch(r"\d{12}", raw):
        user = get_user_by_internal_id(raw)
        if user:
            uid = int(user.get("user_id") or 0)
    if uid is None:
        try:
            uid = int(raw)
        except Exception:
            await message.answer("Нужно прислать Telegram ID или внутренний ID (12 цифр)")
            return
    if action == "ban":
        ban_user(uid, "бан командой", message.from_user.id)
        record_ban_history(uid, "бан командой", message.from_user.id)
        await message.answer(f"Пользователь {uid} забанен")
    else:
        unban_user(uid)
        await message.answer(f"Пользователь {uid} разбанен")
    user_states.pop(message.from_user.id, None)


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("action") == "lookup_user")
async def handle_lookup_user(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    internal_id = (message.text or "").strip()
    if not re.fullmatch(r"\d{12}", internal_id):
        await message.answer("Нужно прислать внутренний ID из 12 цифр")
        return
    user = get_user_by_internal_id(internal_id)
    if not user:
        await message.answer("Пользователь не найден")
        return

    username = user.get("username") or ""
    if username:
        uname = f"@{h(username)}"
        link = f"https://t.me/{username}"
    else:
        uname = "—"
        link = f"tg://user?id={user.get('user_id')}"
    link_html = f'<a href="{link}">ссылка</a>'
    balance = format_money(int(user.get("balance_cents") or 0))
    reg_dt = format_datetime_from_message_date(user.get("created_ts") or 0)

    lines = [
        "<b>Пользователь</b>",
        f"<b>Внутр. ID:</b> <code>{h(internal_id)}</code>",
        f"<b>Telegram ID:</b> {user.get('user_id')}",
        f"<b>Юзернейм:</b> {uname}",
        f"<b>Ник:</b> {h(user.get('nick') or '—')}",
        f"<b>Ссылка:</b> {link_html}",
        f"<b>Дата регистрации:</b> {reg_dt}",
        f"<b>Баланс:</b> {balance}₸",
        "",
        "<b>Транзакции</b>",
    ]
    txs = get_user_transactions(int(user.get("user_id") or 0), limit=20)
    kb_rows = []
    if not txs:
        lines.append("—")
    else:
        for tx in txs:
            dt = format_datetime_from_message_date(tx.get("created_ts") or 0)
            kind = "Покупка" if tx.get("type") == "order" else "Пополнение"
            status_text = (
                status_label(tx.get("status") or "pending")
                if tx.get("type") == "order"
                else topup_status_label(tx.get("status") or "pending")
            )
            if tx.get("type") == "order":
                what_html = format_order_items_short_html(tx.get("items"))
            else:
                what_html = h(tx.get("what") or "—")
            check = tx.get("check")
            check_token = register_check_view(check)
            if check_token:
                ctype = check.get("type") if isinstance(check, dict) else None
                icon = "📷" if ctype == "photo" else "📎"
                label_id = tx.get("id") or ""
                label = f"{icon} Чек {label_id}".strip()
                kb_rows.append(
                    [
                        InlineKeyboardButton(
                            text=label, callback_data=f"check_view:{check_token}"
                        )
                    ]
                )
                check_text = icon
            else:
                check_text = check_summary(check)
            lines.append(
                f"• {dt} | {kind} | {tx.get('amount')} | {status_text} | "
                f"{what_html} | чек: {check_text}"
            )
    kb = InlineKeyboardMarkup(inline_keyboard=kb_rows) if kb_rows else None
    await message.answer(
        "\n".join(lines),
        parse_mode="HTML",
        disable_web_page_preview=True,
        reply_markup=kb,
    )
    user_states.pop(message.from_user.id, None)


@dp.message(lambda m: user_states.get(m.from_user.id, {}).get("action") == "admin_tx_month")
async def handle_admin_tx_month(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    text = (message.text or "").strip()
    match = re.fullmatch(r"(\d{4})-(\d{2})", text)
    if not match:
        await message.answer("Неверный формат. Пример: 2026-02")
        return
    year = int(match.group(1))
    month = int(match.group(2))
    if month < 1 or month > 12:
        await message.answer("Неверный месяц. Укажите от 01 до 12.")
        return

    start_ts, end_ts = month_range_ts(year, month)
    rows: list[Dict[str, Any]] = []
    try:
        conn = get_db_conn()
        try:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    SELECT order_id, user_id, username, total, created_ts, status
                    FROM orders
                    WHERE created_ts >= %s AND created_ts < %s
                    ORDER BY created_ts DESC
                    """,
                    (start_ts, end_ts),
                )
                for r in cur.fetchall():
                    rows.append(
                        {
                            "created_ts": int(r.get("created_ts") or 0),
                            "type": "order",
                            "id": r.get("order_id"),
                            "user_id": r.get("user_id"),
                            "username": r.get("username") or "",
                            "amount": f"{int(r.get('total') or 0)}₸",
                            "status": r.get("status") or "pending",
                        }
                    )
                cur.execute(
                    """
                    SELECT topup_id, user_id, username, amount_cents, created_ts, status
                    FROM topups
                    WHERE created_ts >= %s AND created_ts < %s
                    ORDER BY created_ts DESC
                    """,
                    (start_ts, end_ts),
                )
                for r in cur.fetchall():
                    rows.append(
                        {
                            "created_ts": int(r.get("created_ts") or 0),
                            "type": "topup",
                            "id": r.get("topup_id"),
                            "user_id": r.get("user_id"),
                            "username": r.get("username") or "",
                            "amount": f"{format_money(int(r.get('amount_cents') or 0))}₸",
                            "status": r.get("status") or "pending",
                        }
                    )
        finally:
            conn.close()
    except Exception:
        rows = []

    rows.sort(key=lambda x: x.get("created_ts", 0), reverse=True)
    header = f"<b>Транзакции за {year}-{month:02d}</b>"
    if not rows:
        await message.answer(f"{header}\n\n—", parse_mode="HTML")
        user_states.pop(message.from_user.id, None)
        return

    lines = [header, ""]
    messages: list[str] = []
    for r in rows:
        dt = format_datetime_from_message_date(r.get("created_ts") or 0)
        kind = "Покупка" if r.get("type") == "order" else "Пополнение"
        status_text = (
            status_label(r.get("status") or "pending")
            if r.get("type") == "order"
            else topup_status_label(r.get("status") or "pending")
        )
        uname = r.get("username") or ""
        who = f"@{h(uname)}" if uname else f"id:{r.get('user_id')}"
        lines.append(
            f"• {dt} | {kind} | {r.get('amount')} | {status_text} | {who} | {h(r.get('id') or '')}"
        )
        if sum(len(x) for x in lines) > 3500:
            messages.append("\n".join(lines))
            lines = [header, ""]
    if lines and (len(lines) > 2 or not messages):
        messages.append("\n".join(lines))
    for msg in messages:
        await message.answer(msg, parse_mode="HTML", disable_web_page_preview=True)
    user_states.pop(message.from_user.id, None)


@dp.callback_query(F.data.startswith("check_view:"))
async def check_view(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.from_user.id != OWNER_CHAT_ID:
        await call.answer("Нет доступа", show_alert=True)
        return
    token = call.data.split(":", 1)[1]
    entry = check_view_map.get(token)
    if not entry:
        await call.answer("Чек не найден или устарел", show_alert=True)
        return
    try:
        await send_check_to_admin(
            entry.get("check"), call.message.chat.id, reply_to=call.message.message_id
        )
        await call.answer()
    except Exception:
        await call.answer("Не удалось открыть чек", show_alert=True)


@dp.message(F.reply_to_message, F.text)
async def ban_by_reply(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id != OWNER_CHAT_ID:
        return
    if message.text.strip().lower() != "бан":
        return
    banned_id = message.reply_to_message.from_user.id
    ban_user(banned_id, "бан ответом", message.from_user.id)
    record_ban_history(banned_id, "бан ответом", message.from_user.id)
    await send_clean_message(banned_id, "Вы заблокированы.")
    await message.answer(f"Пользователь {banned_id} заблокирован.")


def build_power_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="🌐 Language", callback_data="menu_lang"),
                InlineKeyboardButton(text="🎮 Games", callback_data="menu_games"),
            ],
            [InlineKeyboardButton(text="🎙 Voice Input", callback_data="menu_voice")],
        ]
    )


def build_games_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🔐 Cipher Quest", callback_data="game_start_cipher")],
            [InlineKeyboardButton(text="🎯 Bulls & Cows", callback_data="game_start_bulls")],
            [InlineKeyboardButton(text="♟ Checkers", callback_data="game_start_checkers")],
        ]
    )


@dp.message(Command("power"))
async def power_menu(message: Message):
    if not is_private_chat(message.chat):
        return
    await send_clean_message(
        message.chat.id,
        "⚡ <b>Power menu</b>\nAdvanced bot features are available here.",
        parse_mode="HTML",
        reply_markup=build_power_menu_kb(),
    )


@dp.message(Command("lang"))
async def language_menu(message: Message):
    if not is_private_chat(message.chat):
        return
    await send_clean_message(
        message.chat.id,
        tr(message.from_user.id, "lang_pick"),
        parse_mode="HTML",
        reply_markup=build_lang_keyboard(),
    )


@dp.callback_query(F.data.startswith("lang_set:"))
async def language_set_callback(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    lang_code = (call.data or "").split(":", 1)[1].strip().lower()
    if lang_code not in SUPPORTED_LANGS:
        await call.answer("Invalid language", show_alert=True)
        return
    set_user_lang(call.from_user.id, lang_code)
    await send_clean_message(
        call.message.chat.id,
        tr(call.from_user.id, "lang_set", lang=LANG_LABELS.get(lang_code, lang_code)),
        parse_mode="HTML",
    )
    await call.answer()


@dp.callback_query(F.data.in_(["menu_power", "menu_lang", "menu_games", "menu_voice"]))
async def power_menu_callbacks(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.data == "menu_power":
        await send_clean_message(
            call.message.chat.id,
            "⚡ <b>Возможности</b>\nВыберите раздел ниже:",
            parse_mode="HTML",
            reply_markup=build_power_menu_kb(),
        )
    elif call.data == "menu_lang":
        await send_clean_message(
            call.message.chat.id,
            tr(call.from_user.id, "lang_pick"),
            parse_mode="HTML",
            reply_markup=build_lang_keyboard(),
        )
    elif call.data == "menu_games":
        await send_clean_message(
            call.message.chat.id,
            tr(call.from_user.id, "games_menu"),
            parse_mode="HTML",
            reply_markup=build_games_kb(),
        )
    else:
        await send_clean_message(
            call.message.chat.id,
            "🎙 <b>Voice input</b>\nSend a voice message in private chat.\n"
            "I will transcribe it and try to execute intent (catalog/cart/profile/games).",
            parse_mode="HTML",
        )
    await call.answer()


@dp.message(Command("games"))
async def games_menu(message: Message):
    if not is_private_chat(message.chat):
        return
    await send_clean_message(
        message.chat.id,
        tr(message.from_user.id, "games_menu"),
        parse_mode="HTML",
        reply_markup=build_games_kb(),
    )


@dp.callback_query(F.data.in_(["game_start_cipher", "game_start_bulls", "game_start_checkers"]))
async def game_start(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    uid = call.from_user.id
    if call.data == "game_start_cipher":
        game = start_cipher_game(uid)
        await send_clean_message(
            call.message.chat.id,
            f"{tr(uid, 'game_cipher_title')}\n\n<code>{h(game.get('encoded', ''))}</code>",
            parse_mode="HTML",
        )
    elif call.data == "game_start_bulls":
        start_bulls_game(uid)
        await send_clean_message(
            call.message.chat.id,
            tr(uid, "game_bulls_title"),
            parse_mode="HTML",
        )
    else:
        await send_clean_message(
            call.message.chat.id,
            tr(uid, "game_checkers_title"),
            parse_mode="HTML",
            reply_markup=build_checkers_level_kb(uid),
        )
    await call.answer()


@dp.callback_query(F.data.startswith("game_checkers_level:"))
async def game_checkers_level(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    parts = (call.data or "").split(":", 1)
    if len(parts) < 2:
        await call.answer("Неверные данные", show_alert=True)
        return
    level = clamp_checkers_level(parts[1])
    game = start_checkers_game(call.from_user.id, level)
    await send_checkers_board(
        call.message.chat.id,
        call.from_user.id,
        game,
        extra=tr(call.from_user.id, "game_checkers_click_help"),
    )
    await call.answer()


@dp.callback_query(F.data.in_(["checkers_noop", "checkers_refresh"]))
async def checkers_aux_callback(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    if call.data == "checkers_noop":
        await call.answer()
        return
    game = mini_games.get(call.from_user.id)
    if not game or game.get("type") != "checkers":
        await call.answer("Нет активной игры", show_alert=True)
        return
    await send_checkers_board(call.message.chat.id, call.from_user.id, game)
    await call.answer()


@dp.callback_query(F.data == "checkers_resign")
async def checkers_resign(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    game = mini_games.get(call.from_user.id)
    if not game or game.get("type") != "checkers":
        await call.answer("Нет активной игры", show_alert=True)
        return
    mini_games.pop(call.from_user.id, None)
    await send_clean_message(
        call.message.chat.id,
        tr(call.from_user.id, "game_checkers_resigned"),
        parse_mode="HTML",
    )
    await call.answer()


@dp.callback_query(F.data.startswith("checkers_cell:"))
async def checkers_cell_click(call: CallbackQuery):
    if not call.message or not is_private_chat(call.message.chat):
        await call.answer()
        return
    game = mini_games.get(call.from_user.id)
    if not game or game.get("type") != "checkers":
        await call.answer("Нет активной игры", show_alert=True)
        return
    parts = (call.data or "").split(":")
    if len(parts) != 3:
        await call.answer("Неверные данные", show_alert=True)
        return
    try:
        row = int(parts[1])
        col = int(parts[2])
    except Exception:
        await call.answer("Неверные данные", show_alert=True)
        return
    if not checkers_in_bounds(row, col):
        await call.answer()
        return

    legal_moves, selected, selectable, targets = checkers_human_context(game)
    clicked = (row, col)
    if not legal_moves:
        await process_checkers_user_path(call.message.chat.id, call.from_user.id, game, None)
        await call.answer()
        return

    if selected is None:
        if clicked in selectable:
            game["ui_selected"] = [row, col]
            await send_checkers_board(
                call.message.chat.id,
                call.from_user.id,
                game,
                extra=tr(call.from_user.id, "game_checkers_select_target"),
            )
            await call.answer()
            return
        await call.answer(tr(call.from_user.id, "game_checkers_select_piece"), show_alert=False)
        return

    if clicked == selected:
        game["ui_selected"] = None
        await send_checkers_board(call.message.chat.id, call.from_user.id, game)
        await call.answer()
        return

    if clicked in targets:
        game["ui_selected"] = None
        await process_checkers_user_path(
            call.message.chat.id,
            call.from_user.id,
            game,
            [selected, clicked],
        )
        await call.answer()
        return

    if clicked in selectable:
        game["ui_selected"] = [row, col]
        await send_checkers_board(
            call.message.chat.id,
            call.from_user.id,
            game,
            extra=tr(call.from_user.id, "game_checkers_select_target"),
        )
        await call.answer()
        return

    await call.answer(tr(call.from_user.id, "game_checkers_select_target"), show_alert=False)


@dp.message(Command("game_stats"))
async def game_stats_view(message: Message):
    if not is_private_chat(message.chat):
        return
    uid = message.from_user.id
    stats = init_game_stats(uid)
    await send_clean_message(
        message.chat.id,
        tr(
            uid,
            "game_stats",
            cipher_wins=int(stats.get("cipher_wins", 0)),
            cipher_games=int(stats.get("cipher_games", 0)),
            bulls_wins=int(stats.get("bulls_wins", 0)),
            bulls_games=int(stats.get("bulls_games", 0)),
            checkers_wins=int(stats.get("checkers_wins", 0)),
            checkers_games=int(stats.get("checkers_games", 0)),
        ),
        parse_mode="HTML",
    )


@dp.message(Command("cancel_game"))
async def cancel_game(message: Message):
    if not is_private_chat(message.chat):
        return
    mini_games.pop(message.from_user.id, None)
    await send_clean_message(message.chat.id, "Игра отменена.")


@dp.message(lambda m: m.from_user and m.from_user.id in mini_games and m.text and not m.text.startswith("/"))
async def game_input(message: Message):
    if not is_private_chat(message.chat):
        return
    uid = message.from_user.id
    game = mini_games.get(uid)
    if not game:
        return

    gtype = game.get("type")
    if gtype == "cipher":
        phrase = normalize_game_text(str(game.get("phrase") or ""))
        guess = normalize_game_text(message.text or "")
        attempts = int(game.get("attempts", 0)) + 1
        game["attempts"] = attempts
        if guess == phrase:
            stats = init_game_stats(uid)
            stats["cipher_wins"] = int(stats.get("cipher_wins", 0)) + 1
            mini_games.pop(uid, None)
            await send_clean_message(
                message.chat.id,
                tr(uid, "game_cipher_win", attempts=attempts),
                parse_mode="HTML",
            )
            return
        origin = str(game.get("phrase") or "")
        words = [w for w in origin.split() if w]
        if attempts <= 2:
            hint = f"Длина фразы: {len(origin)}"
        elif attempts <= 4:
            hint = f"Первая буква: {origin[:1]}"
        else:
            first_word = words[0] if words else origin
            hint = f"Начало: {first_word[:2]}..."
        await send_clean_message(
            message.chat.id,
            tr(uid, "game_cipher_fail", hint=hint),
            parse_mode="HTML",
        )
        return

    if gtype == "bulls":
        guess = (message.text or "").strip()
        if not re.fullmatch(r"\d{4}", guess) or len(set(guess)) != 4:
            await send_clean_message(
                message.chat.id,
                tr(uid, "game_guess_format"),
                parse_mode="HTML",
            )
            return
        secret = str(game.get("secret") or "")
        attempts = int(game.get("attempts", 0)) + 1
        game["attempts"] = attempts
        bulls, cows = bulls_and_cows(secret, guess)
        left = int(game.get("max_attempts", 12)) - attempts
        if bulls == 4:
            stats = init_game_stats(uid)
            stats["bulls_wins"] = int(stats.get("bulls_wins", 0)) + 1
            mini_games.pop(uid, None)
            await send_clean_message(
                message.chat.id,
                tr(uid, "game_bulls_win", code=secret, attempts=attempts),
                parse_mode="HTML",
            )
            return
        if left <= 0:
            mini_games.pop(uid, None)
            await send_clean_message(
                message.chat.id,
                tr(uid, "game_bulls_lose", code=secret),
                parse_mode="HTML",
            )
            return
        await send_clean_message(
            message.chat.id,
            tr(uid, "game_bulls_step", bulls=bulls, cows=cows, left=left),
            parse_mode="HTML",
        )
        return

    if gtype == "checkers":
        user_path = parse_checkers_path(message.text or "")
        if not user_path:
            board = game.get("board")
            legal_human_moves = (
                checkers_generate_moves(board, "human")
                if isinstance(board, list)
                else []
            )
            await send_checkers_board(
                message.chat.id,
                uid,
                game,
                extra=(
                    f"{tr(uid, 'game_checkers_bad_move')}\n\n"
                    f"<code>{h(checkers_legal_moves_preview(legal_human_moves))}</code>"
                ),
            )
            return
        await process_checkers_user_path(message.chat.id, uid, game, user_path)
        return


@dp.message(F.voice)
async def handle_voice_message(message: Message):
    if not is_private_chat(message.chat):
        return
    uid = message.from_user.id
    if uid in get_banned():
        await send_clean_message(message.chat.id, "Вы заблокированы.")
        return

    await send_clean_message(message.chat.id, tr(uid, "voice_wait"), parse_mode="HTML")
    text, err = await transcribe_voice_message(message, VOICE_RECOGNITION_LANG)
    if err == "dep_missing":
        await send_clean_message(message.chat.id, tr(uid, "voice_dep_missing"), parse_mode="HTML")
        return
    if text is None:
        await send_clean_message(message.chat.id, tr(uid, "voice_no_text"), parse_mode="HTML")
        return
    text = (text or "").strip()
    if not text:
        await send_clean_message(message.chat.id, tr(uid, "voice_no_text"), parse_mode="HTML")
        return

    # Try routing recognized voice text into current state handlers.
    text_msg = clone_message_with_text(message, text)
    if text_msg:
        state = user_states.get(uid, {})
        step = state.get("step")
        if step == "payment_method":
            await payment_method_choice(text_msg)
            return
        if step == "topup_amount":
            await topup_amount(text_msg)
            return
        if step == "nick":
            await get_nick(text_msg)
            return
        if uid in mini_games and not text.startswith("/"):
            await game_input(text_msg)
            return
        if uid in review_pending and not text.startswith("/"):
            await handle_review(text_msg)
            return

    # Intent routing for generic voice commands.
    intent = detect_voice_intent(text)
    if intent == "catalog":
        await show_inventory(message.chat.id, uid)
        return
    if intent == "cart":
        cart = user_cart.get(uid, {})
        if cart:
            inv = await run_blocking(load_inventory)
            txt, kb = build_cart_text_and_kb(cart, inv)
            await send_clean_message(message.chat.id, txt, parse_mode="HTML", reply_markup=kb)
        else:
            await send_clean_message(message.chat.id, "Корзина пуста.")
        return
    if intent == "profile":
        profile = await run_blocking(get_or_create_user, message.from_user)
        await show_profile(message.chat.id, profile)
        return
    if intent == "games":
        await send_clean_message(
            message.chat.id,
            tr(uid, "games_menu"),
            parse_mode="HTML",
            reply_markup=build_games_kb(),
        )
        return

    await send_clean_message(
        message.chat.id,
        tr(uid, "voice_text", text=h(text)),
        parse_mode="HTML",
    )


# -------------------- Прочее --------------------

@dp.message()
async def catch_all(message: Message):
    if not is_private_chat(message.chat):
        return
    if message.from_user.id in get_banned():
        await send_clean_message(message.chat.id, "Вы заблокированы.")
        return
    state = user_states.get(message.from_user.id, {})
    if state.get("step") or state.get("action"):
        return
    if review_pending.get(message.from_user.id):
        return
    if message.text:
        cmd = message.text.split()[0]
        if cmd in ("/start", "/admin", "/power", "/lang", "/games", "/game_stats", "/cancel_game"):
            return
        if (
            message.reply_to_message
            and message.text.strip().lower() == "бан"
            and message.from_user.id == OWNER_CHAT_ID
        ):
            return
    await send_clean_message(
        message.chat.id, "Я не понимаю эту команду. Используйте /start."
    )


async def main():
    print("Шоп запущен")
    try:
        load_inventory()
    except Exception as e:
        print("Ошибка загрузки inventory:", e)
    try:
        init_db()
        prune_old_orders()
        prune_admin_tx_logs()
    except Exception as e:
        print("Ошибка инициализации БД:", e)

    try:
        await bot.delete_webhook(drop_pending_updates=True)
    except Exception as e:
        print("Не смог удалить webhook:", e)

    try:
        asyncio.create_task(admin_tx_prune_loop())
    except Exception:
        log_exception("main: failed to start admin_tx_prune_loop")

    while True:
        try:
            await dp.start_polling(bot)
        except Exception as ex:
            print("Polling crashed:", ex)
            await asyncio.sleep(5)


if __name__ == "__main__":
    asyncio.run(main())
