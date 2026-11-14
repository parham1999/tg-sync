#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Telegram channel reposter.

Reads PUBLIC channels through their web preview (t.me/s/<name>), drops ad posts,
rewrites the caption (source channel IDs/links -> your channel) and publishes
the post to your own channel using a normal bot.

Only the Python standard library is used - nothing to install.
Works on Python 3.8+.

Usage:
    python repost.py              run forever (checks every N seconds)
    python repost.py --check      verify token / bot admin rights / sources
    python repost.py --dry-run    show what WOULD be posted, send nothing
    python repost.py --once       run a single cycle and exit
"""
import argparse
import datetime
import hashlib
import html
import io
import json
import logging
import os
import random
import re
import sys
import time
import urllib.error
import urllib.request
import uuid
from html.parser import HTMLParser

try:                                  # optional: used only to put your ID on photos
    from PIL import Image, ImageDraw, ImageFont
except Exception:                     # pragma: no cover
    Image = None

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
MAX_UPLOAD = 49 * 1024 * 1024  # Bot API upload limit is 50 MB

DEFAULTS = {
    "bot_token": "",
    "target_channel": "",
    "sources": [],
    "check_every_seconds": 300,
    # Only the NEWEST post of each source is considered every time the program runs
    # (older ones are never copied). Source order is shuffled and posts are spaced out.
    "latest_only": True,
    "random_delay_seconds": [15, 60],   # random pause between two posts of one run
    "max_posts_per_run": 6,             # at most this many posts per round (0 = no limit)
    "interval_minutes": [30, 40],       # minimum gap between two posting rounds
    "utc_offset_minutes": 210,          # Iran time (UTC+3:30)
    "night_hours": [1, 6],              # from 01:00 until 05:59 ...
    "night_max_posts": 1,               # ... only this many posts per round ...
    "night_interval_minutes": [60, 70], # ... and one round per hour
    "watermark": True,                  # small ID in the corner of photos (never on videos)
    "watermark_text": "",               # empty = your channel ID
    "owner_id": 0,                      # filled automatically when you press Start in the bot
    "review_suspicious": True,          # send suspected ads to you with Send / Reject buttons
    "review_keyword_ads": False,        # also review posts with obvious betting words (noisy)
    "review_max_per_round": 3,
    # crisis mode: a sudden flood of posts (war, disaster ...)
    "crisis_interval_minutes": [10, 15],   # rounds are this far apart while it is on
    "crisis_posts_per_channel": 3,         # latest N new posts of every source (normally only 1)
    "crisis_max_posts": 15,                # at most this many posts per round
    "crisis_delay_seconds": [5, 15],       # pause between two posts
    "crisis_on_rate": 24,                  # auto-on: this many new posts (all sources) within 30 min ...
    "crisis_on_channels": 4,               # ... or this many sources with ...
    "crisis_channel_rate": 5,              # ... at least this many new posts each within 30 min
    "crisis_off_rate": 14,                 # auto-off: below this many per 30 min for 20 minutes
    "widen_max_layers": 4,                 # to reach the wanted post count: up to this many newest posts per source
    "widen_max_age_minutes": 60,           # ... but only posts younger than this (the newest one is always allowed)
    "manual_max_posts": 15,                # the highest number you can type in "manual" speed
    "crisis_max_hours": 8,                 # auto mode never stays on longer than this
    "report_time": [23, 30],               # daily report to the bot chat (Iran time)
    "initial_posts": 0,            # how many old posts to publish on the very first run
    "delay_between_posts": 3,
    "replacements": [],            # [["old text", "new text"], ...]
    "keep_mentions": [],           # @usernames that must NOT be replaced
    "add_footer": True,            # add your @channel at the end if it is missing
    "strip_all_links": False,      # True = remove every link, keep only the text
    "link_previews": False,
    "skip_forwarded": True,        # forwarded posts are never copied
    "skip_replies": True,
    "skip_invite_links": True,     # posts that contain t.me/+xxx or joinchat links
    # any of these pieces of text anywhere in the post => treated as an ad
    "ad_keywords": [
        "#تبلیغ", "#تبلیغات", "تبلیغات", "رزرو تبلیغ", "سفارش تبلیغ", "جهت تبلیغ",
        "#ad", "#ads", "sponsored", "#sponsored", "advertisement",
        "شرط بندی", "شرط‌بندی", "شرطبندی", "شرط بند", "کازینو", "پوکر", "اسلات",
        "رولت", "بونوس", "بونس", "تخفیف", "کد معرف", "ثبت نام و دریافت", "ثبت‌نام و دریافت",
        "betting", "casino", "poker", "1xbet", "bet365", "bonus", "jackpot", "slot",
    ],
    # whole words only (so "بت" matches the word "بت" but not "ثبت")
    "ad_words": ["بت", "بت‌ها", "bet", "bets"],
    # ads almost always carry a link to a site/app: skip every post that has a
    # link to anything other than Telegram (links to the domains below are allowed)
    "extra_ad_keywords": [],      # your own additional ad words (added to ad_keywords)
    "skip_other_mentions": True,   # skip posts that mention/link ANOTHER channel or bot
    "skip_posts_with_links": True,
    "allowed_domains": ["telegra.ph", "youtube.com", "youtu.be"],
    "blocked_domains": [],
    "incomplete_post": "skip",     # "skip" or "text_only" when media cannot be copied
    "proxy": "",                   # e.g. "http://127.0.0.1:10809" (empty = system settings)
    "api_base": "https://api.telegram.org",
    "web_base": "https://t.me/s/",
}

log = logging.getLogger("repost")
IN_CLOUD = os.environ.get("GITHUB_ACTIONS") == "true"


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #
class ApiError(Exception):
    def __init__(self, desc, code=0, retry_after=0):
        Exception.__init__(self, desc)
        self.desc = desc
        self.code = code
        self.retry_after = retry_after


class NetError(Exception):
    pass


class Skip(Exception):
    pass


def die(msg):
    print("\nERROR: " + msg + "\n")
    sys.exit(2)


def plain(s):
    s = re.sub(r"<br\s*/?>", "\n", s, flags=re.I)
    return html.unescape(re.sub(r"<[^>]+>", "", s))


def vis_len(s):
    return len(plain(s))


def normalize_source(s):
    s = s.strip()
    s = re.sub(r"^(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(?:s/)?", "", s, flags=re.I)
    return s.lstrip("@").split("/")[0].split("?")[0]


def load_config(path):
    """Config comes from the CONFIG_JSON environment variable (cloud mode, kept in a
    GitHub secret) or, if that is not set, from config.json next to this file."""
    env = os.environ.get("CONFIG_JSON", "").strip()
    try:
        if env:
            raw = json.loads(env)
        else:
            with open(path, "r", encoding="utf-8-sig") as f:
                raw = json.load(f)
    except FileNotFoundError:
        die("config.json not found next to repost.py")
    except ValueError as e:
        die("the config has a typing mistake (quotes/commas): %s" % e)
    cfg = dict(DEFAULTS)
    cfg.update(raw)
    extra = os.environ.get("SETTINGS_JSON", "").strip()   # optional second secret (no token inside)
    if extra:
        try:
            cfg.update(json.loads(extra))
        except ValueError as e:
            die("SETTINGS_JSON has a typing mistake (quotes/commas): %s" % e)
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip() or str(cfg["bot_token"]).strip()
    if not token or "PASTE" in token.upper():
        die("bot_token is empty in config.json - paste the token you got from @BotFather.")
    cfg["bot_token"] = token
    # Optional test mode: a file named target_override.txt next to this script
    # (line 1 = "@test_channel", optional line "initial_posts=5") replaces the target.
    ov = os.path.join(BASE_DIR, "target_override.txt")
    if os.path.exists(ov):
        with open(ov, "r", encoding="utf-8-sig") as f:
            lines = [l.strip() for l in f.read().splitlines() if l.strip()]
        if lines and lines[0].startswith("@"):
            cfg["target_channel"] = lines[0]
            for l in lines[1:]:
                if l.startswith("initial_posts="):
                    cfg["initial_posts"] = int(l.split("=", 1)[1])
            cfg["_test_mode"] = True
            print("*** TEST MODE: posting to the test channel from target_override.txt ***")
    tgt = str(cfg["target_channel"]).strip()
    if not tgt.startswith("@"):
        die('target_channel must look like "@YOUR_CHANNEL" (with the @).')
    cfg["target_channel"] = tgt
    srcs = [normalize_source(s) for s in cfg["sources"] if str(s).strip()]
    srcs = [s for s in srcs if s]
    if not srcs or any(re.match(r"^source_channel_\d+$", s) for s in srcs):
        die("sources in config.json still has the sample names - put the real source channel usernames.")
    cfg["sources"] = srcs
    cfg["ad_keywords"] = list(cfg["ad_keywords"]) + list(cfg["extra_ad_keywords"])
    return cfg


def load_state(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            st = json.load(f)
        if isinstance(st, dict) and isinstance(st.get("channels"), dict):
            return st
    except (OSError, ValueError):
        pass
    return {"channels": {}}


class SubState(dict):
    """The state of one extra destination channel (a 'profile'). It lives inside the main state under
    state["dests"], and save_state() always writes the whole main state."""
    root = None
    root_cfg = None


def save_state(path, state):
    if isinstance(state, SubState) and state.root is not None:
        state = state.root
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=1)
    os.replace(tmp, path)


# ---- several destination channels: every destination is a separate profile (own sources, speed, words,
# history, on/off, reports). The first one (p1) is the original channel and keeps living in the main state. ----
MAX_DESTS = 10
TAG = [""]                                         # prefix of bot messages when more than one destination exists
_PCACHE = {}


def hub_of(cfg, state):
    """(main cfg, main state) whatever profile was passed."""
    if isinstance(state, SubState) and state.root is not None:
        return state.root_cfg, state.root
    return cfg, state


def dest_list(cfg0, root):
    out = []
    for d in root.get("dests", []):
        st = d.get("st")
        if not isinstance(st, SubState):
            st = SubState(st if isinstance(st, dict) else {"channels": {}})
            d["st"] = st
        st.root, st.root_cfg = root, cfg0
        out.append(d)
    return out


def dest_cfg(cfg0, d):
    c = _PCACHE.get(d["id"])
    if c is None or c[0] != d["target"] or c[2] is not cfg0:
        ci = dict(cfg0)
        base_ad = list(cfg0.get("_base_ad", cfg0["ad_keywords"]))
        ci.update(target_channel=d["target"], sources=[], _base_sources=[], _base_ad=base_ad, ad_keywords=list(base_ad),
                  _allow_empty=True, _pid=d["id"], watermark_text=d.get("wm", ""))
        c = _PCACHE[d["id"]] = (d["target"], ci, cfg0)
    return c[1]


def profiles(cfg0, root):
    """[(id, cfg, state)] - the first one is always the original destination."""
    out = [("p1", cfg0, root)]
    for d in dest_list(cfg0, root):
        out.append((d["id"], dest_cfg(cfg0, d), d["st"]))
    return out


def active_profile(cfg0, root):
    ps = profiles(cfg0, root)
    want = root.get("active")
    return next((p for p in ps if p[0] == want), ps[0])


def set_tag(cfg, state):
    cfg0, root = hub_of(cfg, state)
    TAG[0] = ("🎯 %s" % cfg["target_channel"]) if root.get("dests") else ""


# --------------------------------------------------------------------------- #
# network
# --------------------------------------------------------------------------- #
def encode_multipart(fields, files):
    boundary = uuid.uuid4().hex
    parts = []
    for k, v in fields.items():
        if not isinstance(v, str):
            v = json.dumps(v, ensure_ascii=False)
        parts.append(('--%s\r\nContent-Disposition: form-data; name="%s"\r\n\r\n%s\r\n'
                      % (boundary, k, v)).encode("utf-8"))
    for k, (fname, data, ctype) in files.items():
        head = ('--%s\r\nContent-Disposition: form-data; name="%s"; filename="%s"\r\n'
                'Content-Type: %s\r\n\r\n' % (boundary, k, fname, ctype))
        parts.append(head.encode("utf-8"))
        parts.append(data)
        parts.append(b"\r\n")
    parts.append(("--%s--\r\n" % boundary).encode("utf-8"))
    return b"".join(parts), "multipart/form-data; boundary=" + boundary


class Net:
    def __init__(self, cfg):
        handlers = []
        if cfg["proxy"]:
            handlers.append(urllib.request.ProxyHandler(
                {"http": cfg["proxy"], "https": cfg["proxy"]}))
        self.opener = urllib.request.build_opener(*handlers)
        self.token = cfg["bot_token"]
        self.api_base = cfg["api_base"].rstrip("/")

    def tg_url(self, url):
        """tgfile:<file_id> = a file of a message sent to the bot -> its download link."""
        if not url.startswith("tgfile:"):
            return url
        try:
            info = self.api("getFile", {"file_id": url[7:]})
        except ApiError as e:
            raise NetError("Telegram will not give this file (%s)" % e.desc)
        return "%s/file/bot%s/%s" % (self.api_base, self.token, info["file_path"])

    def get(self, url, binary=False, timeout=40):
        url = self.tg_url(url)
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        try:
            with self.opener.open(req, timeout=timeout) as r:
                data = r.read()
        except (urllib.error.URLError, OSError) as e:
            raise NetError(str(e))
        return data if binary else data.decode("utf-8", "replace")

    sent = []

    def forget_and_delete_sent(self):
        """Delete everything of the current post that already reached the channel."""
        for chat, mid in self.sent:
            try:
                self.api("deleteMessage", {"chat_id": chat, "message_id": mid})
            except (ApiError, NetError) as e:
                log.warning("could not delete a half-sent message: %s", getattr(e, "desc", e))
        self.sent = []

    def get_range(self, url, nbytes):
        """First nbytes of a file plus its total size (for duplicate detection)."""
        if url.startswith("tgfile:"):
            data = self.get(url, binary=True, timeout=180)
            return data[:nbytes], len(data)
        req = urllib.request.Request(url, headers={"User-Agent": UA, "Range": "bytes=0-%d" % (nbytes - 1)})
        try:
            with self.opener.open(req, timeout=40) as r:
                data = r.read(nbytes)
                cr = r.headers.get("Content-Range", "")
                total = int(cr.rsplit("/", 1)[1]) if "/" in cr and cr.rsplit("/", 1)[1].isdigit() \
                    else int(r.headers.get("Content-Length", len(data)))
        except (urllib.error.URLError, OSError) as e:
            raise NetError(str(e))
        return data, total

    def api(self, method, payload=None, files=None):
        url = "%s/bot%s/%s" % (self.api_base, self.token, method)
        if files:
            body, ctype = encode_multipart(payload or {}, files)
        else:
            body, ctype = json.dumps(payload or {}).encode("utf-8"), "application/json"
        last = None
        for attempt in range(4):
            req = urllib.request.Request(
                url, data=body, headers={"Content-Type": ctype, "User-Agent": UA})
            try:
                with self.opener.open(req, timeout=120) as r:
                    data = json.loads(r.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                try:
                    data = json.loads(e.read().decode("utf-8"))
                except Exception:
                    data = {"ok": False, "description": "HTTP %s" % e.code,
                            "error_code": e.code}
            except (urllib.error.URLError, OSError, ValueError) as e:
                last = e
                time.sleep(5 * (attempt + 1))
                continue
            if data.get("ok"):
                res = data.get("result")
                if method.startswith("send") and payload and "chat_id" in payload:
                    for r in (res if isinstance(res, list) else [res]):
                        if isinstance(r, dict) and r.get("message_id"):
                            self.sent.append((payload["chat_id"], r["message_id"]))
                return res
            ra = (data.get("parameters") or {}).get("retry_after", 0)
            if data.get("error_code") == 429 and attempt < 3:
                log.info("Telegram asked to slow down, waiting %ss", ra + 1)
                time.sleep(min(ra + 1, 60))
                continue
            raise ApiError(data.get("description", "unknown error"),
                           data.get("error_code", 0), ra)
        raise NetError("cannot reach Telegram API (is your VPN on?): %s" % last)


# --------------------------------------------------------------------------- #
# reading the public channel page
# --------------------------------------------------------------------------- #
MSG_SPLIT = re.compile(r'<div class="tgme_widget_message_wrap')
TEXT_RE = re.compile(
    r'<div class="tgme_widget_message_text js-message_text[^"]*"[^>]*>(.*?)</div>', re.S)
MEDIA_RE = re.compile(
    r'tgme_widget_message_photo_wrap[^>]*?style="[^"]*?background-image:\s*url\(\s*[\'"]?([^\'")]+)[\'"]?\s*\)'
    r'|(<video\b[^>]*>)', re.S)
UNSUPPORTED = ("tgme_widget_message_poll",
               "tgme_widget_message_voice", "tgme_widget_message_document_wrap",
               "tgme_widget_message_sticker", "tgme_widget_message_tgsticker",
               "tgme_widget_message_location", "tgme_widget_message_contact",
               "tgme_widget_message_roundvideo")
UKIND = {"tgme_widget_message_poll": "نظرسنجی", "tgme_widget_message_voice": "ویس",
         "tgme_widget_message_document_wrap": "فایل یا سند (PDF، ZIP، APK و...)",
         "tgme_widget_message_sticker": "استیکر", "tgme_widget_message_tgsticker": "استیکر",
         "tgme_widget_message_location": "موقعیت مکانی", "tgme_widget_message_contact": "مخاطب",
         "tgme_widget_message_roundvideo": "ویدیوی گرد (video note)"}
EMOJI_RE = re.compile(r'<i class="emoji"[^>]*>\s*<b>(.*?)</b>\s*</i>', re.S)
INVITE_RE = re.compile(r"(?:t|telegram)\.me/(?:\+|joinchat/)", re.I)


PROXY_RE = re.compile(r'(?:[ \t]*[|•·–—][ \t]*)?<a\b[^>]*href="https?://t\.me/(?:proxy|socks)\?[^"]*"[^>]*>.*?</a>', re.S | re.I)


def strip_proxy_links(t):
    """Telegram proxy links ('| پروکسی' in footers) are not channels and not ads: drop them."""
    return PROXY_RE.sub("", t)


def parse_views(num, unit):
    try:
        v = float(num.replace(",", ""))
    except ValueError:
        return None
    return int(v * {"k": 1e3, "m": 1e6}.get(unit.lower(), 1))


def parse_ts(s):
    try:
        d = datetime.datetime.fromisoformat(s.strip().replace("Z", "+00:00"))
        if d.tzinfo is None:
            d = d.replace(tzinfo=datetime.timezone.utc)
        return int(d.timestamp())
    except ValueError:
        return None


VIDEO_META = {}        # video file url -> {"thumb": cover url, "w":, "h":, "d": seconds}


def remember_videos(chunk):
    for seg in chunk.split("tgme_widget_message_video_player")[1:]:
        vm = re.search(r"<video\b[^>]*>", seg)
        sm = re.search(r'\bsrc="([^"]+)"', vm.group(0)) if vm else None
        if not sm:
            continue
        meta = {}
        th = re.search(r"tgme_widget_message_video_thumb[^>]*?background-image:\s*url\(\s*['\"]?([^'\")]+)", seg)
        if th:
            meta["thumb"] = html.unescape(th.group(1))
        for k, a in (("w", "width"), ("h", "height")):
            am = re.search(r'\b%s="(\d+)"' % a, vm.group(0))
            if am:
                meta[k] = int(am.group(1))
        dm = re.search(r'message_video_duration[^>]*>\s*(?:(\d+):)?(\d+):(\d+)\s*<', seg)
        if dm:
            meta["d"] = int(dm.group(1) or 0) * 3600 + int(dm.group(2)) * 60 + int(dm.group(3))
        if meta:
            if len(VIDEO_META) > 600:
                VIDEO_META.clear()
            VIDEO_META[html.unescape(sm.group(1))] = meta


def parse_page(page):
    posts = []
    for chunk in MSG_SPLIT.split(page)[1:]:
        m = re.search(r'data-post="[^"/]+/(\d+)"', chunk)
        if not m:
            continue
        tm = TEXT_RE.search(chunk)
        remember_videos(chunk)
        media = []
        for mm in MEDIA_RE.finditer(chunk):
            if mm.group(1):
                media.append(("photo", html.unescape(mm.group(1))))
            elif mm.group(2):
                tag = mm.group(2)
                cm = re.search(r'\bclass="([^"]*)"', tag)
                sm = re.search(r'\bsrc="([^"]+)"', tag)
                cls = cm.group(1) if cm else ""
                # real post video only: not the blurred copy, not animated custom emoji
                if sm and "js-message_video" in cls and "blured" not in cls:
                    media.append(("video", html.unescape(sm.group(1))))
        seen, uniq = set(), []
        for item in media:
            if item[1] not in seen:
                seen.add(item[1])
                uniq.append(item)
        vm = re.search(r'tgme_widget_message_views">\s*([\d.,]+)\s*([KkMm]?)\s*<', chunk)
        tmm = re.search(r'<time[^>]*\bdatetime="([^"]+)"', chunk)
        posts.append({
            "id": int(m.group(1)),
            "views": parse_views(vm.group(1), vm.group(2)) if vm else None,
            "ts": parse_ts(tmm.group(1)) if tmm else None,
            "text_html": strip_proxy_links(tm.group(1)) if tm else "",
            "media": uniq,
            "forwarded": "tgme_widget_message_forwarded_from" in chunk,
            "reply": "tgme_widget_message_reply" in chunk,
            "ukind": next((UKIND[u] for u in UNSUPPORTED if u in chunk), None)
                     or ("ویدیو (لینک مستقیم فایل در صفحه‌ی منبع نبود؛ معمولاً ویدیوی خیلی بزرگ)"
                         if "tgme_widget_message_video_wrap" in chunk and not any(k == "video" for k, _ in uniq)
                         else "عکس (لینک مستقیم فایل در صفحه‌ی منبع نبود)"),
            "unsupported": any(u in chunk for u in UNSUPPORTED) or (
                ("tgme_widget_message_video_wrap" in chunk
                 and not any(k == "video" for k, _ in uniq))
                or ("tgme_widget_message_photo_wrap" in chunk
                    and not any(k == "photo" for k, _ in uniq))),
        })
    posts.sort(key=lambda p: p["id"])
    return posts


# --------------------------------------------------------------------------- #
# rewriting the caption
# --------------------------------------------------------------------------- #
TME_RE = re.compile(
    r"(?<![\w.])(?:https?://)?(?:www\.)?(?:t|telegram)\.me/[A-Za-z0-9_+/\-]+(?:\?[^\s<]*)?", re.I)
TME_HREF_RE = re.compile(r"^(?:https?:)?//(?:www\.)?(?:t|telegram)\.me/", re.I)
MENTION_RE = re.compile(r"(?<![\w@./])@([A-Za-z][A-Za-z0-9_]{3,31})(?!\w)")


SRC = "\ue000"            # placeholder for "the source channel's ID/link" while converting
CTA_RE = re.compile(r"join|follow|subscribe|عضو|دنبال|فالو|کانال\s*(?:ما|رسمی)|ما\s*را|ارتباط|پیج|ادمین|admin", re.I)
KEEP_END = ".:؟?!،,)»\"'"


HASHTAG_LINE = re.compile(r"^[\s\u200c\u200f]*(?:#[\w\u200c]+[\s\u200c\u200f]*)+$")


def drop_hashtag_lines(t):
    """A line that is nothing but hashtags (#Meti) says nothing without its channel: remove it.
    Hashtags inside a real sentence stay."""
    return "\n".join(l for l in t.split("\n") if not HASHTAG_LINE.match(re.sub(r"<[^>]+>", "", l)))


def drop_source_lines(t, own):
    """The source channel's ID is removed together with the decoration around it:
    a line that is only an ID footer (emoji, '| name', ...) disappears completely; an ID glued
    to the end of a real sentence is cut off and the sentence stays. Your ID is added by the
    caller on its own line."""
    out = []
    for line in t.split("\n"):
        if SRC not in line:
            out.append(line)
            continue
        pre, _, post = line.partition(SRC)
        post_plain = post.replace(SRC, "")
        post_words = re.search(r"\w", re.sub(r"<[^>]+>", "", post_plain))
        starts_sep = re.match(r"\s*(?:<[^>]+>)*\s*[|•·–—\-/]", post_plain)
        if post_words and not starts_sep:      # real text follows: ID in the middle of a sentence
            out.append(line.replace(SRC, own))
            continue
        pre_plain = re.sub(r"<[^>]+>", "", pre)
        if not re.search(r"\w", pre_plain):   # nothing but decoration before the ID: drop the line
            k = len(out)
            while k and not out[k - 1].strip():
                k -= 1
            if k:                              # ... and a short "Join Us"-style line just above it
                prev = re.sub(r"<[^>]+>", "", out[k - 1])
                if CTA_RE.search(prev) and len(re.findall(r"\w+", prev)) <= 6:
                    del out[k - 1:]
            continue
        if CTA_RE.search(pre_plain) or (len(re.findall(r"\w+", pre_plain)) <= 3 and any(x.strip() for x in out)):
            continue                           # "Join Us @source", "عضو شوید @source": a footer line
        # glued to a sentence: keep the sentence, drop trailing emoji/symbols but keep . : ! ? etc.
        keep = pre
        while keep and not re.search(r"[\w" + re.escape(KEEP_END) + r">]$", keep):
            keep = keep[:-1]
        out.append(keep.rstrip())
    return "\n".join(out)


def balance_tags(t):
    stack, out = [], []
    for m in re.finditer(r"<(/?)([a-z-]+)([^>]*)>|[^<]+|<", t):
        if m.group(2) is None:
            out.append(m.group(0))
            continue
        close, name = m.group(1), m.group(2)
        if not close:
            stack.append(name)
            out.append(m.group(0))
        elif name in stack:
            while stack and stack[-1] != name:
                out.append("</%s>" % stack.pop())
            stack.pop()
            out.append(m.group(0))
    while stack:
        out.append("</%s>" % stack.pop())
    return "".join(out)


class Rules:
    def __init__(self, cfg):
        self.own = cfg["target_channel"]
        self.keep = {self.own.lower()}
        for k in cfg["keep_mentions"]:
            self.keep.add("@" + str(k).lstrip("@").lower())
        self.repl = [(a, b) for a, b in cfg["replacements"]]
        self.strip_links = cfg["strip_all_links"]

    def text(self, s):
        for a, b in self.repl:
            s = s.replace(a, b)
        s = TME_RE.sub(SRC, s)
        return MENTION_RE.sub(
            lambda m: m.group(0) if m.group(0).lower() in self.keep else SRC, s)

    def link(self, href, inner):
        if TME_HREF_RE.match(href):
            return SRC
        if self.strip_links or not re.match(r"https?://", href, re.I):
            return inner
        return '<a href="%s">%s</a>' % (html.escape(href, quote=True), inner)


class Converter(HTMLParser):
    """Turns the channel's HTML into the small HTML subset the Bot API accepts."""
    ALLOWED = {"b": "b", "strong": "b", "i": "i", "em": "i", "u": "u", "ins": "u",
               "s": "s", "strike": "s", "del": "s", "code": "code", "pre": "pre",
               "tg-spoiler": "tg-spoiler"}

    def __init__(self, rules):
        HTMLParser.__init__(self, convert_charrefs=True)
        self.rules = rules
        self.bufs = [[]]
        self.frames = []

    def handle_starttag(self, tag, attrs):
        if tag == "br":
            self.bufs[-1].append("\n")
        elif tag in self.ALLOWED or tag == "a":
            self.frames.append((tag, dict(attrs)))
            self.bufs.append([])

    def handle_startendtag(self, tag, attrs):
        if tag == "br":
            self.bufs[-1].append("\n")

    def _close(self):
        tag, attrs = self.frames.pop()
        inner = "".join(self.bufs.pop())
        if not inner.strip():
            out = inner
        elif tag == "a":
            out = self.rules.link(attrs.get("href") or "", inner)
        else:
            t = self.ALLOWED[tag]
            out = "<%s>%s</%s>" % (t, inner, t)
        self.bufs[-1].append(out)

    def handle_endtag(self, tag):
        if self.frames and self.frames[-1][0] == tag:
            self._close()

    def handle_data(self, data):
        self.bufs[-1].append(html.escape(self.rules.text(data), quote=False))

    def result(self):
        while self.frames:
            self._close()
        return "".join(self.bufs[0])


def build_text(cfg, rules, raw_html):
    raw_html = EMOJI_RE.sub(r"\1", raw_html)
    conv = Converter(rules)
    conv.feed(raw_html)
    conv.close()
    t = conv.result()
    t = balance_tags(drop_hashtag_lines(drop_source_lines(t, rules.own)))
    t = re.sub(r"[ \t]+\n", "\n", t)
    t = re.sub(r"\n{3,}", "\n\n", t).strip()
    # some sources start every post with a red dot: drop it (also when it sits inside a leading <b>/<i> tag)
    t = re.sub(r"^((?:<[^>]+>\s*)*)(?:\U0001F534\ufe0f?[ \t\u200c\u200f]*)+", r"\1", t).strip()
    if cfg["add_footer"] and rules.own.lower() not in plain(t).lower():
        t = (t + "\n\n" + rules.own) if t else rules.own
    return t


def other_channels(cfg, post):
    """Usernames mentioned in the post (as @name or t.me/name) that are neither the
    source channel(s) being copied, nor your channel, nor listed in keep_mentions."""
    allowed = {cfg["target_channel"].lstrip("@").lower()}
    allowed |= {x.lower() for x in cfg["sources"]}
    allowed |= {str(k).lstrip("@").lower() for k in cfg["keep_mentions"]}
    found = set()
    raw = post["text_html"]
    text = plain(raw)
    for m in MENTION_RE.finditer(text):
        found.add(m.group(1).lower())
    for src in [text] + [html.unescape(h) for h in re.findall(r'href="([^"]+)"', raw)]:
        for m in re.finditer(r"(?<![\w.])(?:https?://)?(?:www\.)?(?:t|telegram)\.me/([A-Za-z0-9_]{4,})", src, re.I):
            found.add(m.group(1).lower())
    return sorted(u for u in found if u not in allowed and u not in ("s", "joinchat", "proxy", "socks"))


# --------------------------------------------------------------------------- #
# duplicate detection (the source channels copy from each other)
# --------------------------------------------------------------------------- #
def norm_for_dedupe(text_html, own):
    t = plain(text_html).lower().replace(own.lower(), " ")
    t = re.sub(r"https?://\S+", " ", t)
    t = re.sub(r"@\w+", " ", t)
    t = t.replace("ي", "ی").replace("ك", "ک").replace("ة", "ه").replace("\u200c", " ").replace("\u200f", " ")
    t = re.sub(r"[\u064b-\u065f\u0670\u0640]", "", t)
    t = re.sub(r"[^\w\s]|_", " ", t)
    return re.sub(r"\s+", " ", t).strip()


def text_fp(norm):
    words = norm.split()
    fp = {}
    if len(norm) >= 25:
        fp["x"] = hashlib.sha1(norm.encode("utf-8")).hexdigest()[:12]
    if len(words) >= 8:
        sh = {hashlib.sha1(" ".join(words[i:i + 3]).encode("utf-8")).hexdigest()[:8]
              for i in range(len(words) - 2)}
        fp["h"] = sorted(sh)[:80]
    cw = {w for w in words if len(w) >= 3}          # content words, order ignored (same news, other wording)
    if len(cw) >= 7:
        fp["w"] = sorted(hashlib.sha1(w.encode("utf-8")).hexdigest()[:8] for w in cw)[:80]
    return fp


def jaccard(a, b):
    a, b = set(a), set(b)
    return len(a & b) / float(len(a | b)) if a and b else 0.0


def find_dup_why(fp, entries):
    """(the earlier post it repeats, how we know) or (None, None)."""
    for e in entries:
        if fp.get("x") and fp["x"] == e.get("x"):
            return e, "متن دقیقاً یکسان است"
        if fp.get("h") and e.get("h") and jaccard(fp["h"], e["h"]) >= 0.8:
            return e, "متن تقریباً یکسان است"
        if fp.get("w") and e.get("w"):
            a, b = set(fp["w"]), set(e["w"])
            inter = len(a & b)
            if inter >= 6 and (inter / float(len(a | b)) >= 0.55
                               or (min(len(a), len(b)) >= 8 and inter / float(min(len(a), len(b))) >= 0.85)):
                return e, "همان خبر است با جمله‌بندی دیگر (کلمه‌های اصلی یکی است)"
        if fp.get("m") and set(fp["m"]) & set(e.get("m", [])):
            return e, "همان عکس یا ویدیو است"
        if fp.get("p") and e.get("p") and (fp.get("man") or e.get("man")):
            # a picture you sent by hand: the same picture in another size still counts as a duplicate
            if any(hamming(a, b) <= 3 for a in fp["p"] for b in e["p"]):
                return e, "همان عکس است با اندازه‌ی دیگر"
    return None, None


def find_dup(fp, entries):
    return find_dup_why(fp, entries)[0]


def explain_skip(reason, post):
    """Reason of skip_reason() in plain Persian, as precisely as possible."""
    m = re.match(r"ad (?:keyword|word) '(.*)'", reason)
    if m:
        return "کلمه‌ی تبلیغاتی «%s» دارد (اگر نمی‌خواهی جلویش را بگیرد: /unban %s)" % (m.group(1), m.group(1))
    m = re.match(r"link to blocked site (.*)", reason)
    if m:
        return "لینک سایت ممنوع‌شده دارد: %s" % m.group(1)
    m = re.match(r"contains a link to a site/app \((.*)\)", reason)
    if m:
        return "آدرس سایت یا اپ دارد: %s (پست‌های دارای آدرس سایت ارسال نمی‌شوند)" % m.group(1)
    m = re.match(r"mentions another channel/bot \(@(.*)\)", reason)
    if m:
        return "به کانال یا ربات دیگری اشاره می‌کند: @%s" % m.group(1)
    if reason.startswith("contains a channel invite"):
        return "لینک دعوت به کانال یا گروه دارد"
    if reason == "it is a reply":
        return "ریپلای به پست دیگری است"
    if reason == "it is forwarded":
        return "فورواردی از کانال دیگر است"
    if reason.startswith("media type"):
        return "رسانه‌ی غیرقابل‌کپی دارد: %s" % (post.get("ukind") or "نامشخص")
    if reason == "empty":
        return "پست خالی است (نه متن دارد نه عکس و ویدیو)"
    return reason


def dhash(data):
    """64-bit 'looks like' hash: the same picture in another size/quality gives (almost) the same value."""
    im = Image.open(io.BytesIO(data))
    im.load()
    im = im.convert("L").resize((9, 8))
    px = list(im.getdata())
    bits = 0
    for r in range(8):
        for c in range(8):
            bits = (bits << 1) | (1 if px[r * 9 + c] > px[r * 9 + c + 1] else 0)
    return "%016x" % bits


def hamming(a, b):
    return bin(int(a, 16) ^ int(b, 16)).count("1")


def media_info(net, media):
    """(exact file hashes, look-alike hashes of the photos) of the first 3 media files."""
    exact, look = [], []
    for kind, url in media[:3]:
        try:
            if kind == "photo":
                data = net.get(url, binary=True, timeout=30)
                exact.append(hashlib.sha1(data).hexdigest()[:12])
                try:
                    look.append(dhash(data))
                except Exception:
                    pass
            else:
                data, total = net.get_range(url, 262144)
                exact.append(hashlib.sha1(data + str(total).encode()).hexdigest()[:12])
        except Exception:
            pass
    return exact, look


def media_hashes(net, media):
    return media_info(net, media)[0]


def skip_reason(cfg, post):
    text = plain(post["text_html"]).lower()
    if post["reply"] and cfg["skip_replies"]:
        return "it is a reply"
    if post["forwarded"] and cfg["skip_forwarded"]:
        return "it is forwarded"
    for kw in cfg["ad_keywords"]:
        if kw.lower() in text:
            return "ad keyword '%s'" % kw
    for w in cfg["ad_words"]:
        if re.search(r"(?<!\w)%s(?!\w)" % re.escape(w.lower()), text):
            return "ad word '%s'" % w
    hosts = set()
    for href in re.findall(r'href="([^"]+)"', post["text_html"]):
        href = html.unescape(href)
        mh = re.match(r"https?://([^/:?#]+)", href, re.I)
        if mh and not TME_HREF_RE.match(href):
            h = mh.group(1).lower()
            hosts.add(h[4:] if h.startswith("www.") else h)
    for mh in re.finditer(r"(?<![\w@.])((?:[a-z0-9-]+\.)+(?:com|net|org|ir|io|bet|xyz|app|info|"
                          r"site|online|top|vip|live|club|win|apk))(?![\w.])", text):
        hosts.add(mh.group(1))
    for h in hosts:
        if any(h == d or h.endswith("." + d) for d in cfg["blocked_domains"]):
            return "link to blocked site %s" % h
    if cfg["skip_posts_with_links"]:
        for h in hosts:
            if not any(h == d or h.endswith("." + d) for d in cfg["allowed_domains"]):
                return "contains a link to a site/app (%s)" % h
    if cfg["skip_other_mentions"]:
        others = other_channels(cfg, post)
        if others:
            return "mentions another channel/bot (@%s)" % others[0]
    if cfg["skip_invite_links"] and INVITE_RE.search(post["text_html"]):
        return "contains a channel invite link"
    if post["unsupported"] and cfg["incomplete_post"] == "skip":
        return "media type cannot be copied (voice/file/poll/sticker/large video)"
    if not post["text_html"].strip() and not post["media"]:
        return "empty"
    return None


# --------------------------------------------------------------------------- #
# publishing
# --------------------------------------------------------------------------- #
def call_html(net, method, payload, files=None):
    try:
        return net.api(method, payload, files)
    except ApiError as e:
        if "parse entities" in e.desc.lower() and payload.get("parse_mode"):
            p = dict(payload)
            p.pop("parse_mode")
            for k in ("caption", "text"):
                if k in p:
                    p[k] = plain(p[k])
            return net.api(method, p, files)
        raise


def split_text(t, limit=4000):
    if len(t) <= limit:
        return [t]
    chunks, cur = [], ""
    for line in t.split("\n"):
        while len(line) > limit:
            if cur:
                chunks.append(cur)
                cur = ""
            chunks.append(line[:limit])
            line = line[limit:]
        if len(cur) + len(line) + 1 > limit:
            chunks.append(cur)
            cur = line
        else:
            cur = (cur + "\n" + line) if cur else line
    if cur:
        chunks.append(cur)
    return chunks


def send_text(net, cfg, t):
    for part in split_text(t):
        call_html(net, "sendMessage", {
            "chat_id": cfg["target_channel"], "text": part, "parse_mode": "HTML",
            "disable_web_page_preview": not cfg["link_previews"]})
        time.sleep(1)


def wm_text(cfg):
    return cfg.get("watermark_text") or "t.me/" + cfg["target_channel"].lstrip("@")


def wm_on(cfg):
    return bool(cfg.get("watermark")) and Image is not None and not cfg.get("_no_wm")


def _font(size):
    for p in ("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf",
              "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
              "DejaVuSans-Bold.ttf", "arialbd.ttf"):
        try:
            return ImageFont.truetype(p, size)
        except Exception:
            pass
    try:
        return ImageFont.load_default(size)
    except Exception:
        return ImageFont.load_default()


def watermark_photo(data, text):
    """Small faint link on a random spot (4 corners, top-middle, bottom-middle): semi-transparent dark pill, white text."""
    im = Image.open(io.BytesIO(data))
    im.load()
    im = im.convert("RGBA")
    w, h = im.size
    if min(w, h) < 200:
        return data
    size = max(10, int(min(w, h) * 0.022))
    font = _font(size)
    ov = Image.new("RGBA", im.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(ov)
    b = d.textbbox((0, 0), text, font=font)
    tw, th = b[2] - b[0], b[3] - b[1]
    padx, pady, m = int(size * 0.55), int(size * 0.35), int(size * 0.7)
    bw, bh = tw + 2 * padx, th + 2 * pady
    where = random.choice(["tl", "tc", "tr", "bl", "bc", "br"])
    x0 = m if where[1] == "l" else (w - m - bw if where[1] == "r" else (w - bw) // 2)
    y0 = m if where[0] == "t" else h - m - bh
    x1, y1 = x0 + bw, y0 + bh
    d.rounded_rectangle([x0, y0, x1, y1], radius=int(size * 0.5), fill=(0, 0, 0, 50))
    d.text((x0 + padx - b[0], y0 + pady - b[1]), text, font=font, fill=(255, 255, 255, 150))
    out = Image.alpha_composite(im, ov).convert("RGB")
    buf = io.BytesIO()
    out.save(buf, "JPEG", quality=92, optimize=True)
    return buf.getvalue()


def marked_photo(net, cfg, url):
    """Download a photo and return its watermarked bytes, or None if that is not possible."""
    if not wm_on(cfg):
        return None
    try:
        return watermark_photo(net.get(url, binary=True, timeout=60), wm_text(cfg))
    except Exception as e:
        log.info("could not put the ID on a photo (%s) - sending it as it is", e)
        return None


def video_cover(net, url):
    """(extra fields, {name: file}) for a video of a source channel: its cover picture, size, length.
    Without them Telegram often shows a black box instead of a preview."""
    meta = VIDEO_META.get(url)
    if not meta:
        return {}, {}
    fields = {k: meta[k] for k in ("w", "h", "d") if k in meta}
    fields = {"width": fields.get("w"), "height": fields.get("h"), "duration": fields.get("d")}
    fields = {k: v for k, v in fields.items() if v}
    files = {}
    if meta.get("thumb"):
        try:
            data = net.get(meta["thumb"], binary=True, timeout=30)
            try:                                     # Telegram wants a JPEG, at most 320 px and 200 KB
                im = Image.open(io.BytesIO(data))
                im.load()
                im = im.convert("RGB")
                im.thumbnail((320, 320))
                buf = io.BytesIO()
                im.save(buf, "JPEG", quality=80)
                data = buf.getvalue()
            except Exception:
                pass
            if 200 < len(data) <= 200 * 1024:
                files["thumb"] = ("thumb.jpg", data, "image/jpeg")
        except Exception:
            pass
    return fields, files


def send_single(net, cfg, kind, url, caption):
    if kind == "video" and not url.startswith("tgfile:"):
        fields, tfiles = video_cover(net, url)
        if tfiles:                                   # upload the video together with its cover
            try:
                data = net.get(url, binary=True, timeout=180)
                if len(data) <= MAX_UPLOAD:
                    payload = {"chat_id": cfg["target_channel"], "supports_streaming": True,
                               "thumbnail": "attach://thumb"}
                    payload.update(fields)
                    if caption:
                        payload["caption"] = caption
                        payload["parse_mode"] = "HTML"
                    files = dict(tfiles, video=("video.mp4", data, "video/mp4"))
                    return call_html(net, "sendVideo", payload, files=files)
            except (NetError, ApiError) as e:
                log.info("video with cover failed (%s) - sending it the plain way", getattr(e, "desc", e))
    method = "sendPhoto" if kind == "photo" else "sendVideo"
    ref = url[7:] if url.startswith("tgfile:") else url      # a file id is sent as it is, no download
    payload = {"chat_id": cfg["target_channel"], kind: ref}
    if kind == "video":
        payload["supports_streaming"] = True
    if caption:
        payload["caption"] = caption
        payload["parse_mode"] = "HTML"
    if kind == "photo":
        data = marked_photo(net, cfg, url)
        if data:
            payload.pop(kind)
            try:
                return call_html(net, method, payload, files={kind: ("photo.jpg", data, "image/jpeg")})
            except ApiError as e:
                log.info("marked photo refused (%s) - sending the original", e.desc)
                payload[kind] = ref
    try:
        return call_html(net, method, payload)
    except ApiError as e:
        log.info("sending by link failed (%s) - uploading the file itself", e.desc)
    data = net.get(url, binary=True, timeout=180)
    if len(data) > MAX_UPLOAD:
        raise ApiError("file is bigger than the 50 MB bot limit")
    payload.pop(kind)
    fname, ctype = ("photo.jpg", "image/jpeg") if kind == "photo" else ("video.mp4", "video/mp4")
    return call_html(net, method, payload, files={kind: (fname, data, ctype)})


def send_group(net, cfg, media, caption):
    """Albums are always uploaded as files and sent as ONE album - never split into single
    messages (Telegram refuses video links, so the files are downloaded first)."""
    for i in range(0, len(media), 10):
        chunk = media[i:i + 10]
        cap = caption if i == 0 else ""
        if len(chunk) == 1:
            send_single(net, cfg, chunk[0][0], chunk[0][1], cap)
            continue
        items, files = [], {}
        for j, (kind, url) in enumerate(chunk):
            if kind == "video" and url.startswith("tgfile:"):     # a video you sent: use its file id
                it = {"type": "video", "media": url[7:], "supports_streaming": True}
                if cap and j == 0:
                    it["caption"] = cap
                    it["parse_mode"] = "HTML"
                items.append(it)
                continue
            data = marked_photo(net, cfg, url) if kind == "photo" else None
            if data is None:
                data = net.get(url, binary=True, timeout=180)
            if len(data) > MAX_UPLOAD:
                raise ApiError("file is bigger than the 50 MB bot limit")
            name = "m%d" % j
            files[name] = (name + (".jpg" if kind == "photo" else ".mp4"), data,
                           "image/jpeg" if kind == "photo" else "video/mp4")
            it = {"type": kind, "media": "attach://" + name}
            if kind == "video":
                it["supports_streaming"] = True
                fields, tfiles = video_cover(net, url)
                if tfiles:
                    files["t%d" % j] = tfiles["thumb"]
                    it["thumbnail"] = "attach://t%d" % j
                it.update(fields)
            if cap and j == 0:
                it["caption"] = cap
                it["parse_mode"] = "HTML"
            items.append(it)
        try:
            net.api("sendMediaGroup", {"chat_id": cfg["target_channel"], "media": items}, files)
        except ApiError as e:
            if "parse entities" in e.desc.lower() and cap:
                for it in items:
                    it.pop("parse_mode", None)
                    if "caption" in it:
                        it["caption"] = plain(it["caption"])
                net.api("sendMediaGroup", {"chat_id": cfg["target_channel"], "media": items}, files)
            else:
                raise
        time.sleep(1)


def deliver(net, cfg, post, text):
    net.sent = []
    try:
        _deliver(net, cfg, post, text)
    except BaseException:
        net.forget_and_delete_sent()      # never leave half of a post in the channel
        raise
    net.last_sent = list(net.sent)
    net.sent = []


def _deliver(net, cfg, post, text):
    media = post["media"]
    if not media:
        if not text:
            raise Skip("nothing to send")
        send_text(net, cfg, text)
        return
    cap = text if vis_len(text) <= 1024 else ""
    rest = "" if cap else text
    try:
        if len(media) == 1:
            send_single(net, cfg, media[0][0], media[0][1], cap)
        else:
            send_group(net, cfg, media, cap)
    except ApiError as e:
        if cfg["incomplete_post"] == "text_only" and text:
            log.info("media failed (%s) - sending text only", e.desc)
            send_text(net, cfg, text)
            return
        raise Skip("media could not be copied: %s" % e.desc)
    if rest:
        send_text(net, cfg, rest)


# --------------------------------------------------------------------------- #
# main loop
# --------------------------------------------------------------------------- #
def run_cycle(cfg, net, rules, state, state_path, dry):
    fails = run_cycle.fails
    for name in cfg["sources"]:
        # state keys are hashed, and in the cloud (public GitHub logs) names are hidden
        key = hashlib.sha1(name.lower().encode("utf-8")).hexdigest()[:10]
        label = key if IN_CLOUD else name
        try:
            page = net.get(cfg["web_base"] + name)
        except NetError as e:
            log.warning("[%s] cannot open channel page: %s", label, e)
            continue
        posts = parse_page(page)
        if not posts:
            log.warning("[%s] no posts found - is the username right and the channel public?", label)
            continue
        st = state["channels"].setdefault(key, {})
        if "last_id" not in st:
            n = max(cfg["initial_posts"], 3 if dry else 0)
            sel = posts[-n:] if n > 0 else []
            st["last_id"] = (sel[0]["id"] - 1) if sel else posts[-1]["id"]
            log.info("[%s] first run: starting after post %d", label, st["last_id"])
            if not dry:
                save_state(state_path, state)
        new = [p for p in posts if p["id"] > st["last_id"]]
        for p in new:
            tag = "%s/%d" % (label, p["id"])
            reason = skip_reason(cfg, p)
            if reason:
                log.info("[%s] skipped: %s", tag, reason)
            else:
                text = build_text(cfg, rules, p["text_html"])
                if dry:
                    log.info("[%s] WOULD POST (%d media):\n%s\n----", tag, len(p["media"]), text)
                else:
                    try:
                        deliver(net, cfg, p, text)
                        log.info("[%s] posted", tag)
                        time.sleep(cfg["delay_between_posts"])
                    except Skip as e:
                        log.warning("[%s] skipped: %s", tag, e)
                    except NetError as e:
                        log.warning("[%s] network problem, will retry: %s", tag, e)
                        break
                    except ApiError as e:
                        fails[tag] = fails.get(tag, 0) + 1
                        log.error("[%s] Telegram refused (%s) attempt %d/3", tag, e.desc, fails[tag])
                        if fails[tag] < 3:
                            break
                        log.error("[%s] giving up on this post", tag)
            if not dry:
                st["last_id"] = p["id"]
                save_state(state_path, state)


run_cycle.fails = {}

# --------------------------------------------------------------------------- #
# control from inside Telegram (on/off, review of suspected ads)
# --------------------------------------------------------------------------- #
BTN_OFF, BTN_ON, BTN_STATUS, BTN_REVIEW = "⏸ خاموش", "▶️ روشن", "📊 وضعیت", "🔍 مشکوک‌ها"
BTN_CR_ON, BTN_CR_OFF, BTN_CR_AUTO = "🚨 بحران روشن", "🛑 بحران خاموش", "🤖 بحران خودکار"
BTN_SP_NORMAL, BTN_SP_BOOST = "🐢 نرمال (۱ تا ۶ پست)", "🚀 بوست (۷ تا ۱۰ پست)"
BTN_SRC, BTN_BAN, BTN_HOURS, BTN_NOW = "📋 منبع‌ها", "🚫 کلمات ممنوع", "⏰ ساعت‌ها", "⚡ ارسال همین الان"
SEED_SOURCES = ["Daneshjoo", "FilmFarsiOrg", "Radiokocsher"]
BTN_SPEED, BTN_CRMENU, BTN_MORE = "🎚 سرعت ارسال", "🚨 بحران", "⚙️ بیشتر"
BTN_DEST = "🎯 مقصدها"
ALL_BTNS = {BTN_OFF, BTN_ON, BTN_STATUS, BTN_REVIEW, BTN_CR_ON, BTN_CR_OFF, BTN_CR_AUTO, BTN_SP_NORMAL, BTN_SP_BOOST,
            BTN_SRC, BTN_BAN, BTN_HOURS, BTN_NOW, BTN_SPEED, BTN_CRMENU, BTN_MORE, BTN_DEST}
HELP_TEXT = ("📖 راهنما\n"
             "• 📊 وضعیت: حال ربات و توضیح آخرین دور\n"
             "• ⚡ ارسال همین الان: یک دور فوری\n"
             "• ▶️ روشن / ⏸ خاموش: شروع و توقف ارسال\n"
             "• 🎚 سرعت ارسال: کم، متوسط، زیاد، دستی (بازه‌ی دلخواه) یا خودکار (فرمول ساعت و تعطیلی)\n"
             "• 🚨 بحران: روشن، خاموش یا خودکار\n"
             "• 📋 منبع‌ها: لیست کانال‌های مبدا؛ اضافه کردن: /add name ، حذف: /del name ، بی‌صدا: /mute name 3\n"
             "• ⚙️ بیشتر: کلمات ممنوع، ساعت‌های پربازدید، بررسی مشکوک‌ها\n"
             "• 🎯 مقصدها: چند کانال مقصد با منبع‌ها و تنظیمات جدا؛ /dest add @channel ، /dest use 2\n"
             "• هر پستی را برای ربات فوروارد کنید، همان لحظه در کانال گذاشته می‌شود.\n"
             "• دستورها: /speed low|mid|high|auto ، /manual 8-10 ، /menu")

# texts of older keyboards still work until the phone refreshes its buttons
OLD_CR = {"🚨 بحران: روشن": BTN_CR_ON, "🛑 بحران: خاموش": BTN_CR_OFF, "🤖 بحران: خودکار": BTN_CR_AUTO}
OLD_HOURS, OLD_REVIEW = "⏰ ساعت‌های پربازدید", "🔍 بررسی مشکوک‌ها (روشن/خاموش)"


def btn(t):
    return {"text": t}


MENU_KB = {"keyboard": [[btn(BTN_STATUS), btn(BTN_NOW)],
                        [btn(BTN_ON), btn(BTN_OFF)],
                        [btn(BTN_SPEED), btn(BTN_CRMENU)],
                        [btn(BTN_SRC), btn(BTN_DEST), btn(BTN_MORE)]],
           "resize_keyboard": True}      # not persistent: the keyboard icon next to the message box hides it



# ---------------------------------------------------------------------------- #
# posting speed: low / mid / high / manual range / automatic (hour and holiday table)
# ---------------------------------------------------------------------------- #
SPEED_FIXED = {"low": ("کم", 1, 2), "mid": ("متوسط", 2, 4), "high": ("زیاد", 6, 8)}
# automatic: posts per HOUR, by hour of the day (Iran time). W = normal days, H = Thursday noon..Friday evening
AUTO_W = [(0, 1, 4, 5), (1, 7, 0, 1), (7, 11, 3, 4), (11, 16, 2, 3), (16, 20, 3, 4), (20, 24, 4, 5)]
AUTO_H = [(0, 2, 6, 6), (2, 8, 0, 1), (8, 12, 4, 4), (12, 17, 4, 4), (17, 20, 4, 5), (20, 24, 6, 6)]
_DIG = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")


def speed_mode(state):
    m = state.get("speed")
    return m if m in ("low", "mid", "high", "manual", "auto") else "auto"      # older values: auto


def parse_range(text, top=15):
    """'8 تا 10', '8-10', '۸ الی ۱۰', '8' -> (8, 10) / (8, 8); None when there is no number."""
    t = (text or "").translate(_DIG)
    m = re.search(r"(\d{1,3})\s*(?:تا|الی|الي|to|[-–—~،,/]|\s)\s*(\d{1,3})", t) or re.search(r"(\d{1,3})", t)
    if not m:
        return None
    a = int(m.group(1))
    b = int(m.group(2)) if m.lastindex and m.lastindex >= 2 else a
    lo, hi = sorted((a, b))
    lo, hi = max(1, min(lo, top)), max(1, min(hi, top))
    return lo, hi


def auto_rate(cfg, now):
    """(low, high posts per hour, is_holiday, hour) wanted right now by the automatic formula."""
    lt = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60)
    wd, h = lt.tm_wday, lt.tm_hour                         # Monday = 0 ... Thursday = 3, Friday = 4
    holiday = (wd == 3 and h >= 12) or (wd == 4 and h < 20) or (wd == 4 and False)
    for a, b, lo, hi in (AUTO_H if holiday else AUTO_W):
        if a <= h < b:
            return lo, hi, holiday, h
    return 3, 4, holiday, h


def mean_gap(cfg, night):
    a, b = cfg["night_interval_minutes"] if night else cfg["interval_minutes"]
    return (float(a) + float(b)) / 2.0


def round_target(cfg, state, now):
    """(how many posts this round should end with, is it a quiet-night round, short description)."""
    mode = speed_mode(state)
    if mode in SPEED_FIXED:
        name, lo, hi = SPEED_FIXED[mode]
        return random.randint(lo, hi), False, "%s (%d تا %d پست در هر دور)" % (name, lo, hi)
    if mode == "manual":
        lo, hi = state.get("manual_range") or [2, 4]
        return random.randint(int(lo), int(hi)), False, "دستی (%d تا %d پست در هر دور)" % (lo, hi)
    lo, hi, holiday, h = auto_rate(cfg, now)
    night = hi <= 1
    x = random.uniform(lo, hi) * mean_gap(cfg, night) / 60.0
    n = int(x) + (1 if random.random() < x - int(x) else 0)
    if night:
        n = min(n, int(cfg["night_max_posts"]))
    return n, night, "خودکار (%s، ساعت %d: %s پست در ساعت)" % (
        "تعطیلی" if holiday else "روز عادی", h, ("%d تا %d" % (lo, hi)) if lo != hi else str(lo))


def _speed_line(cfg, state, now=None):
    now = now or time.time()
    mode = speed_mode(state)
    rounds = 1440.0 / mean_gap(cfg, False)
    if mode in SPEED_FIXED:
        name, lo, hi = SPEED_FIXED[mode]
        return "🎚 سرعت: %s (%d تا %d پست در هر دور)" % (name, lo, hi)
    if mode == "manual":
        lo, hi = state.get("manual_range") or [2, 4]
        return "🎚 سرعت: دستی (%d تا %d پست در هر دور)" % (lo, hi)
    lo, hi, holiday, h = auto_rate(cfg, now)
    return "🎚 سرعت: 🤖 خودکار — الان ساعت %d و %s: %s پست در ساعت" % (
        h, "زمان تعطیلی (پنجشنبه ظهر تا جمعه)" if holiday else "روز عادی", ("%d تا %d" % (lo, hi)) if lo != hi else str(lo))


def _speed_apply(cfg, state, mode, rng=None):
    """Switch the speed and return the full explanation for the owner."""
    rounds = 1440.0 / mean_gap(cfg, False)
    tail = ("\n\nهمه‌ی فیلترها مثل قبل اجرا می‌شوند (تبلیغ، لینک، فوروارد، ریپلای، تکراری...) و عدد بالا تعداد "
            "پستِ نهاییِ ارسال‌شده است. اگر بعد از فیلترها به این تعداد نرسید، ربات از هر کانال پست‌های کمی قدیمی‌تر "
            "را هم (تا %d پست آخر و حداکثر %d دقیقه قدیمی) بررسی می‌کند؛ باز هم اگر پست قابل‌ارسال کافی نبود، همان تعدادِ "
            "موجود را می‌فرستد. اگر «بحران» روشن باشد، قانون خودش اولویت دارد." % (
                int(cfg["widen_max_layers"]), int(cfg["widen_max_age_minutes"])))
    state["next_run_ts"] = 0                          # start with the new speed in the next loop
    if mode in SPEED_FIXED:
        name, lo, hi = SPEED_FIXED[mode]
        state["speed"] = mode
        return ("%s حالت «%s» روشن شد.\nاز دور بعدی (همین حالا شروع می‌شود) هر دور %d تا %d پست می‌گذارم. دورها هر ۳۰ تا ۴۰ "
                "دقیقه‌اند (حدود %d دور در شبانه‌روز)، یعنی اگر پست قابل‌ارسال کافی باشد حدود %d تا %d پست در روز." % (
                    {"low": "🐢", "mid": "⚖️", "high": "🚀"}[mode], name, lo, hi, rounds, lo * rounds, hi * rounds) + tail)
    if mode == "manual":
        lo, hi = rng
        state["speed"] = "manual"
        state["manual_range"] = [lo, hi]
        state.pop("await_manual", None)
        return ("✏️ حالت «دستی» روشن شد.\nاز دور بعدی هر دور %s پست می‌گذارم (هر دور یک عدد تصادفی در این بازه). "
                "دورها هر ۳۰ تا ۴۰ دقیقه‌اند، یعنی اگر پست قابل‌ارسال کافی باشد حدود %d تا %d پست در روز." % (
                    ("%d تا %d" % (lo, hi)) if lo != hi else str(lo), lo * rounds, hi * rounds) + tail)
    state["speed"] = "auto"
    return ("🤖 حالت «خودکار» روشن شد. از این به بعد دقیقاً طبق این فرمول پست می‌گذارم (ساعت به وقت ایران):\n\n"
            "📅 روز عادی (شنبه تا پنجشنبه تا ظهر) — پست در هر ساعت:\n"
            "• ۰۰ تا ۰۱: ۴ تا ۵\n"
            "• ۰۱ تا ۰۷: ۰ تا ۱ (نیمه‌خاموش)\n"
            "• ۰۷ تا ۱۱: ۳ تا ۴\n"
            "• ۱۱ تا ۱۶: ۲ تا ۳\n"
            "• ۱۶ تا ۲۰: ۳ تا ۴\n"
            "• ۲۰ تا ۲۴: ۴ تا ۵\n"
            "جمع: حدود ۶۰ تا ۷۰ پست در شبانه‌روز.\n\n"
            "🎉 تعطیلی (پنجشنبه از ساعت ۱۲ تا جمعه ساعت ۲۰) — پست در هر ساعت:\n"
            "• ۰۰ تا ۰۲: ۶\n"
            "• ۰۲ تا ۰۸: ۰ تا ۱\n"
            "• ۰۸ تا ۱۲: ۴\n"
            "• ۱۲ تا ۱۷: ۴\n"
            "• ۱۷ تا ۲۰: ۴ تا ۵\n"
            "• ۲۰ تا ۲۴: ۶\n"
            "جمع: حدود ۸۰ تا ۸۵ پست در شبانه‌روز. جمعه شب بعد از ساعت ۲۰ دوباره مثل روز عادی می‌شود.\n\n"
            "🧮 محاسبه‌ی هر دور: نرخ ساعتِ فعلی (یک عدد تصادفی بین کمینه و بیشینه) × طول دور (حدود ۳۵ دقیقه ÷ ۶۰). "
            "مثلاً ساعت ۲۱ روز عادی: ۴ تا ۵ پست در ساعت × ۰٫۵۸ ≈ ۲ تا ۳ پست در هر دور. اعشار تصادفی گرد می‌شود؛ "
            "پس در ساعت‌های کم‌پست بعضی دورها پستی ندارند و بعضی یکی می‌فرستند." + tail
            + "\n\n" + speed_line(cfg, state))


_FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")


def speed_apply(cfg, state, mode, rng=None):
    return _speed_apply(cfg, state, mode, rng).translate(_FA)


def speed_line(cfg, state, now=None):
    return _speed_line(cfg, state, now).translate(_FA)


def speed_menu():
    kb = {"inline_keyboard": [
        [{"text": "🐢 کم (۱ تا ۲)", "callback_data": "tx:sp_low"}, {"text": "⚖️ متوسط (۲ تا ۴)", "callback_data": "tx:sp_mid"},
         {"text": "🚀 زیاد (۶ تا ۸)", "callback_data": "tx:sp_high"}],
        [{"text": "✏️ تنظیم دستی", "callback_data": "tx:sp_manual"}, {"text": "🤖 خودکار", "callback_data": "tx:sp_auto"}]]}
    return kb


def speed_menu_text(cfg, state):
    return ("🎚 سرعت ارسال را انتخاب کنید (تعداد پستِ نهایی هر دور، بعد از همه‌ی فیلترها):\n"
            "🐢 کم: ۱ تا ۲ • ⚖️ متوسط: ۲ تا ۴ • 🚀 زیاد: ۶ تا ۸\n"
            "✏️ دستی: خودتان بازه را می‌نویسید (مثلاً ۸ تا ۱۰)\n"
            "🤖 خودکار: با ساعت شبانه‌روز و تعطیلات خودش تنظیم می‌کند\n\n"
            "الان: " + speed_line(cfg, state))


def crisis_menu():
    return {"inline_keyboard": [[{"text": "🚨 روشن", "callback_data": "tx:cr_on"}, {"text": "🛑 خاموش", "callback_data": "tx:cr_off"},
                                 {"text": "🤖 خودکار", "callback_data": "tx:cr_auto"}]]}


def more_menu(state):
    return {"inline_keyboard": [[{"text": "🚫 کلمات ممنوع", "callback_data": "tx:ban"}, {"text": "⏰ ساعت‌های پربازدید", "callback_data": "tx:hours"}],
                                [{"text": "🔍 بررسی مشکوک‌ها (روشن/خاموش)", "callback_data": "tx:review"}],
                                [{"text": "📖 راهنما و دستورها", "callback_data": "tx:help"}]]}


TX_MAP = {"sp_low": "/speed low", "sp_mid": "/speed mid", "sp_high": "/speed high", "sp_auto": "/speed auto",
          "sp_manual": "/manual", "cr_on": BTN_CR_ON, "cr_off": BTN_CR_OFF, "cr_auto": BTN_CR_AUTO,
          "dest_add": "/dest add", "ban": BTN_BAN, "hours": BTN_HOURS, "review": BTN_REVIEW, "help": "/help"}


def hours_update(cfg, net, state, now):
    """About every 3 hours read the public page of OUR channel and note the views of posts that are
    6-14 hours old, grouped by the Iran hour they were published. Needs a public channel."""
    if now - state.get("hv_ts", 0) < 3 * 3600:
        return
    state["hv_ts"] = int(now)
    name = normalize_source(str(cfg.get("target_channel", "")))
    if not re.match(r"^[A-Za-z][A-Za-z0-9_]{3,31}$", name):
        return
    try:
        posts = parse_page(net.get(cfg["web_base"] + name))
    except Exception:                              # statistics must never disturb posting
        log.info("could not read the destination page for the hour statistics")
        return
    hv, seen = state.setdefault("hv", {}), state.setdefault("hv_seen", [])
    for p in posts:
        if p.get("views") is None or p.get("ts") is None or p["id"] in seen:
            continue
        if not 6 * 3600 <= now - p["ts"] <= 14 * 3600:
            continue
        hour = str(time.gmtime(p["ts"] + int(cfg["utc_offset_minutes"]) * 60).tm_hour)
        b = hv.setdefault(hour, [0, 0])
        b[0] += p["views"]
        b[1] += 1
        seen.append(p["id"])
    del seen[:-300]


def hours_text(state):
    rows = [(int(h), b[0] / b[1], b[1]) for h, b in (state.get("hv") or {}).items() if b[1] >= 2]
    total = sum(b[1] for b in (state.get("hv") or {}).values())
    if total < 15 or not rows:
        return ("⏰ هنوز داده‌ی کافی نیست (%d پست سنجیده شده). ربات هر چند ساعت بازدید پست‌های ۶ تا ۱۴ ساعت "
                "پیشِ کانال خودتان را می‌خواند؛ بعد از چند روز اینجا ساعت‌های پربازدید را می‌بینید." % total)
    rows.sort(key=lambda r: -r[1])
    lines = ["⏰ بهترین ساعت‌های انتشار (به وقت ایران، میانگین بازدید هر پست، %d پست سنجیده شده):" % total]
    for h, avg, n in rows[:5]:
        lines.append("• %02d:00 تا %02d:59  ←  %d بازدید (از %d پست)" % (h, h, avg, n))
    worst = rows[-1]
    if len(rows) > 5:
        lines.append("کم‌بازدیدترین: %02d:00 با %d بازدید" % (worst[0], worst[1]))
    lines.append("\nبازدید پست‌ها وقتی ۶ تا ۱۴ ساعت از انتشارشان گذشته ثبت می‌شود تا با هم قابل مقایسه باشند. "
                 "ربات خودش ساعت ارسال را عوض نمی‌کند؛ این فقط راهنمای شماست.")
    return "\n".join(lines)


# ---- sources / banned words managed from the bot (kept in state.json, on top of the secret config) ----
def apply_overrides(cfg, state):
    """Merge what you changed in the bot with the base config: added/removed sources, banned words."""
    base_src = cfg.setdefault("_base_sources", list(cfg["sources"]))
    base_ad = cfg.setdefault("_base_ad", list(cfg["ad_keywords"]))
    now = time.time()
    mu = state.get("muted") or {}
    for k in [k for k, v in mu.items() if v <= now]:
        mu.pop(k)
    gone = {x.lower() for x in state.get("src_del", [])}
    srcs, seen = [], set()
    for s in list(base_src) + list(state.get("src_add", [])):
        if s.lower() not in gone and s.lower() not in seen:
            seen.add(s.lower())
            srcs.append(s)
    if srcs or cfg.get("_allow_empty"):
        cfg["sources"] = srcs
    off = {w.lower() for w in state.get("ban_off", [])}
    ads = [w for w in base_ad if w.lower() not in off]
    ads += [w for w in state.get("ban_words", []) if w.lower() not in {a.lower() for a in ads}]
    cfg["ad_keywords"] = ads


def is_muted(state, name):
    return (state.get("muted") or {}).get(name.lower(), 0) > time.time()


def fmt_left(sec):
    return "%d ساعت" % max(1, round(sec / 3600)) if sec < 2 * 86400 else "%d روز" % round(sec / 86400)


def sources_view(cfg, state):
    rows, lines = [], ["📋 منبع‌های فعلی (%d):" % len(cfg["sources"])]
    for s in cfg["sources"]:
        left = (state.get("muted") or {}).get(s.lower(), 0) - time.time()
        lines.append("• %s%s" % (s, "  🔇 بی‌صدا، %s دیگر" % fmt_left(left) if left > 0 else ""))
        pre = (cfg["_pid"] + "|") if cfg.get("_pid") else ""
        rows.append([{"text": ("🔊 باز کردن " if left > 0 else "🔇 بی‌صدا (۱ روز) ") + s, "callback_data": "mt:" + pre + s},
                     {"text": "🗑 حذف", "callback_data": "dl:" + pre + s}])
    lines.append("\nاضافه کردن منبع (هر شکلی درست است):\n/add besnr\nadd besnr\nadd/besnr\nhttps://t.me/besnr")
    lines.append("\nبی‌صدا برای چند روز: /mute besnr 3")
    return "\n".join(lines), {"inline_keyboard": rows}


def bans_text(cfg, state):
    mine = state.get("ban_words", [])
    off = state.get("ban_off", [])
    base = [w for w in cfg.get("_base_ad", cfg["ad_keywords"]) if w.lower() not in {x.lower() for x in off}]
    lines = ["🚫 کلمات ممنوعِ شما (%d): %s" % (len(mine), "، ".join(mine) or "هیچ"),
             "کلمات ممنوعِ پیش‌فرض (%d): %s" % (len(base), "، ".join(base)),
             "\nاضافه: /ban کلمه\nحذف (از هر دو لیست): /unban کلمه",
             "هر پستی که این کلمه‌ها را داشته باشد ارسال نمی‌شود."]
    if off:
        lines.insert(2, "پیش‌فرض‌های غیرفعال‌شده: " + "، ".join(off))
    return "\n".join(lines)


def add_source(cfg, net, state, raw):
    name = normalize_source(raw)
    if not re.match(r"^[A-Za-z][A-Za-z0-9_]{3,31}$", name):
        return "❌ آیدی کانال درست نیست: %s" % raw
    if name.lower() in {s.lower() for s in cfg["sources"]}:
        return "این کانال از قبل در لیست هست."
    try:
        posts = parse_page(net.get(cfg["web_base"] + name))
    except NetError:
        posts = []
    if not posts:
        return "❌ کانالی عمومی با این نام پیدا نشد یا پستی نداشت: %s" % name
    state["src_del"] = [x for x in state.get("src_del", []) if x.lower() != name.lower()]
    if name.lower() not in {s.lower() for s in cfg.get("_base_sources", [])}:
        state.setdefault("src_add", []).append(name)
    state.setdefault("channels", {}).setdefault(src_key(name), {})["last_id"] = posts[-1]["id"]
    apply_overrides(cfg, state)
    return "✅ %s اضافه شد. از پست‌های بعدی‌اش استفاده می‌شود (پست‌های قدیمی نه)." % name


def del_source(cfg, state, raw):
    name = normalize_source(raw)
    real = next((s for s in cfg["sources"] if s.lower() == name.lower()), None)
    if not real:
        return "این کانال در لیست نیست: %s" % raw
    if len(cfg["sources"]) <= 1 and not cfg.get("_allow_empty"):
        return "❌ آخرین منبع را نمی‌شود حذف کرد."
    state["src_add"] = [x for x in state.get("src_add", []) if x.lower() != real.lower()]
    if real.lower() in {s.lower() for s in cfg.get("_base_sources", [])}:
        state.setdefault("src_del", []).append(real)
    (state.get("muted") or {}).pop(real.lower(), None)
    apply_overrides(cfg, state)
    return "🗑 %s حذف شد." % real


def source_button(cfg, net, state, cb):
    """Inline buttons under the sources list: mute / unmute (mt:) and delete (dl:)."""
    act, _, name = (cb.get("data") or "").partition(":")
    real = next((s for s in cfg["sources"] if s.lower() == name.lower()), None)
    note = "این کانال در لیست نیست"
    if real:
        mu = state.setdefault("muted", {})
        if act == "mt":
            if is_muted(state, real):
                mu.pop(real.lower(), None)
                note = "🔊 %s دوباره فعال شد" % real
            else:
                mu[real.lower()] = int(time.time() + 86400)
                note = "🔇 %s برای ۱ روز بی‌صدا شد" % real
        else:
            note = del_source(cfg, state, real)
    text, kb = sources_view(cfg, state)
    m = cb.get("message") or {}
    try:
        net.api("editMessageText", {"chat_id": m["chat"]["id"], "message_id": m["message_id"],
                                    "text": text, "reply_markup": kb})
    except (ApiError, NetError, KeyError):
        pass
    try:
        net.api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": note[:150]})
    except (ApiError, NetError):
        pass


def manage_command(cfg, net, state, text):
    """Returns (reply, markup) when the text is a source / banned-word command, else None."""
    # forgiving format: "/add name", "add name", "add/name", "/add/name", "اضافه name"
    fm = re.match(r"^/?(add|del|mute|unmute|ban|unban|اضافه|حذف)(?:@\w+)?(?:[\s/:：]+(.*))?$", text, re.S | re.I)
    if fm and (fm.group(2) or text.startswith("/") or fm.group(1).lower() in ("add", "del", "mute", "unmute", "ban", "unban")):
        w = fm.group(1).lower()
        cmd, arg = "/" + {"اضافه": "add", "حذف": "del"}.get(w, w), (fm.group(2) or "").strip()
        if cmd in ("/add", "/del") and not arg:
            return ("مثال:\n%s besnr\n%s/besnr\n%s https://t.me/besnr" % (cmd, cmd[1:], cmd)), None
    else:
        cmd, _, arg = text.partition(" ")
        cmd, arg = cmd.split("@")[0].lower(), arg.strip()
    if text == BTN_SRC or cmd == "/sources":
        return sources_view(cfg, state)
    if text in (BTN_HOURS, OLD_HOURS) or cmd == "/hours":
        return hours_text(state), None
    if text == BTN_BAN or cmd == "/bans":
        return bans_text(cfg, state), None
    if cmd == "/add" or (not arg and re.match(r"^(?:https?://)?(?:www\.)?(?:t|telegram)\.me/[A-Za-z]\w+/?$", text)):
        r = add_source(cfg, net, state, arg or text)
        return r, None
    if cmd == "/del":
        return del_source(cfg, state, arg) if arg else "مثال: /del name", None
    if cmd in ("/mute", "/unmute"):
        parts = arg.split()
        name = normalize_source(parts[0]) if parts else ""
        real = next((s for s in cfg["sources"] if s.lower() == name.lower()), None)
        if not real:
            return "این کانال در لیست نیست. مثال: /mute name 3", None
        mu = state.setdefault("muted", {})
        if cmd == "/unmute":
            mu.pop(real.lower(), None)
            return "🔊 %s دوباره فعال شد." % real, None
        days = 1.0
        if len(parts) > 1:
            try:
                days = min(30.0, max(0.1, float(parts[1])))
            except ValueError:
                pass
        mu[real.lower()] = int(time.time() + days * 86400)
        return "🔇 %s برای %s بی‌صدا شد؛ در این مدت پستش ارسال نمی‌شود." % (real, fmt_left(days * 86400)), None
    if cmd in ("/ban", "/unban"):
        w = arg.strip()
        if not w:
            return "مثال: %s کلمه" % cmd, None
        mine, off = state.setdefault("ban_words", []), state.setdefault("ban_off", [])
        lw = w.lower()
        if cmd == "/ban":
            if lw in {x.lower() for x in off}:
                state["ban_off"] = [x for x in off if x.lower() != lw]
            elif lw not in {x.lower() for x in mine} and lw not in {x.lower() for x in cfg.get("_base_ad", [])}:
                mine.append(w)
            r = "🚫 «%s» ممنوع شد." % w
        else:
            state["ban_words"] = [x for x in mine if x.lower() != lw]
            if lw in {x.lower() for x in cfg.get("_base_ad", [])} and lw not in {x.lower() for x in off}:
                off.append(w)
            r = "✅ «%s» از کلمات ممنوع برداشته شد." % w
        apply_overrides(cfg, state)
        return r, None
    return None


SHOW_KB = [False]      # the menu keyboard is attached to an answer only when this is set (/start, one-time refresh)
REPLY_TO = [None]      # id of the owner's message the bot is answering right now: the answer quotes it


def tell(net, chat, text, markup=None):
    if TAG[0]:
        text = TAG[0] + "\n" + text
    p = {"chat_id": chat, "text": text, "disable_web_page_preview": True}
    if REPLY_TO[0]:
        p["reply_to_message_id"] = REPLY_TO[0]
        p["allow_sending_without_reply"] = True
    if markup is MENU_KB and not SHOW_KB[0]:
        markup = None                              # Telegram keeps the keyboard on screen; re-sending it would pop it open again
    if markup:
        p["reply_markup"] = markup
    try:
        return net.api("sendMessage", p)
    except (ApiError, NetError) as e:
        log.warning("could not message the owner: %s", getattr(e, "desc", e))


def owner_of(cfg, state):
    root = hub_of(cfg, state)[1]
    return int(cfg.get("owner_id") or root.get("owner_id") or 0)


def status_text(cfg, state):
    on = not state.get("paused")
    lines = ["وضعیت ربات: " + ("🟢 روشن" if on else "🔴 خاموش")]
    root = hub_of(cfg, state)[1]
    if root.get("dests"):
        lines.insert(0, "🎯 مقصد در حال مدیریت: %s (از %d مقصد؛ تغییر: «🎯 مقصدها»)" % (
            cfg["target_channel"], len(root["dests"]) + 1))
    nxt = state.get("next_run_ts", 0) - time.time()
    if on:
        lines.append("دور بعدی ارسال: " + ("به‌زودی" if nxt <= 0 else "حدود %d دقیقه دیگر" % (nxt // 60 + 1)))
    lines.append("پست‌های منتظر تصمیم شما: %d" % len(state.get("pending", {})))
    lines.append("تاییدشده و منتظر ارسال: %d" % len(state.get("approved", [])))
    lines.append("بررسی پست‌های مشکوک: " + ("روشن" if not state.get("review_off") else "خاموش"))
    lines.append(speed_line(cfg, state))
    if speed_mode(state) == "auto":
        lo, hi, hol, h = auto_rate(cfg, time.time())
        lines.append("   ↳ این ساعت %s پست در ساعت ≈ %s پست در هر دور (فرمول کامل: 🎚 سرعت ارسال ← خودکار)" % (
            ("%d تا %d" % (lo, hi)) if lo != hi else str(lo),
            ("%.1f تا %.1f" % (lo * mean_gap(cfg, hi <= 1) / 60, hi * mean_gap(cfg, hi <= 1) / 60))))
    mode = state.get("crisis_mode", "auto")
    lines.append("حالت بحران: " + {"on": "🚨 روشن (دستی)", "off": "🛑 خاموش (دستی)"}.get(
        mode, "🚨 فعال (خودکار)" if state.get("crisis_auto") else "🤖 خودکار (الان عادی)"))
    lr, lm = state.get("last_round"), state.get("last_manual")
    if lr:
        lines.append("\n" + round_text(cfg, lr, "آخرین دور ارسال"))
    if lm and (not lr or lm.get("t", 0) > lr.get("t", 0)):
        lines.append("\n" + round_text(cfg, lm, "آخرین ارسال فوری (⚡)"))
    if not lr and not lm:
        lines.append("\nهنوز دوری با پست تازه انجام نشده.")
    return "\n".join(lines)


def round_text(cfg, r, title):
    tm = time.gmtime(r["t"] + int(cfg["utc_offset_minutes"]) * 60)
    ago = max(0, int((time.time() - r["t"]) / 60))
    when = "%d دقیقه پیش" % ago if ago < 60 else "%d ساعت و %d دقیقه پیش" % (ago // 60, ago % 60)
    names = {src_key(n): n for n in cfg["sources"]}
    out = ["📦 %s (ساعت %02d:%02d، %s%s):" % (title, tm.tm_hour, tm.tm_min, when, "، حالت بحران" if r.get("crisis") else ("، سرعت %s" % r["mode"]) if r.get("mode") else ""),
           "• پست تازه پیدا شد: %d" % r["found"]]
    ignored = r["found"] - r.get("considered", r["found"])
    if ignored > 0:
        out.append("• نادیده (بعد از رسیدن به تعداد هدف، پست‌های قدیمی‌تر بررسی نمی‌شوند): %d" % ignored)
    if r.get("target") is not None and r.get("mode"):
        out.append("• هدف این دور: %d پست%s" % (r["target"], (" — %d پست کمتر از هدف قابل‌ارسال بود (پست تازه‌ی تکراری/ردشده/نبود)" % r["short"]) if r.get("short") else ""))
    if r.get("rej"):
        out.append("• ردشده: %d (%s)" % (sum(r["rej"].values()), "، ".join("%s %d" % kv for kv in sorted(r["rej"].items()))))
    if r.get("over"):
        out.append("• جا نشد (سقف پست در هر دور): %d" % r["over"])
    out.append("• ریپوست شد: %d" % r.get("posted", 0))
    rows = sorted(r.get("src", {}).items(), key=lambda kv: (-kv[1][1], -kv[1][0]))
    if rows:
        out.append("سهم کانال‌ها (تازه ← ریپوست):")
        for key, (new, sent) in rows:
            out.append("  %s %s: %d ← %d" % ("✅" if sent else "▫️", names.get(key, "(کانال حذف‌شده)"), new, sent))
    if r.get("appr"):
        out.append("  + %d پست تاییدشده‌ی شما" % r["appr"])
    why = r.get("why") or []
    ign = r.get("ign") or {}
    if why or ign:
        out.append("\n🔎 علت هر پستی که نرفت:")
        for n, (key, pid, text) in enumerate(why[:12], 1):
            name = names.get(key)
            out.append("%d) %s\n    %s" % (n, ("t.me/%s/%s" % (name, pid)) if name and pid else
                                              (name or "کانال نامشخص"), text))
        if len(why) > 12:
            out.append("... و %d مورد دیگر" % (len(why) - 12))
        if ign:
            out.append("• پست‌های قدیمی‌تر که نادیده ماندند (فقط تازه‌ترینِ هر کانال بررسی می‌شود): " + "، ".join(
                "%s %d" % (names.get(k, "؟"), v) for k, v in ign.items()))
    return "\n".join(out)


def reseed(cfg, net, state):
    """After switching on: everything posted while off counts as seen, only newer posts are used."""
    for name in cfg["sources"]:
        key = hashlib.sha1(name.lower().encode("utf-8")).hexdigest()[:10]
        try:
            posts = parse_page(net.get(cfg["web_base"] + name))
        except NetError:
            continue
        if posts:
            state["channels"].setdefault(key, {})["last_id"] = posts[-1]["id"]

def process_updates(cfg, net, state, state_path, wait=0):
    """wait > 0 = long polling: Telegram holds the request and answers the moment you press a button."""
    cfg, state = hub_of(cfg, state)
    if FWD_BUF and wait:
        wait = min(wait, 2)                         # collecting album parts: look again in 2 s
    try:
        ups = net.api("getUpdates", {"offset": state.get("update_offset", 0), "timeout": int(wait),
                                     "allowed_updates": ["message", "callback_query"]})
    except (ApiError, NetError) as e:
        log.warning("cannot read bot messages: %s", getattr(e, "desc", e))
        return
    for u in ups or []:
        state["update_offset"] = u["update_id"] + 1
        REPLY_TO[0] = None
        SHOW_KB[0] = False
        try:
            handle_update(cfg, net, state, u)
        except Exception:
            log.exception("could not handle a bot message")
        REPLY_TO[0] = None
        SHOW_KB[0] = False
    TAG[0] = ""
    ow = owner_of(cfg, state)
    if ow and not state.get("seeded_src2"):       # one time: three new source channels
        out = []
        for nm in SEED_SOURCES:
            r = add_source(cfg, net, state, nm)
            out.append("• %s: %s" % (nm, r))
        if all(("پیدا نشد" not in x) for x in out) or state.get("seed_tries", 0) >= 3:
            state["seeded_src2"] = 1
        state["seed_tries"] = state.get("seed_tries", 0) + 1
        save_state(state_path, state)
        tell(net, ow, "📋 افزودن منبع‌های جدید:\n" + "\n".join(out) + "\n(از پست‌های قدیمی‌شان چیزی ارسال نمی‌شود؛ فقط پست‌های تازه.)")
    if ow and state.get("kb_v") != 4:             # one time: the menu with the new "destinations" button
        SHOW_KB[0] = True
        old = state.get("speed") in ("normal", "boost")
        msg = ("⌨️ منوی ربات به‌روز شد.\n"
               "• 🎯 مقصدها: چند کانال مقصد، هر کدام با منبع‌ها و تنظیمات جدا (ویماپرو همان که بود می‌ماند)\n"
               "• 🎚 سرعت ارسال ← کم / متوسط / زیاد / دستی / خودکار\n• 🚨 بحران ← روشن / خاموش / خودکار\n"
               "• ⚙️ بیشتر ← کلمات ممنوع، ساعت‌ها، بررسی مشکوک‌ها، راهنما\n"
               "هر دکمه که بزنید، ربات به پیام شما ریپلای می‌کند و توضیح کامل می‌دهد چه حالتی روشن شد.")
        if old:
            msg += "\n\nℹ️ سرعت‌های قدیمی (نرمال/بوست) حذف شدند و الان روی «🤖 خودکار» هستید."
        if tell(net, ow, msg, MENU_KB) is not None:
            state["kb_v"] = 4
            if old:
                state["speed"] = "auto"
            save_state(state_path, state)
        SHOW_KB[0] = False
    if expire_pending(cfg, net, state) or flush_forwards(cfg, net, state) or ups:
        save_state(state_path, state)


def _handle_update(cfg, net, state, u):
    cb = u.get("callback_query")
    if cb:
        if cb["from"]["id"] != owner_of(cfg, state):
            return
        act, _, pid = (cb.get("data") or "").partition(":")
        if act == "tx":                            # a button inside one of the menus = the same as typing its command
            cmd = TX_MAP.get(pid)
            m0 = cb.get("message") or {}
            try:
                net.api("answerCallbackQuery", {"callback_query_id": cb["id"]})
            except (ApiError, NetError):
                pass
            if cmd and m0.get("chat"):
                fake = {"message": {"message_id": m0.get("message_id"), "chat": m0["chat"], "from": cb["from"], "text": cmd}}
                handle_update(cfg, net, state, fake)
            return
        if act in ("mt", "dl"):
            source_button(cfg, net, state, cb)
            return
        if act in ("fw", "rm"):
            forward_button(cfg, net, state, cb, act, pid)
            return
        pend = state.setdefault("pending", {}).pop(pid, None)
        if pend is None:
            try:
                net.api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": "این مورد منقضی شده"})
            except (ApiError, NetError):
                pass
            return
        if act == "ok":
            pend["t"] = int(time.time())
            state.setdefault("approved", []).append(pend)
            note = "✅ تایید شد؛ در دور بعدی ارسال می‌شود"
        else:
            note = "❌ رد شد"
        m = cb.get("message") or {}
        try:                                       # first: update the message (works even when late)
            net.api("editMessageText", {"chat_id": m["chat"]["id"], "message_id": m["message_id"],
                                        "text": (m.get("text") or "") + "\n\n" + note})
        except (ApiError, NetError, KeyError):
            pass
        try:                                       # Telegram refuses this one if we are too slow
            net.api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": note})
        except (ApiError, NetError):
            pass
        return
    m = u.get("message")
    if not m or (m.get("chat") or {}).get("type") != "private":
        return
    uid, text = m["from"]["id"], (m.get("text") or "").strip()
    owner = owner_of(cfg, state)
    if not owner:
        if not text.startswith("/start"):
            return
        hub_of(cfg, state)[1]["owner_id"] = owner = uid          # the first person who presses Start is the owner
        log.info("owner registered")
    if uid != owner:
        return
    REPLY_TO[0] = m.get("message_id")             # every answer below quotes this message
    SHOW_KB[0] = text.startswith("/start") or text.startswith("/menu")
    if is_forward_or_media(m):                    # a post you forwarded / sent: process it and publish now
        gid = m.get("media_group_id")
        if gid:
            b = FWD_BUF.setdefault(gid, {"msgs": [], "t": 0, "pf": (cfg, state)})
            b["msgs"].append(m)
            b["t"] = time.time()
        else:
            handle_forward(cfg, net, state, owner, [m])
        return
    managed = manage_command(cfg, net, state, text)
    if managed:
        tell(net, owner, managed[0], managed[1] or MENU_KB)
        return
    if state.get("await_manual") and not text.startswith("/") and text not in ALL_BTNS:
        if time.time() - state["await_manual"] > 600:
            state.pop("await_manual", None)
        else:
            rng = parse_range(text, int(cfg["manual_max_posts"]))
            if rng:
                tell(net, owner, speed_apply(cfg, state, "manual", rng), MENU_KB)
                return
            tell(net, owner, "عدد را متوجه نشدم. مثلاً بنویسید «۸ تا ۱۰» یا «4».")
            return
    text = OLD_CR.get(text, text)
    if text in (OLD_REVIEW,):
        text = BTN_REVIEW
    if text == BTN_NOW or text.startswith("/now"):
        if state.get("paused"):
            tell(net, owner, "🔴 ربات خاموش است. اول «▶️ روشن» را بزنید.", MENU_KB)
        else:
            state["run_now"] = int(time.time())
            tell(net, owner, "⚡ دور فوری شروع شد؛ نتیجه را همین‌جا می‌فرستم. دور عادی سر وقت خودش اجرا می‌شود.", MENU_KB)
        return
    sm = re.match(r"^/?(speed|manual|boost|normal|auto)(?:@\w+)?(?:[\s:_]+(.*))?$", text, re.I | re.S)
    if text in (BTN_SPEED, BTN_SP_NORMAL, BTN_SP_BOOST) or (sm and (text.startswith("/") or sm.group(2))):
        word = (sm.group(1).lower() if sm else "")
        arg = ((sm.group(2) or "").strip().lower() if sm else "")
        if word in ("boost", "normal") or text in (BTN_SP_NORMAL, BTN_SP_BOOST):
            word, arg = "speed", "auto"           # the old two buttons: now the automatic mode
        if word == "auto":
            word, arg = "speed", "auto"
        if word == "manual":
            rng = parse_range(arg, int(cfg["manual_max_posts"])) if arg else None
            if rng:
                tell(net, owner, speed_apply(cfg, state, "manual", rng), MENU_KB)
            else:
                state["await_manual"] = int(time.time())
                tell(net, owner, "✏️ تنظیم دستی: بازه‌ی تعداد پستِ نهایی هر دور را بنویسید، مثلاً «۸ تا ۱۰» یا «3-5» "
                     "(یک عدد تنها هم قبول است؛ از ۱ تا %d). همین‌جا برایم بنویسید؛ تا ۱۰ دقیقه منتظرم." % int(cfg["manual_max_posts"]))
        elif word == "speed" and arg in ("low", "mid", "high", "auto"):
            tell(net, owner, speed_apply(cfg, state, arg), MENU_KB)
        else:
            tell(net, owner, speed_menu_text(cfg, state), speed_menu())
        return
    if text == BTN_CRMENU:
        mode = state.get("crisis_mode", "auto")
        tell(net, owner, "🚨 حالت بحران: وقتی کانال‌ها ناگهان پر از پست تازه می‌شوند (مثلاً خبر مهم)، ربات از هر کانال تا ۳ پست آخر "
             "را با فاصله‌ی کم (هر ۱۰ تا ۱۵ دقیقه، تا ۱۵ پست در هر دور) می‌فرستد و لیبل عکس را نمی‌گذارد.\n"
             "🚨 روشن = همیشه بحران • 🛑 خاموش = هرگز بحران • 🤖 خودکار = با هجوم پست‌ها خودش روشن و خاموش می‌شود.\n\n"
             "الان: " + {"on": "🚨 روشن (دستی)", "off": "🛑 خاموش (دستی)"}.get(
                 mode, "🚨 فعال (خودکار)" if state.get("crisis_auto") else "🤖 خودکار (الان عادی)"), crisis_menu())
        return
    if text == BTN_MORE:
        tell(net, owner, "⚙️ تنظیمات بیشتر:", more_menu(state))
        return
    if text.startswith("/help"):
        tell(net, owner, HELP_TEXT, MENU_KB)
        return
    if text.startswith("/crisis") or text in (BTN_CR_ON, BTN_CR_OFF, BTN_CR_AUTO):
        if text == BTN_CR_ON or text.startswith("/crisis_on"):
            state["crisis_mode"] = "on"
            state["next_run_ts"] = 0
            msg = "🚨 حالت بحران روشن شد (دستی). تا وقتی خاموش یا خودکار نکنید می‌ماند. لیبل عکس‌ها غیرفعال است."
        elif text == BTN_CR_OFF or text.startswith("/crisis_off"):
            state["crisis_mode"] = "off"
            msg = "🛑 حالت بحران خاموش شد (دستی). حتی اگر پست‌ها زیاد شوند، فعال نمی‌شود."
        else:
            state["crisis_mode"] = "auto"
            msg = "🤖 حالت بحران روی خودکار است: با هجوم پست‌ها روشن و با آرام شدن خاموش می‌شود."
        state["crisis_auto"] = 0
        state.pop("crisis_calm_since", None)
        tell(net, owner, msg, MENU_KB)
    elif text == BTN_REVIEW or text.startswith("/review"):
        state["review_off"] = not state.get("review_off")
        tell(net, owner, "بررسی پست‌های مشکوک: " + ("خاموش شد" if state["review_off"] else "روشن شد"), MENU_KB)
    elif "خاموش" in text or text.startswith("/stop") or text.startswith("/off"):
        state["paused"] = True
        tell(net, owner, "🔴 ارسال خاموش شد. هر وقت خواستید «روشن کردن» را بزنید.", MENU_KB)
    elif "روشن" in text or text.startswith("/on"):
        reseed(cfg, net, state)
        state["paused"] = False
        state["next_run_ts"] = 0
        tell(net, owner, "🟢 ارسال روشن شد. فقط پست‌هایی که از حالا منتشر شوند بررسی می‌شوند.", MENU_KB)
    else:
        extra = ""
        if text and text != BTN_STATUS and not text.startswith(("/start", "/status", "/help")):
            extra = "متوجه این پیام نشدم. برای فرستادن یک پست به کانال، همان پست را برای من فوروارد کنید.\n\n" + "اضافه کردن منبع (هر کدام از این شکل‌ها درست است):\n/add besnr\nadd besnr\nadd/besnr\nhttps://t.me/besnr\n\nحذف: /del besnr\nبی‌صدا برای ۳ روز: /mute besnr 3   (برگرداندن: /unmute besnr)\nکلمه ممنوع: /ban کلمه   (برداشتن: /unban کلمه)" + "\n\n"
        tell(net, owner, extra + status_text(cfg, state), MENU_KB)


# ---- posts you forward (or send) to the bot: processed like any other post, published at once ----
FWD_BUF = {}                                     # album parts arrive as separate messages: collect them
FWD_KEYS = ("forward_origin", "forward_from_chat", "forward_from", "forward_date", "forward_sender_name")
FWD_BAD = ("document", "voice", "audio", "sticker", "animation", "video_note", "poll", "location", "contact")


# ---------------------------------------------------------------------------- #
# destinations: add / switch / remove (every destination = a separate profile)
# ---------------------------------------------------------------------------- #
SPEED_FA = {"low": "کم", "mid": "متوسط", "high": "زیاد", "manual": "دستی", "auto": "خودکار"}


def check_dest(net, target):
    """(ok, message, title). The bot must be an admin that may post AND delete messages - checked before anything starts."""
    try:
        me = net.api("getMe")
        chat = net.api("getChat", {"chat_id": target})
    except ApiError as e:
        return False, ("❌ کانالی با آیدی %s پیدا نشد (%s).\nآیدی را درست و عمومی بنویسید، مثل @mychannel" % (target, e.desc)), None
    except NetError as e:
        return False, "⚠️ مشکل شبکه؛ چند دقیقه بعد دوباره امتحان کنید (%s)." % e, None
    title = chat.get("title") or target
    if chat.get("type") != "channel":
        return False, "❌ %s یک کانال نیست (فقط کانال تلگرام پشتیبانی می‌شود)." % target, None
    how = ("\n\nچطور: کانال %s ← بالا روی نامش بزنید ← Administrators ← Add Admin ← این ربات را انتخاب کنید ← "
           "گزینه‌های «Post Messages» و «Delete Messages» را روشن کنید ← Save. بعد دوباره همین‌جا آیدی کانال را بفرستید." % target)
    try:
        mem = net.api("getChatMember", {"chat_id": target, "user_id": me["id"]})
    except ApiError as e:
        return False, "❌ ربات در %s عضو یا مدیر نیست (%s). اول باید ربات را مدیر کانال کنید.%s" % (target, e.desc, how), None
    if mem.get("status") not in ("administrator", "creator"):
        return False, "❌ ربات در %s مدیر نیست.%s" % (target, how), None
    if mem.get("status") == "administrator":
        miss = []
        if not mem.get("can_post_messages"):
            miss.append("ارسال پیام (Post Messages)")
        if not mem.get("can_delete_messages"):
            miss.append("حذف پیام‌ها (Delete Messages)")
        if miss:
            return False, "❌ ربات در %s مدیر است ولی این دسترسی‌ها را ندارد: %s.%s" % (target, "، ".join(miss), how), None
    return True, "", title


def dest_summary(cfg0, root, active_id):
    rows = []
    for i, (pid_, c, st) in enumerate(profiles(cfg0, root), 1):
        rows.append("%d) %s%s\n    %d منبع • %s • سرعت: %s" % (
            i, c["target_channel"], "  ✅ (در حال مدیریت)" if pid_ == active_id else "", len(c["sources"]),
            "⏸ خاموش" if st.get("paused") else "🟢 روشن", SPEED_FA.get(speed_mode(st), "؟")))
    return "\n".join(rows)


def dest_menu(cfg0, root):
    aid = active_profile(cfg0, root)[0]
    ps = profiles(cfg0, root)
    txt = ("🎯 مقصدها (%d از %d):\n%s\n\n"
           "هر مقصد کاملاً جداست: منبع‌ها، سرعت، کلمات ممنوع، تاریخچه‌ی ضدتکرار، روشن/خاموش و گزارش‌هایش. "
           "یک کانال مبدأ را می‌شود برای چند مقصد گذاشت (هر مقصد مستقل از آن استفاده می‌کند).\n"
           "دکمه‌های 📊 وضعیت، ⚡ ارسال، ▶️/⏸، 🎚 سرعت، 🚨 بحران، 📋 منبع‌ها و ⚙️ بیشتر همیشه روی «مقصد در حال مدیریت» (✅) اثر دارند؛ "
           "برای عوض کردنش روی نام مقصد بزنید.") % (len(ps), MAX_DESTS, dest_summary(cfg0, root, aid))
    rows = [[{"text": ("✅ " if p[0] == aid else "🎯 ") + p[1]["target_channel"], "callback_data": "dp:" + p[0]}] for p in ps]
    rows.append([{"text": "➕ مقصد جدید", "callback_data": "tx:dest_add"}])
    rows += [[{"text": "🗑 حذف " + p[1]["target_channel"], "callback_data": "dd:" + p[0]}] for p in ps[1:]]
    return txt, {"inline_keyboard": rows}


def dest_add(cfg0, net, root, raw):
    name = normalize_source(raw)
    if not re.match(r"^[A-Za-z][A-Za-z0-9_]{3,31}$", name):
        return "❌ آیدی کانال درست نیست: %s\nمثال: /dest add @mychannel" % raw, None
    target = "@" + name
    ps = profiles(cfg0, root)
    if any(p[1]["target_channel"].lower() == target.lower() for p in ps):
        return "این کانال از قبل در لیست مقصدها هست.", None
    if len(ps) >= MAX_DESTS:
        return "❌ سقف %d مقصد پر شده است. اول یکی را حذف کنید." % MAX_DESTS, None
    ok, msg, title = check_dest(net, target)
    if not ok:
        return msg, None
    n = int(root.get("dest_n", 1)) + 1
    root["dest_n"] = n
    st = SubState({"channels": {}, "fp": [], "next_run_ts": int(time.time() + random.uniform(120, 420))})
    root.setdefault("dests", []).append({"id": "d%d" % n, "target": target, "title": title, "st": st})
    root["active"] = "d%d" % n
    profiles(cfg0, root)
    return ("✅ مقصد جدید اضافه شد: %s (%s)\n"
            "ربات مدیر کانال است و دسترسی ارسال و حذف پیام را دارد.\n\n"
            "از همین لحظه %s «مقصد در حال مدیریت» است: دکمه‌های 📋 منبع‌ها، 🎚 سرعت، 🚨 بحران، ▶️/⏸ و ... همه روی همین کانال اثر دارند "
            "و تنظیمات ویماپرو و بقیه‌ی مقصدها دست نمی‌خورد.\n\n"
            "قدم بعد: منبع‌هایش را اضافه کنید، مثلاً /add besnr (هر منبعی که برای مقصد دیگر هم گذاشته‌اید مجاز است). "
            "تا وقتی منبعی نداشته باشد هیچ پستی به آن ارسال نمی‌شود. سرعت پیش‌فرضش «خودکار» است و آیدی و لیبل عکس‌هایش %s می‌شود. "
            "برای برگشتن به ویماپرو: 🎯 مقصدها ← نام کانال." % (target, title, target, target)), None


def dest_text(cfg0, net, root, text):
    """Hub-level texts. Returns True when handled."""
    owner = owner_of(cfg0, root)
    m = re.match(r"^/dests?(?:@\w+)?(?:\s+(add|use|del)(?:\s+(.*))?)?\s*$", text, re.I | re.S)
    awaiting = root.get("await_dest")
    if awaiting and time.time() - awaiting > 600:
        root.pop("await_dest", None)
        awaiting = None
    if text != BTN_DEST and not m and not (awaiting and text and not text.startswith("/") and text not in ALL_BTNS):
        return False
    TAG[0] = ""
    if awaiting and not m and text != BTN_DEST:
        root.pop("await_dest", None)
        msg, kb = dest_add(cfg0, net, root, text)
        tell(net, owner, msg, kb or MENU_KB)
        return True
    cmd = (m.group(1) or "").lower() if m else ""
    arg = (m.group(2) or "").strip() if m else ""
    if cmd == "add":
        if not arg:
            root["await_dest"] = int(time.time())
            tell(net, owner, "➕ مقصد جدید: آیدی کانال را بفرستید، مثلاً @mychannel\n"
                 "قبلش ربات را در آن کانال مدیر کنید و دسترسی‌های «Post Messages» و «Delete Messages» را بدهید؛ "
                 "من قبل از شروع چک می‌کنم و اگر دسترسی‌ای کم باشد دقیقاً می‌گویم کدام. (تا ۱۰ دقیقه منتظرم)")
        else:
            msg, kb = dest_add(cfg0, net, root, arg)
            tell(net, owner, msg, kb or MENU_KB)
        return True
    if cmd in ("use", "del"):
        ps = profiles(cfg0, root)
        pick = None
        if arg.translate(_DIG).isdigit() and 1 <= int(arg.translate(_DIG)) <= len(ps):
            pick = ps[int(arg.translate(_DIG)) - 1]
        else:
            pick = next((p for p in ps if p[1]["target_channel"].lower().lstrip("@") == arg.lower().lstrip("@")), None)
        if not pick:
            tell(net, owner, "این مقصد را پیدا نکردم. شماره یا آیدی را از 🎯 مقصدها ببینید، مثل /dest use 2")
        elif cmd == "use":
            tell(net, owner, dest_switch(cfg0, root, pick[0]))
        else:
            tell(net, owner, *dest_confirm(pick))
        return True
    txt, kb = dest_menu(cfg0, root)
    tell(net, owner, txt, kb)
    return True


def dest_switch(cfg0, root, pid_):
    root["active"] = pid_
    p = active_profile(cfg0, root)
    return ("🎯 حالا «%s» در حال مدیریت است.\nهمه‌ی دکمه‌ها (وضعیت، ارسال، روشن/خاموش، سرعت، بحران، منبع‌ها، بیشتر) "
            "و فوروارد کردن پست برای ربات از این لحظه روی همین کانال اثر دارند و بقیه‌ی مقصدها دست نمی‌خورند.\n\n%s" % (
                p[1]["target_channel"], status_text(p[1], p[2])))


def dest_confirm(p):
    return ("🗑 حذف مقصد %s؟\nفقط از ربات حذف می‌شود: منبع‌ها و تنظیمات این مقصد پاک می‌شود و دیگر چیزی به آن ارسال نمی‌شود. "
            "پست‌های خود کانال و مدیر بودن ربات در آن دست نمی‌خورد." % p[1]["target_channel"],
            {"inline_keyboard": [[{"text": "✅ بله، حذف شود", "callback_data": "dc:" + p[0]},
                                  {"text": "↩️ انصراف", "callback_data": "dx:0"}]]})


def dest_button(cfg0, net, root, cb, act, pid_):
    owner = owner_of(cfg0, root)
    m = cb.get("message") or {}
    TAG[0] = ""
    note = ""
    try:
        net.api("answerCallbackQuery", {"callback_query_id": cb["id"]})
    except (ApiError, NetError):
        pass
    REPLY_TO[0] = m.get("message_id")
    ps = profiles(cfg0, root)
    pick = next((p for p in ps if p[0] == pid_), None)
    if act == "dp" and pick:
        tell(net, owner, dest_switch(cfg0, root, pick[0]))
    elif act == "dd" and pick and pick[0] != "p1":
        tell(net, owner, *dest_confirm(pick))
    elif act == "dc" and pick and pick[0] != "p1":
        root["dests"] = [d for d in root.get("dests", []) if d["id"] != pick[0]]
        _PCACHE.pop(pick[0], None)
        if root.get("active") == pick[0]:
            root["active"] = "p1"
        tell(net, owner, "🗑 مقصد %s از ربات حذف شد و دیگر چیزی به آن ارسال نمی‌شود. حالا «%s» در حال مدیریت است." % (
            pick[1]["target_channel"], active_profile(cfg0, root)[1]["target_channel"]))
    elif act == "dx":
        tell(net, owner, "↩️ انصراف داده شد؛ چیزی حذف نشد.")
    else:
        tell(net, owner, "این مورد دیگر وجود ندارد.")
    REPLY_TO[0] = None
    txt, kb = dest_menu(cfg0, root)
    try:
        net.api("editMessageText", {"chat_id": m["chat"]["id"], "message_id": m["message_id"], "text": txt, "reply_markup": kb})
    except (ApiError, NetError, KeyError):
        pass


def handle_update(cfg, net, state, u):
    """Routes a bot message / button to the destination it belongs to (the one you manage, or the owner of a
    pending review / forward / source button)."""
    cfg0, root = hub_of(cfg, state)
    cb = u.get("callback_query")
    if cb:
        if cb["from"]["id"] != owner_of(cfg0, root):
            return
        data = cb.get("data") or ""
        act, _, pid = data.partition(":")
        if act in ("dp", "dd", "dc", "dx"):
            dest_button(cfg0, net, root, cb, act, pid)
            return
        if act == "tx":
            cmd = TX_MAP.get(pid)
            m0 = cb.get("message") or {}
            try:
                net.api("answerCallbackQuery", {"callback_query_id": cb["id"]})
            except (ApiError, NetError):
                pass
            if cmd and m0.get("chat"):
                handle_update(cfg0, net, root, {"message": {"message_id": m0.get("message_id"), "chat": m0["chat"],
                                                            "from": cb["from"], "text": cmd}})
            return
        ps = profiles(cfg0, root)
        target = None
        if act in ("mt", "dl") and "|" in pid:
            want, _, name = pid.partition("|")
            target = next((p for p in ps if p[0] == want), None)
            cb = dict(cb, data="%s:%s" % (act, name))
        elif act in ("ok", "no"):
            target = next((p for p in ps if pid in (p[2].get("pending") or {})), None)
        elif act == "fw":
            target = next((p for p in ps if pid in (p[2].get("fwd") or {})), None)
        elif act == "rm":
            target = next((p for p in ps if pid in (p[2].get("undo") or {})), None)
        target = target or active_profile(cfg0, root)
        set_tag(target[1], target[2])
        _handle_update(target[1], net, target[2], dict(u, callback_query=cb))
        return
    m = u.get("message")
    if m and (m.get("chat") or {}).get("type") == "private" and (m.get("from") or {}).get("id") == owner_of(cfg0, root) \
            and not is_forward_or_media(m):
        REPLY_TO[0] = m.get("message_id")
        SHOW_KB[0] = (m.get("text") or "").startswith(("/start", "/menu"))
        if dest_text(cfg0, net, root, (m.get("text") or "").strip()):
            return
    p = active_profile(cfg0, root)
    set_tag(p[1], p[2])
    _handle_update(p[1], net, p[2], u)


def is_forward_or_media(m):
    return any(k in m for k in FWD_KEYS) or bool(m.get("photo") or m.get("video") or m.get("animation")
                                                 or m.get("document") or m.get("voice") or m.get("sticker"))


def entities_to_html(text, ents):
    """Telegram message text + entities -> HTML (offsets are in UTF-16 units)."""
    u = text.encode("utf-16-le")
    n = len(u) // 2

    def seg(a, b):
        return html.escape(u[a * 2:b * 2].decode("utf-16-le", "replace"), quote=False)

    tags = []
    for e in ents or []:
        try:
            o, ln, t = int(e["offset"]), int(e["length"]), e.get("type")
        except (KeyError, TypeError, ValueError):
            continue
        if o < 0 or ln <= 0 or o + ln > n:
            continue
        simple = {"bold": "b", "italic": "i", "underline": "u", "strikethrough": "s", "code": "code",
                  "pre": "pre", "spoiler": "tg-spoiler"}
        if t in simple:
            tags.append((o, o + ln, "<%s>" % simple[t], "</%s>" % simple[t]))
        elif t == "text_link" and e.get("url"):
            tags.append((o, o + ln, '<a href="%s">' % html.escape(e["url"], quote=True), "</a>"))
        elif t == "url":
            link = u[o * 2:(o + ln) * 2].decode("utf-16-le", "replace")
            if not re.match(r"[a-z]+://", link, re.I):
                link = "http://" + link
            tags.append((o, o + ln, '<a href="%s">' % html.escape(link, quote=True), "</a>"))
    tags.sort(key=lambda x: (x[0], -x[1]))

    def build(a, b, items):
        out, pos, i = [], a, 0
        while i < len(items):
            st, en, op, cl = items[i]
            if st < pos:
                i += 1
                continue
            out.append(seg(pos, st))
            j, kids = i + 1, []
            while j < len(items) and items[j][0] < en:
                if items[j][1] <= en:
                    kids.append(items[j])
                j += 1
            out.append(op + build(st, en, kids) + cl)
            pos, i = en, j
        out.append(seg(pos, b))
        return "".join(out)

    return build(0, n, tags)


def crisis_active(state):
    mode = state.get("crisis_mode", "auto")
    return mode == "on" or (mode == "auto" and bool(state.get("crisis_auto")))


def forward_kb(pid, kind):
    return {"inline_keyboard": [[{"text": "🔁 ارسال به‌هرحال" if kind == "fw" else "🗑 حذف از کانال",
                                  "callback_data": "%s:%s" % (kind, pid)}]]}


def hours_ago(t):
    h = max(0, (time.time() - t) / 3600.0)
    return "کمتر از ۱ ساعت" if h < 1 else "حدود %d ساعت" % round(h) if h < 48 else "%d روز" % round(h / 24)


def publish_forward(cfg, net, state, owner, ttext, media, fp, pid):
    """Send it to the channel now, remember it (so no later post repeats it), offer an undo button."""
    now = int(time.time())
    dcfg = dict(cfg, _no_wm=True) if crisis_active(state) else cfg
    net.last_sent = []
    try:
        deliver(net, dcfg, {"id": 0, "media": media}, ttext)
    except Skip as e:
        return "⚠️ ارسال نشد: %s" % e, None
    except ApiError as e:
        return "⚠️ تلگرام این پست را نپذیرفت: %s" % e.desc, None
    except NetError as e:
        return "⚠️ مشکل شبکه، ارسال نشد: %s" % e, None
    hist = state.setdefault("fp", [])
    hist.append(dict(fp, t=now, man=True, pid=pid))
    state.setdefault("posted_log", []).append(now)
    stat_add(state, cfg, "posted")
    und = state.setdefault("undo", {})
    und[pid] = {"ids": [list(x) for x in getattr(net, "last_sent", [])], "t": now}
    for k in [k for k, v in und.items() if now - v.get("t", 0) > 2 * 86400]:
        und.pop(k)
    return "✅ در کانال گذاشته شد.", forward_kb(pid, "rm")


def handle_forward(cfg, net, state, owner, msgs):
    msgs = sorted(msgs, key=lambda x: x.get("message_id", 0))
    REPLY_TO[0] = msgs[0].get("message_id") if msgs else None
    try:
        _handle_forward(cfg, net, state, owner, msgs)
    finally:
        REPLY_TO[0] = None


def _handle_forward(cfg, net, state, owner, msgs):
    media, text, ents = [], "", []
    for m in msgs:
        if any(m.get(k) for k in FWD_BAD):
            tell(net, owner, "این نوع پیام (ویس، فایل، استیکر، گیف، نظرسنجی...) را نمی‌توانم بفرستم. "
                 "فقط متن، عکس و ویدیو.", MENU_KB)
            return
        if m.get("photo"):
            media.append(("photo", "tgfile:" + m["photo"][-1]["file_id"]))
        elif m.get("video"):
            media.append(("video", "tgfile:" + m["video"]["file_id"]))
        t = m.get("caption") if (m.get("photo") or m.get("video")) else m.get("text")
        if t and not text:
            text = t
            ents = m.get("caption_entities") or m.get("entities") or []
    if not text and not media:
        tell(net, owner, "متن یا عکس و ویدیویی برای ارسال پیدا نشد.", MENU_KB)
        return
    rules = Rules(cfg)
    ttext = build_text(cfg, rules, entities_to_html(text, ents))
    now = time.time()
    hist = state.setdefault("fp", [])
    hist[:] = [e for e in hist if now - e.get("t", 0) < 14 * 86400][-400:]
    fp = text_fp(norm_for_dedupe(ttext, rules.own))
    exact, look = media_info(net, media) if media else ([], [])
    fp["m"] = exact
    if look:
        fp["p"] = look
    fp["man"] = True
    pid = hashlib.sha1((ttext + repr(media) + str(int(now))).encode("utf-8")).hexdigest()[:8]
    dup = find_dup(fp, hist)
    if dup:
        fw = state.setdefault("fwd", {})
        fw[pid] = {"text": ttext, "media": [list(x) for x in media], "fp": fp, "t": int(now),
                   "mid": msgs[0].get("message_id")}
        for k in [k for k, v in fw.items() if now - v.get("t", 0) > 86400]:
            fw.pop(k)
        tell(net, owner, "⛔ تکراری است: مشابه همین پست قبلاً در کانال گذاشته شده (%s پیش). نفرستادم.\n"
             "اگر مطمئنید دوباره بفرستد، دکمه‌ی زیر را بزنید." % hours_ago(dup.get("t", now)), forward_kb(pid, "fw"))
        return
    msg, kb = publish_forward(cfg, net, state, owner, ttext, media, fp, pid)
    tell(net, owner, msg, kb or MENU_KB)


def flush_forwards(cfg, net, state):
    """Album parts that stopped arriving (2 s of silence) are published as one post."""
    done = False
    for gid in [g for g, b in FWD_BUF.items() if time.time() - b["t"] >= 2.0]:
        b = FWD_BUF.pop(gid)
        try:
            pc, ps = b.get("pf") or (cfg, state)
            set_tag(pc, ps)
            handle_forward(pc, net, ps, owner_of(cfg, state), b["msgs"])
        except Exception:
            log.exception("could not process a forwarded album")
        done = True
    return done


def forward_button(cfg, net, state, cb, act, pid):
    owner = owner_of(cfg, state)
    note = "این مورد منقضی شده"
    m = cb.get("message") or {}
    if act == "fw":
        item = (state.get("fwd") or {}).pop(pid, None)
        if item:
            REPLY_TO[0] = item.get("mid")
            msg, kb = publish_forward(cfg, net, state, owner, item["text"],
                                      [tuple(x) for x in item["media"]], item.get("fp") or {}, pid)
            note = msg
            if kb:
                tell(net, owner, msg, kb)
            REPLY_TO[0] = None
    else:
        item = (state.get("undo") or {}).pop(pid, None)
        if item:
            gone = 0
            for chat, mid in item.get("ids", []):
                try:
                    net.api("deleteMessage", {"chat_id": chat, "message_id": mid})
                    gone += 1
                except (ApiError, NetError) as e:
                    log.warning("could not delete a message: %s", getattr(e, "desc", e))
            state["fp"] = [e for e in state.get("fp", []) if e.get("pid") != pid]
            note = "🗑 از کانال حذف شد." if gone else "⚠️ حذف نشد (شاید قبلاً حذف شده یا مدتی گذشته)."
    try:
        net.api("editMessageText", {"chat_id": m["chat"]["id"], "message_id": m["message_id"],
                                    "text": (m.get("text") or "") + "\n\n" + note})
    except (ApiError, NetError, KeyError):
        pass
    try:
        net.api("answerCallbackQuery", {"callback_query_id": cb["id"], "text": note[:150]})
    except (ApiError, NetError):
        pass


def heartbeat(cfg, net, state):
    """Once a day (after 07:30 Iran time) tell the owner the bot is alive."""
    owner = owner_of(cfg, state)
    if not owner or isinstance(state, SubState):
        return
    now = time.time()
    lt = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60)
    day = "%04d-%02d-%02d" % (lt.tm_year, lt.tm_mon, lt.tm_mday)
    if (lt.tm_hour, lt.tm_min) < (7, 30) or state.get("hb_day") == day:
        return
    TAG[0] = ""
    txt = "🟢 ربات از سمت گیت‌هاب فعال است.\n"
    for pid_, c, st in profiles(cfg, state):
        log_ = [t for t in st.get("posted_log", []) if now - t < 86400]
        if state.get("dests"):
            txt += "%s: %s، %d پست در ۲۴ ساعت گذشته\n" % (
                c["target_channel"], "⏸ خاموش" if st.get("paused") else "روشن", len(log_))
        else:
            txt += "وضعیت: " + ("⏸ خاموش (با دکمه‌ی شما)" if st.get("paused") else "روشن") + "\n"
            txt += "پست‌های ارسال‌شده در ۲۴ ساعت گذشته: %d" % len(log_)
    if tell(net, owner, txt, MENU_KB) is not None:
        state["hb_day"] = day



def review_worthy(cfg, reason):
    if not cfg["review_suspicious"] or not reason:
        return False
    if reason.startswith("ad keyword"):
        return bool(cfg["review_keyword_ads"])
    return reason.startswith(("ad word", "contains a link", "mentions another", "contains a channel invite"))


def send_for_review(net, cfg, state, tag, src, p, text, reason):
    owner = owner_of(cfg, state)
    pid = hashlib.sha1(("%s/%s" % (tag, p["id"])).encode()).hexdigest()[:8]
    ocfg = dict(cfg, target_channel=owner, _no_wm=True)
    try:
        deliver(net, ocfg, p, text)
    except (Skip, ApiError, NetError) as e:
        log.warning("[%s] could not show it to the owner: %s", tag, getattr(e, "desc", e))
        return False
    state.setdefault("pending", {})[pid] = {
        "text": text, "media": [list(x) for x in p["media"]], "t": int(time.time())}
    ask = "☝️ این پست مشکوک به تبلیغ بود (%s) از کانال %s.\nارسال شود؟\n(اگر تا ۲ ساعت جواب ندهید، خودکار رد می‌شود.)" % (reason, src)
    r = tell(net, owner, ask, {
        "inline_keyboard": [[{"text": "✅ ارسال", "callback_data": "ok:" + pid},
                             {"text": "❌ رد", "callback_data": "no:" + pid}]]})
    if isinstance(r, dict) and r.get("message_id"):
        state["pending"][pid].update(mid=r["message_id"], chat=owner, ask=ask)
    return True


PENDING_TTL = 2 * 3600


def expire_pending(cfg, net, state, now=None):
    """Same for every destination (called from the main loop)."""
    cfg0, root = hub_of(cfg, state)
    done = False
    for pid_, c, st in profiles(cfg0, root):
        done = _expire_pending(c, net, st, now) or done
    return done


def _expire_pending(cfg, net, state, now=None):
    """Posts waiting for your decision for more than 2 hours count as rejected."""
    now = now or time.time()
    old = [k for k, v in state.get("pending", {}).items() if now - v.get("t", 0) > PENDING_TTL]
    for k in old:
        v = state["pending"].pop(k)
        if v.get("mid"):
            try:
                net.api("editMessageText", {"chat_id": v["chat"], "message_id": v["mid"],
                                            "text": v.get("ask", "") + "\n\n⏳ ۲ ساعت بدون جواب ماند؛ خودکار رد شد."})
            except (ApiError, NetError):
                pass
    return bool(old)


def spread_by_channel(items):
    """Random order in which no source appears twice in a row (as far as the choice allows) and every
    source gets its turn before any source gets a second one - so a busy channel cannot fill a round."""
    approved = [i for i in items if i[0].startswith("approved/")]
    groups = {}
    for i in items:
        if not i[0].startswith("approved/"):
            groups.setdefault(i[0].split("/")[0], []).append(i)
    out, last = list(approved), None
    while groups:
        # sources with the fewest posts already placed come first: fair share
        placed = {}
        for i in out:
            placed[i[0].split("/")[0]] = placed.get(i[0].split("/")[0], 0) + 1
        low = min(placed.get(g, 0) for g in groups)
        pool = [g for g in groups if placed.get(g, 0) == low and g != last] or \
               [g for g in groups if g != last] or list(groups)
        g = random.choice(pool)
        it = max(groups[g], key=lambda i: i[1].get("id", 0))      # the newest post of that source first
        groups[g].remove(it)
        if not groups[g]:
            del groups[g]
        out.append(it)
        last = g
    return out


def pick_and_order(items, limit):
    """Take up to `limit` items (random order already) and arrange them so that no two
    text-only posts (no photo/video) are next to each other."""
    media = [i for i in items if i[1]["media"]]
    texts = [i for i in items if not i[1]["media"]]
    pick = []
    for i in items:                               # fair: first come in the random order
        if len(pick) >= limit:
            break
        pick.append(i)
    pm = [i for i in pick if i[1]["media"]]
    pt = [i for i in pick if not i[1]["media"]]
    spare = [i for i in media if i not in pick]
    while len(pt) > len(pm) + 1:                  # too many text posts to separate
        pt.pop()
        if spare:
            pm.append(spare.pop(0))
    # alternate, starting with whichever group is bigger (media first on a tie)
    out = []
    a, b = (pt, pm) if len(pt) > len(pm) else (pm, pt)
    while a or b:
        if a:
            out.append(a.pop(0))
        if b:
            out.append(b.pop(0))
    return out


SKIP_GROUPS = (("ad ", "تبلیغ"), ("link to blocked", "لینک/سایت"), ("contains a link", "لینک/سایت"),
               ("mentions another", "کانال یا ربات دیگر"), ("contains a channel invite", "کانال یا ربات دیگر"),
               ("it is forwarded", "فوروارد"), ("it is a reply", "ریپلای"), ("media type", "رسانه‌ی نامناسب"))


def iran_day(cfg, now):
    lt = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60)
    return "%04d-%02d-%02d" % (lt.tm_year, lt.tm_mon, lt.tm_mday), lt


def src_key(name):
    return hashlib.sha1(name.lower().encode("utf-8")).hexdigest()[:10]


def skip_group(what):
    return "تکراری" if what == "dup" else next((g for p, g in SKIP_GROUPS if what.startswith(p)), "سایر")


def stat_add(state, cfg, what, key=None, n=1):
    """Counters for the daily report: what = 'posted' | 'dup' | 'crisis' | a skip reason text."""
    day = iran_day(cfg, time.time())[0]
    st = state.get("stats")
    if not isinstance(st, dict) or st.get("day") != day:
        return                                   # daily_report() starts a fresh day
    if what == "posted":
        st["posted"] = st.get("posted", 0) + n
        if key:
            by = st.setdefault("by_src", {})
            by[key] = by.get(key, 0) + n
    elif what == "crisis":
        st["crisis"] = st.get("crisis", 0) + n
    else:
        grp = skip_group(what)
        sk = st.setdefault("skip", {})
        sk[grp] = sk.get(grp, 0) + n


def report_text(cfg, st):
    names = {src_key(n): n for n in cfg["sources"]}
    lines = ["📊 گزارش روز %s" % st["day"], "✅ ارسال‌شده: %d" % st.get("posted", 0)]
    by = sorted(st.get("by_src", {}).items(), key=lambda x: -x[1])
    if by:
        lines.append("منبع‌ها: " + "، ".join("%s %d" % (names.get(k, "؟"), v) for k, v in by))
    sk = st.get("skip", {})
    lines.append("⛔ ردشده: " + ("، ".join("%s %d" % (g, v) for g, v in sorted(sk.items(), key=lambda x: -x[1])) or "هیچ"))
    if st.get("crisis"):
        lines.append("🚨 حالت بحران %d بار خودکار فعال شد" % st["crisis"])
    return "\n".join(lines)


def daily_report(cfg, net, state, now):
    """One short summary per day in the bot chat (default 23:30 Iran time)."""
    owner = owner_of(cfg, state)
    day, lt = iran_day(cfg, now)
    st = state.get("stats")
    if not isinstance(st, dict) or "day" not in st:
        state["stats"] = {"day": day, "posted": 0}
        return
    if st["day"] != day:                          # a new day began: close the old one first
        if owner and state.get("rep_day") != st["day"]:
            tell(net, owner, report_text(cfg, st), MENU_KB)
        state["stats"] = {"day": day, "posted": 0}
        return
    h, m = cfg["report_time"]
    if owner and state.get("rep_day") != day and (lt.tm_hour, lt.tm_min) >= (int(h), int(m)):
        if tell(net, owner, report_text(cfg, st), MENU_KB) is not None:
            state["rep_day"] = day


def crisis_eval(cfg, net, state, now, counts):
    """Count the new posts of this scan, switch auto crisis on/off, return True while crisis is active."""
    arr = state.setdefault("arrivals", [])
    gap = now - state.get("last_scan_ts", now)
    state["last_scan_ts"] = int(now)
    if gap > 90 * 60:                              # the bot was away: that is catching up, not a burst
        counts = {}
    total_now = sum(counts.values())
    if total_now:
        arr.append([int(now), total_now, counts])
    arr[:] = [a for a in arr if now - a[0] < 3600]
    win = [a for a in arr if now - a[0] <= 1800]
    total = sum(a[1] for a in win)
    per = {}
    for a in win:
        for k, n in a[2].items():
            per[k] = per.get(k, 0) + n
    hot = sum(1 for n in per.values() if n >= int(cfg["crisis_channel_rate"]))
    mode = state.get("crisis_mode", "auto")
    owner = owner_of(cfg, state)
    if mode == "auto":
        if not state.get("crisis_auto"):
            if total >= int(cfg["crisis_on_rate"]) or hot >= int(cfg["crisis_on_channels"]):
                state["crisis_auto"] = int(now)
                state.pop("crisis_calm_since", None)
                stat_add(state, cfg, "crisis")
                log.info("crisis mode switched ON automatically (%d new posts in 30 min)", total)
                if owner:
                    tell(net, owner, "🚨 تعداد پست‌ها ناگهان بالا رفت (%d پست تازه در ۳۰ دقیقه). حالت بحران "
                         "خودکار روشن شد. دورها کوتاه‌تر، تا ۳ پست آخر هر کانال و لیبل عکس‌ها غیرفعال. "
                         "با دکمه‌ی «بحران: خاموش» می‌توانید خاموشش کنید." % total, MENU_KB)
        else:
            off = False
            if total < int(cfg["crisis_off_rate"]):
                since = state.setdefault("crisis_calm_since", int(now))
                off = now - since >= 20 * 60
            else:
                state.pop("crisis_calm_since", None)
            if now - state["crisis_auto"] > float(cfg["crisis_max_hours"]) * 3600:
                off = True
            if off:
                state["crisis_auto"] = 0
                state.pop("crisis_calm_since", None)
                log.info("crisis mode switched OFF automatically")
                if owner:
                    tell(net, owner, "✅ اوضاع آرام شد؛ حالت بحران خودکار خاموش شد و ربات به حالت عادی برگشت.", MENU_KB)
    return mode == "on" or (mode == "auto" and bool(state.get("crisis_auto")))


def run_cycle_latest(cfg, net, rules, state, state_path, dry, force=False):
    """One posting round: the newest post of every source (in crisis mode the newest few), if new and
    not an ad, duplicates removed, random order, at most max_posts_per_run posts, then a pause."""
    now = time.time()
    notify = manual = False
    if not dry:
        set_tag(cfg, state)
        if not isinstance(state, SubState):        # the bot's messages are read once per loop (by the main destination)
            process_updates(cfg, net, state, state_path)
        set_tag(cfg, state)
        apply_overrides(cfg, state)                # sources / banned words changed from the bot
        heartbeat(cfg, net, state)
        daily_report(cfg, net, state, now)
        hours_update(cfg, net, state, now)
        state["posted_log"] = [t for t in state.get("posted_log", []) if now - t < 3 * 86400]
        if state.get("paused"):
            state.pop("run_now", None)
            log.info("switched OFF from the bot - nothing is posted")
            return
        notify = bool(state.pop("run_now", None))
        # "send now": an extra round right away. The regular schedule (next_run_ts) stays untouched.
        manual = notify and now < state.get("next_run_ts", 0)
    nxt = state.get("next_run_ts", 0)
    if not force and not dry and not manual and now < nxt:
        log.info("waiting - next posting round in about %d min", int((nxt - now) / 60) + 1)
        return
    if not cfg["sources"] and not dry:
        log.info("no sources for this destination yet - nothing to do")
        state["next_run_ts"] = time.time() + 600
        return
    # --- 1. read every source page, count what is new ---
    names = list(cfg["sources"])
    random.shuffle(names)
    pages, counts = [], {}
    for name in names:
        key = src_key(name)
        label = key if IN_CLOUD else name
        try:
            posts = parse_page(net.get(cfg["web_base"] + name))
        except NetError as e:
            log.warning("[%s] cannot open channel page: %s", label, e)
            continue
        if not posts:
            log.warning("[%s] no posts found - is the username right and the channel public?", label)
            continue
        st = state["channels"].setdefault(key, {})
        if is_muted(state, name):                  # muted from the bot: everything new counts as seen
            if not dry:
                st["last_id"] = posts[-1]["id"]
            log.info("[%s] muted - skipped", label)
            continue
        if "last_id" not in st:
            st["last_id"] = posts[-1]["id"] - 1   # first run: the newest post counts too
        new = [p for p in posts if p["id"] > st["last_id"]]
        if new:
            # an album shows up as several posts with the same time: it is ONE post; and one noisy channel
            # may not push the crisis counter alone, so each source counts at most 6 per scan
            groups = len({p["ts"] if p.get("ts") else ("id", p["id"]) for p in new})
            counts[key] = min(groups, 6)
        pages.append((name, key, label, st, new))
    crisis = False if dry else crisis_eval(cfg, net, state, now, counts)
    if crisis:
        log.info("CRISIS MODE is active: up to %d newest posts per source, short rounds, no photo label",
                 int(cfg["crisis_posts_per_channel"]))
    hour = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60).tm_hour
    n0, n1 = cfg["night_hours"]
    custom = (not dry) and (not crisis)           # speed modes (low/mid/high/manual/auto) apply
    night = False
    mode_desc = ""
    limit = 0
    if crisis:
        limit = int(cfg["crisis_max_posts"])
    elif custom:
        limit, night, mode_desc = round_target(cfg, state, now)
        if manual:
            limit = max(1, limit)                 # "send now" always tries for at least one post
        log.info("speed %s: this round should end with %d post(s)", mode_desc, limit)
        if limit <= 0:                            # a deliberately empty round (quiet hours): nothing consumed
            a, b = cfg["night_interval_minutes"] if night else cfg["interval_minutes"]
            state["next_run_ts"] = time.time() + random.uniform(float(a), float(b)) * 60
            state["last_round"] = {"t": int(time.time()), "found": sum(len(p[4]) for p in pages), "considered": 0,
                                   "posted": 0, "over": 0, "appr": 0, "rej": {}, "src": {}, "crisis": False,
                                   "mode": mode_desc, "target": 0, "why": [], "ign": {}}
            save_state(state_path, state)
            log.info("quiet round (target 0): nothing posted, posts stay available for the next round")
            return
    else:
        limit = int(cfg["max_posts_per_run"]) or 99
    # --- 2. choose candidates ---
    rec = {"found": sum(len(p[4]) for p in pages), "considered": 0, "posted": 0, "over": 0, "appr": 0,
           "rej": {}, "src": {p[1]: [len(p[4]), 0] for p in pages if p[4]}, "crisis": bool(crisis), "mode": mode_desc,
           "target": limit, "why": [], "ign": {}}

    def note(key, pid, text):
        if len(rec["why"]) < 40:
            rec["why"].append([key, pid, text])
    lab2key = {p[2]: p[1] for p in pages}
    reviewed = 0
    maxl = int(cfg["crisis_posts_per_channel"]) if crisis else int(cfg["widen_max_layers"]) if custom else 1
    maxage = float(cfg["widen_max_age_minutes"]) * 60
    done = {}                                     # how many of every source's new posts were looked at
    hist = state.setdefault("fp", [])
    hist[:] = [e for e in hist if now - e.get("t", 0) < 14 * 86400][-400:]
    eligible = []
    appr = state.get("approved", [])
    state["approved"] = []
    for a in appr:                                # posts you approved in the bot go first
        if now - a.get("t", 0) > 2 * 86400:
            continue
        fp = text_fp(norm_for_dedupe(a["text"], rules.own))
        fp["m"] = []
        if find_dup(fp, hist):
            continue
        eligible.append(("approved/" + hashlib.sha1(a["text"].encode()).hexdigest()[:6],
                         {"id": 0, "media": a["media"]}, a["text"], fp, None))
    _expire_pending(cfg, net, state, now)
    if not dry:
        for name, key, label, st, new in pages:
            if new:
                st["last_id"] = new[-1]["id"]     # whatever happens, these are never reconsidered
    chosen = []
    for layer in range(1, maxl + 1):
        cands = []
        for name, key, label, st, new in pages:
            if len(new) < layer:
                continue
            p = new[-layer]
            if layer >= 2 and not crisis and p.get("ts") and now - p["ts"] > maxage:
                continue                          # too old to be worth posting
            done[key] = done.get(key, 0) + 1
            rec["considered"] += 1
            reason = skip_reason(cfg, p)
            if reason:
                g = skip_group(reason)
                rec["rej"][g] = rec["rej"].get(g, 0) + 1
                why = explain_skip(reason, p)
                log.info("[%s/%d] skipped: %s", label, p["id"], reason)
                if not dry:
                    stat_add(state, cfg, reason)
                    if (owner_of(cfg, state) and not state.get("review_off") and review_worthy(cfg, reason)
                            and reviewed < int(cfg["review_max_per_round"])):
                        txt = build_text(cfg, rules, p["text_html"])
                        if send_for_review(net, cfg, state, label, name, p, txt, reason):
                            reviewed += 1
                            why += " ← برای تأیید شما فرستاده شد (پیام جدا با دکمه‌ی ارسال/رد)"
                            time.sleep(2)
                note(src_key(name), p["id"], why)
                continue
            cands.append((label, st, p))
        for label, st, p in cands:                # candidates are already in random order
            tag = "%s/%d" % (label, p["id"])
            text = build_text(cfg, rules, p["text_html"])
            fp = text_fp(norm_for_dedupe(text, rules.own))
            fp["m"], look = media_info(net, p["media"]) if p["media"] else ([], [])
            if look:
                fp["p"] = look
            d, dwhy = find_dup_why(fp, hist + [c[3] for c in eligible])
            if d:
                log.info("[%s] skipped: duplicate of a post already sent/selected", tag)
                rec["rej"]["تکراری"] = rec["rej"].get("تکراری", 0) + 1
                note(lab2key.get(label, ""), p["id"], "تکراری: %s؛ %s" % (
                    dwhy, ("مشابهش %s پیش در کانال گذاشته شده بود" % hours_ago(d["t"])) if d.get("t") else
                    "در همین دور از کانال دیگری هم رسید و همان یکی ارسال شد"))
                if not dry:
                    stat_add(state, cfg, "dup")
                continue
            eligible.append((tag, p, text, fp, st))
        if not crisis:
            eligible = spread_by_channel(eligible)
        chosen = pick_and_order(eligible, limit)
        if custom and not crisis and len(chosen) >= limit:
            break                                 # the wanted number is reached: no need to look further back
        if custom and not crisis and layer == 2 and len(chosen) < limit:
            log.info("only %d of %d wanted posts so far: also looking at older posts of each source", len(chosen), limit)
    for name, key, label, st, new in pages:
        if len(new) > done.get(key, 0):
            rec["ign"][key] = len(new) - done.get(key, 0)
    if custom and len(chosen) < limit:
        rec["short"] = limit - len(chosen)
    for item in eligible:
        if item not in chosen:
            log.info("[%s] not chosen this time", item[0])
            if not item[0].startswith("approved/"):
                rec["over"] += 1
                note(lab2key.get(item[0].split("/")[0], ""), item[1]["id"],
                     ("جا نشد: سقف %d پست در این دور پر شده بود" % limit) if len(chosen) >= limit else
                     "کنار گذاشته شد تا دو پست فقط‌متنی پشت‌سرهم نیایند")
            if item[0].startswith("approved/"):   # approved by you: keep it for the next round
                state["approved"].append({"text": item[2], "media": item[1]["media"], "t": int(now)})
    if not dry:
        save_state(state_path, state)
    lo, hi = cfg["crisis_delay_seconds"] if crisis else cfg["random_delay_seconds"]
    dcfg = dict(cfg, _no_wm=True) if crisis else cfg      # no ID label on photos during a crisis
    keys = {src_key(n): n for n in cfg["sources"]}
    posted = 0
    for i, (tag, p, text, fp, st) in enumerate(chosen):
        if dry:
            log.info("[%s] WOULD POST (%d media):\n%s\n----", tag, len(p["media"]), text)
            continue
        try:
            deliver(net, dcfg, p, text)
            log.info("[%s] posted", tag)
            hist.append(dict(fp, t=int(time.time())))
            state.setdefault("posted_log", []).append(int(time.time()))
            stat_add(state, cfg, "posted", tag.split("/")[0] if tag.split("/")[0] in keys else None)
            posted += 1
            if tag.split("/")[0] in lab2key:
                rec["src"].setdefault(lab2key[tag.split("/")[0]], [0, 0])[1] += 1
            else:
                rec["appr"] += 1
        except Skip as e:
            log.warning("[%s] skipped: %s", tag, e)
            note(lab2key.get(tag.split("/")[0], ""), p["id"], "ارسال نشد: %s" % e)
        except NetError as e:
            log.warning("[%s] network problem: %s", tag, e)
            note(lab2key.get(tag.split("/")[0], ""), p["id"], "ارسال نشد: مشکل شبکه (%s)" % e)
        except ApiError as e:
            log.error("[%s] Telegram refused: %s", tag, e.desc)
            note(lab2key.get(tag.split("/")[0], ""), p["id"], "ارسال نشد: تلگرام نپذیرفت (%s)" % e.desc)
        save_state(state_path, state)
        if i < len(chosen) - 1:
            time.sleep(random.uniform(float(lo), float(hi)))
    if not dry and rec["found"]:                  # what the bot's "status" button shows
        rec.update(t=int(time.time()), posted=posted)
        state["last_manual" if manual else "last_round"] = rec
    if not posted and not dry and not manual:
        state["next_run_ts"] = max(state.get("next_run_ts", 0), time.time() + 120)
        save_state(state_path, state)
    if posted and not dry and not manual:
        a, b = (cfg["crisis_interval_minutes"] if crisis
                else cfg["night_interval_minutes"] if night else cfg["interval_minutes"])
        state["next_run_ts"] = time.time() + random.uniform(float(a), float(b)) * 60
        save_state(state_path, state)
        log.info("round finished: %d posted, next round in %d-%d min or later", posted, a, b)
    if manual and not dry:
        save_state(state_path, state)
        log.info("send-now round finished: %d posted (regular schedule unchanged)", posted)
    if notify and not dry and owner_of(cfg, state):
        left = max(0, state.get("next_run_ts", 0) - time.time())
        tell(net, owner_of(cfg, state),
             ("⚡ ارسال فوری انجام شد: %d پست گذاشته شد." % posted) if posted else
             "⚡ الان پست تازه‌ی قابل‌ارسالی نیست (یا همه تکراری/ردشده‌اند).",
             MENU_KB)
        if manual:
            log.info("regular round in about %d min", left // 60 + 1)


def dump(cfg, net, rules, n, state=None, total=0):
    """TEST ONLY: send the last n posts of every source to the test channel exactly as they
    would be published (clean - no notes inside the channel). What was skipped and why goes
    to the owner's private chat with the bot."""
    if not cfg.get("_test_mode"):
        die("--dump works only in TEST MODE (target_override.txt must exist) so it can never "
            "flood your real channel.")
    owner = owner_of(cfg, state or {})
    seen = []
    sent_n = 0
    order = list(enumerate(cfg["sources"], 1))
    if total:
        random.shuffle(order)                      # fair: every source has the same chance
    for si, name in order:
        if total and sent_n >= total:
            break
        try:
            posts = parse_page(net.get(cfg["web_base"] + name))[-n:]
        except NetError as e:
            log.warning("[source %d] cannot open: %s", si, e)
            continue
        log.info("[source %d] %d posts", si, len(posts))
        report = ["📋 %s" % name]
        for p in posts:
            if total and sent_n >= total:
                break
            reason = skip_reason(cfg, p)
            text = build_text(cfg, rules, p["text_html"])
            fp = text_fp(norm_for_dedupe(text, rules.own))
            fp["m"] = media_hashes(net, p["media"]) if p["media"] else []
            dup = None if reason else find_dup(fp, [e for e, _ in seen])
            snippet = plain(p["text_html"]).replace("\n", " ")[:40]
            if reason:
                report.append("⛔ #%d رد شد: %s | %s" % (p["id"], reason, snippet))
                continue
            if dup:
                report.append("♻️ #%d تکراری (مثل %s) | %s" % (
                    p["id"], [t for e, t in seen if e is dup][0], snippet))
                continue
            seen.append((fp, "%s #%d" % (name, p["id"])))
            try:
                deliver(net, cfg, p, text)
                sent_n += 1
                report.append("✅ #%d ارسال شد | %s" % (p["id"], snippet))
            except (Skip, ApiError) as e:
                log.warning("[source %d/%d] not sent: %s", si, p["id"], getattr(e, "desc", e))
                report.append("⚠️ #%d ارسال نشد: %s" % (p["id"], getattr(e, "desc", e)))
            except NetError as e:
                log.warning("[source %d/%d] network problem: %s", si, p["id"], e)
            time.sleep(3.5)
    log.info("dump finished")


def check(cfg, net):
    ok = True
    shown = "your channel" if IN_CLOUD else cfg["target_channel"]  # cloud logs are public
    print("\n--- Checking bot and your channel ---")
    try:
        me = net.api("getMe")
        print("OK: bot token works (bot: @%s)" % me.get("username"))
    except (ApiError, NetError) as e:
        print("PROBLEM: cannot use the bot token / reach Telegram: %s" % getattr(e, "desc", e))
        print("  -> Turn your VPN on, or fix bot_token in config.json (or set 'proxy').")
        return False
    try:
        chat = net.api("getChat", {"chat_id": cfg["target_channel"]})
        can_post = None
        try:
            mem = net.api("getChatMember", {"chat_id": chat["id"], "user_id": me["id"]})
            can_post = mem.get("status") == "creator" or (
                mem.get("status") == "administrator" and mem.get("can_post_messages", True))
        except ApiError as e:
            # Telegram sometimes refuses this call; try an invisible probe instead
            print("   (member lookup said: %s - trying a direct test)" % e.desc)
            try:
                net.api("sendChatAction", {"chat_id": chat["id"], "action": "typing"})
                can_post = True
            except ApiError as e2:
                print("   (direct test said: %s)" % e2.desc)
                can_post = False
        if can_post:
            print("OK: the bot can post in %s" % shown)
        else:
            ok = False
            print("PROBLEM: this bot (@%s) cannot post in %s. Add exactly this bot as an"
                  " admin with 'Post messages' permission." % (me.get("username"), shown))
    except ApiError as e:
        ok = False
        print("PROBLEM: %s -> check target_channel spelling and add the bot as admin." % e.desc)
    except NetError as e:
        print("PROBLEM: network: %s" % e)
        return False
    print("\n--- Checking source channels ---")
    for i, src in enumerate(cfg["sources"]):
        name = ("source #%d" % (i + 1)) if IN_CLOUD else src  # logs are public in the cloud
        try:
            posts = parse_page(net.get(cfg["web_base"] + src))
        except NetError as e:
            ok = False
            print("PROBLEM: [%s] cannot open page: %s" % (name, e))
            continue
        if not posts:
            ok = False
            print("PROBLEM: [%s] no posts found - wrong username or the channel is not public" % name)
            continue
        reasons = {}
        for p in posts:
            r = skip_reason(cfg, p)
            if r:
                if IN_CLOUD:  # keep details (site names, words) out of public logs
                    r = re.sub(r"\s*\(.*?\)|\s*'.*?'", "", r)
                reasons[r] = reasons.get(r, 0) + 1
        skipped = sum(reasons.values())
        print("OK: [%s] %d recent posts visible, %d of them would be skipped (ads/unsupported)"
              % (name, len(posts), skipped))
        for r, c in sorted(reasons.items(), key=lambda x: -x[1]):
            print("   skipped %d x: %s" % (c, r))
        print("   with media: %d, text only: %d" % (
            sum(1 for p in posts if p["media"]), sum(1 for p in posts if not p["media"])))
        if skipped == len(posts) and len(posts) > 3:
            print("   WARNING: everything is being skipped - run  python repost.py --dry-run  to see why")
    print("\n" + ("ALL GOOD - you can start run.bat" if ok else "Fix the problems above, then run check again"))
    return ok


def state_digest(state):
    """What matters for saving: everything except the bot-message counter."""
    d = dict(state)
    d.pop("update_offset", None)
    return hashlib.sha1(json.dumps(d, sort_keys=True).encode()).hexdigest()


def git_push_state(path):
    """Cloud only: keep state.json safe in the repository while the long run is still alive."""
    import subprocess
    try:
        run = lambda *a: subprocess.run(a, check=False, capture_output=True, timeout=120)
        run("git", "config", "user.name", "repost-bot")
        run("git", "config", "user.email", "repost-bot@users.noreply.github.com")
        run("git", "add", path)
        if run("git", "diff", "--cached", "--quiet").returncode != 0:
            run("git", "commit", "-m", "update state")
            if run("git", "push").returncode != 0:
                run("git", "pull", "--rebase", "--autostash")
                run("git", "push")
    except Exception as e:
        log.warning("could not save state to the repository yet: %s", e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=os.path.join(BASE_DIR, "config.json"))
    ap.add_argument("--state", default=os.path.join(BASE_DIR, "state.json"))
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--serve", type=int, default=0, metavar="MINUTES",
                    help="stay alive this many minutes: answer bot buttons every ~20 s, post rounds on schedule")
    ap.add_argument("--force", action="store_true", help="ignore the pause between rounds")
    ap.add_argument("--dump", type=int, default=0, metavar="N",
                    help="TEST MODE only: send the last N posts of every source")
    ap.add_argument("--dump-total", type=int, default=0, metavar="T",
                    help="with --dump: stop after T posts in total")
    args = ap.parse_args()

    for s in (sys.stdout, sys.stderr):
        try:
            s.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s %(message)s", datefmt="%H:%M:%S",
        handlers=[logging.StreamHandler(sys.stdout),
                  logging.FileHandler(os.path.join(BASE_DIR, "repost.log"), encoding="utf-8")])

    cfg = load_config(args.config)
    net = Net(cfg)
    if args.check:
        sys.exit(0 if check(cfg, net) else 1)
    rules = Rules(cfg)
    if args.dump:
        dump(cfg, net, rules, args.dump, load_state(args.state), args.dump_total)
        return
    state = load_state(args.state)
    apply_overrides(cfg, state)
    force = args.force
    log.info("Started. %d source channel(s) -> %s", len(cfg["sources"]),
             "your channel" if IN_CLOUD else cfg["target_channel"])
    deadline = time.time() + args.serve * 60
    saved = state_digest(state)
    first = True
    while True:
        try:
            if cfg["latest_only"]:
                run_cycle_latest(cfg, net, rules, state, args.state, args.dry_run, force and first)
            else:
                run_cycle(cfg, net, rules, state, args.state, args.dry_run)
        except Exception:
            log.exception("cycle failed (will try again)")
        for pid_, pcfg, pst in profiles(cfg, state)[1:]:     # the other destinations: each one is a separate round
            try:
                run_cycle_latest(pcfg, net, Rules(pcfg), pst, args.state, args.dry_run, force and first)
            except Exception:
                log.exception("cycle of %s failed (will try again)", pcfg["target_channel"])
        first = False
        if args.serve:
            TAG[0] = ""
            d = state_digest(state)
            if d != saved and IN_CLOUD:
                git_push_state(args.state)
                saved = d
            if time.time() + 20 < deadline:
                end = time.time() + 20             # wait for bot buttons with long polling = instant
                while time.time() < end:
                    t0 = time.time()
                    try:
                        process_updates(cfg, net, state, args.state, wait=max(1, min(15, end - t0)))
                    except Exception:
                        log.exception("bot check failed (will try again)")
                    if any(p[2].get("run_now") for p in profiles(cfg, state)):
                        break
                    if time.time() - t0 < 1:       # never spin faster than once a second
                        time.sleep(1)
                continue
            break
        if args.once or args.dry_run:
            break
        time.sleep(max(60, int(cfg["check_every_seconds"])))


if __name__ == "__main__":
    main()
