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
    "crisis_on_channels": 3,               # ... or this many sources with ...
    "crisis_channel_rate": 5,              # ... at least this many new posts each within 30 min
    "crisis_off_rate": 14,                 # auto-off: below this many per 30 min for 20 minutes
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


def save_state(path, state):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=1)
    os.replace(tmp, path)


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

    def get(self, url, binary=False, timeout=40):
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


def parse_page(page):
    posts = []
    for chunk in MSG_SPLIT.split(page)[1:]:
        m = re.search(r'data-post="[^"/]+/(\d+)"', chunk)
        if not m:
            continue
        tm = TEXT_RE.search(chunk)
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
    t = balance_tags(drop_source_lines(t, rules.own))
    t = re.sub(r"[ \t]+\n", "\n", t)
    t = re.sub(r"\n{3,}", "\n\n", t).strip()
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


def find_dup(fp, entries):
    for e in entries:
        if fp.get("x") and fp["x"] == e.get("x"):
            return e
        if fp.get("h") and e.get("h") and jaccard(fp["h"], e["h"]) >= 0.8:
            return e
        if fp.get("w") and e.get("w"):
            a, b = set(fp["w"]), set(e["w"])
            inter = len(a & b)
            if inter >= 6 and (inter / float(len(a | b)) >= 0.55
                               or (min(len(a), len(b)) >= 8 and inter / float(min(len(a), len(b))) >= 0.85)):
                return e
        if fp.get("m") and set(fp["m"]) & set(e.get("m", [])):
            return e
    return None


def media_hashes(net, media):
    out = []
    for kind, url in media[:3]:
        try:
            if kind == "photo":
                out.append(hashlib.sha1(net.get(url, binary=True, timeout=30)).hexdigest()[:12])
            else:
                data, total = net.get_range(url, 262144)
                out.append(hashlib.sha1(data + str(total).encode()).hexdigest()[:12])
        except Exception:
            pass
    return out


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
    """Small readable link in the bottom-left corner (semi-transparent dark pill, white text)."""
    im = Image.open(io.BytesIO(data))
    im.load()
    im = im.convert("RGBA")
    w, h = im.size
    if min(w, h) < 200:
        return data
    size = max(11, int(min(w, h) * 0.027))
    font = _font(size)
    ov = Image.new("RGBA", im.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(ov)
    b = d.textbbox((0, 0), text, font=font)
    tw, th = b[2] - b[0], b[3] - b[1]
    padx, pady, m = int(size * 0.55), int(size * 0.35), int(size * 0.7)
    x0, y1 = m, h - m                              # bottom-left corner
    x1, y0 = x0 + tw + 2 * padx, y1 - th - 2 * pady
    d.rounded_rectangle([x0, y0, x1, y1], radius=int(size * 0.5), fill=(0, 0, 0, 70))
    d.text((x0 + padx - b[0], y0 + pady - b[1]), text, font=font, fill=(255, 255, 255, 175))
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


def send_single(net, cfg, kind, url, caption):
    method = "sendPhoto" if kind == "photo" else "sendVideo"
    payload = {"chat_id": cfg["target_channel"], kind: url}
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
                payload[kind] = url
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
BTN_OFF, BTN_ON, BTN_STATUS, BTN_REVIEW = "⏸ خاموش کردن", "▶️ روشن کردن", "📊 وضعیت", "🔍 بررسی مشکوک‌ها (روشن/خاموش)"
BTN_CR_ON, BTN_CR_OFF, BTN_CR_AUTO = "🚨 بحران: روشن", "🛑 بحران: خاموش", "🤖 بحران: خودکار"
BTN_SRC, BTN_BAN, BTN_HOURS = "📋 منبع‌ها", "🚫 کلمات ممنوع", "⏰ ساعت‌های پربازدید"
MENU_KB = {"keyboard": [[{"text": BTN_OFF}, {"text": BTN_ON}], [{"text": BTN_STATUS}],
                        [{"text": BTN_CR_ON}, {"text": BTN_CR_OFF}], [{"text": BTN_CR_AUTO}],
                        [{"text": BTN_SRC}, {"text": BTN_BAN}], [{"text": BTN_HOURS}],
                        [{"text": BTN_REVIEW}]], "resize_keyboard": True, "is_persistent": True}


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
    if srcs:
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
        rows.append([{"text": ("🔊 باز کردن " if left > 0 else "🔇 بی‌صدا (۱ روز) ") + s, "callback_data": "mt:" + s},
                     {"text": "🗑 حذف", "callback_data": "dl:" + s}])
    lines.append("\nاضافه کردن: لینک یا آیدی کانال را بفرست (مثلاً /add name)")
    lines.append("بی‌صدا برای چند روز: /mute name 3")
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
    if len(cfg["sources"]) <= 1:
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
    cmd, _, arg = text.partition(" ")
    cmd, arg = cmd.split("@")[0].lower(), arg.strip()
    if text == BTN_SRC or cmd == "/sources":
        return sources_view(cfg, state)
    if text == BTN_HOURS or cmd == "/hours":
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


def tell(net, chat, text, markup=None):
    p = {"chat_id": chat, "text": text, "disable_web_page_preview": True}
    if markup:
        p["reply_markup"] = markup
    try:
        return net.api("sendMessage", p)
    except (ApiError, NetError) as e:
        log.warning("could not message the owner: %s", getattr(e, "desc", e))


def owner_of(cfg, state):
    return int(cfg.get("owner_id") or state.get("owner_id") or 0)


def status_text(cfg, state):
    on = not state.get("paused")
    lines = ["وضعیت ربات: " + ("🟢 روشن" if on else "🔴 خاموش")]
    nxt = state.get("next_run_ts", 0) - time.time()
    if on:
        lines.append("دور بعدی ارسال: " + ("به‌زودی" if nxt <= 0 else "حدود %d دقیقه دیگر" % (nxt // 60 + 1)))
    lines.append("پست‌های منتظر تصمیم شما: %d" % len(state.get("pending", {})))
    lines.append("تاییدشده و منتظر ارسال: %d" % len(state.get("approved", [])))
    lines.append("بررسی پست‌های مشکوک: " + ("روشن" if not state.get("review_off") else "خاموش"))
    mode = state.get("crisis_mode", "auto")
    lines.append("حالت بحران: " + {"on": "🚨 روشن (دستی)", "off": "🛑 خاموش (دستی)"}.get(
        mode, "🚨 فعال (خودکار)" if state.get("crisis_auto") else "🤖 خودکار (الان عادی)"))
    return "\n".join(lines)


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
    try:
        ups = net.api("getUpdates", {"offset": state.get("update_offset", 0), "timeout": int(wait),
                                     "allowed_updates": ["message", "callback_query"]})
    except (ApiError, NetError) as e:
        log.warning("cannot read bot messages: %s", getattr(e, "desc", e))
        return
    for u in ups or []:
        state["update_offset"] = u["update_id"] + 1
        try:
            handle_update(cfg, net, state, u)
        except Exception:
            log.exception("could not handle a bot message")
    if ups:
        save_state(state_path, state)


def handle_update(cfg, net, state, u):
    cb = u.get("callback_query")
    if cb:
        if cb["from"]["id"] != owner_of(cfg, state):
            return
        act, _, pid = (cb.get("data") or "").partition(":")
        if act in ("mt", "dl"):
            source_button(cfg, net, state, cb)
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
        state["owner_id"] = owner = uid          # the first person who presses Start is the owner
        log.info("owner registered")
    if uid != owner:
        return
    managed = manage_command(cfg, net, state, text)
    if managed:
        tell(net, owner, managed[0], managed[1] or MENU_KB)
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
    elif BTN_REVIEW in text or text.startswith("/review"):
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
        tell(net, owner, status_text(cfg, state), MENU_KB)


def heartbeat(cfg, net, state):
    """Once a day (after 07:30 Iran time) tell the owner the bot is alive."""
    owner = owner_of(cfg, state)
    if not owner:
        return
    now = time.time()
    lt = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60)
    day = "%04d-%02d-%02d" % (lt.tm_year, lt.tm_mon, lt.tm_mday)
    if (lt.tm_hour, lt.tm_min) < (7, 30) or state.get("hb_day") == day:
        return
    log_ = [t for t in state.get("posted_log", []) if now - t < 86400]
    txt = "🟢 ربات از سمت گیت‌هاب فعال است.\n"
    txt += "وضعیت: " + ("⏸ خاموش (با دکمه‌ی شما)" if state.get("paused") else "روشن") + "\n"
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
    tell(net, owner, "☝️ این پست مشکوک به تبلیغ بود (%s) از کانال %s.\nارسال شود؟" % (reason, src), {
        "inline_keyboard": [[{"text": "✅ ارسال", "callback_data": "ok:" + pid},
                             {"text": "❌ رد", "callback_data": "no:" + pid}]]})
    return True


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
        grp = "تکراری" if what == "dup" else next((g for p, g in SKIP_GROUPS if what.startswith(p)), "سایر")
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
    if not dry:
        process_updates(cfg, net, state, state_path)
        apply_overrides(cfg, state)                # sources / banned words changed from the bot
        heartbeat(cfg, net, state)
        daily_report(cfg, net, state, now)
        hours_update(cfg, net, state, now)
        state["posted_log"] = [t for t in state.get("posted_log", []) if now - t < 3 * 86400]
        if state.get("paused"):
            log.info("switched OFF from the bot - nothing is posted")
            return
    nxt = state.get("next_run_ts", 0)
    if not force and not dry and now < nxt:
        log.info("waiting - next posting round in about %d min", int((nxt - now) / 60) + 1)
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
            counts[key] = len(new)
        pages.append((name, key, label, st, new))
    crisis = False if dry else crisis_eval(cfg, net, state, now, counts)
    if crisis:
        log.info("CRISIS MODE is active: up to %d newest posts per source, short rounds, no photo label",
                 int(cfg["crisis_posts_per_channel"]))
    hour = time.gmtime(now + int(cfg["utc_offset_minutes"]) * 60).tm_hour
    n0, n1 = cfg["night_hours"]
    night = n0 <= hour < n1 and not crisis
    if night:
        log.info("night hours: at most %d post(s) per round", cfg["night_max_posts"])
    # --- 2. choose candidates ---
    cands = []
    reviewed = 0
    take = int(cfg["crisis_posts_per_channel"]) if crisis else 1
    for name, key, label, st, new in pages:
        if not new:
            log.info("[%s] nothing new", label)
            continue
        if not dry:
            st["last_id"] = new[-1]["id"]         # whatever happens, these are never reconsidered
        for p in new[-take:]:
            reason = skip_reason(cfg, p)
            if reason:
                log.info("[%s/%d] skipped: %s", label, p["id"], reason)
                if not dry:
                    stat_add(state, cfg, reason)
                    if (owner_of(cfg, state) and not state.get("review_off") and review_worthy(cfg, reason)
                            and reviewed < int(cfg["review_max_per_round"])):
                        txt = build_text(cfg, rules, p["text_html"])
                        if send_for_review(net, cfg, state, label, name, p, txt, reason):
                            reviewed += 1
                            time.sleep(2)
                continue
            cands.append((label, st, p))
    hist = state.setdefault("fp", [])
    hist[:] = [e for e in hist if now - e.get("t", 0) < 14 * 86400][-400:]
    if crisis:
        limit = int(cfg["crisis_max_posts"])
    else:
        limit = int(cfg["max_posts_per_run"]) or len(cands)
        if night:
            limit = min(limit, int(cfg["night_max_posts"])) if limit else int(cfg["night_max_posts"])
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
    for k in [k for k, v in state.get("pending", {}).items() if now - v.get("t", 0) > 86400]:
        state["pending"].pop(k)
    for label, st, p in cands:                    # candidates are already in random order
        tag = "%s/%d" % (label, p["id"])
        text = build_text(cfg, rules, p["text_html"])
        fp = text_fp(norm_for_dedupe(text, rules.own))
        fp["m"] = media_hashes(net, p["media"]) if p["media"] else []
        if find_dup(fp, hist + [c[3] for c in eligible]):
            log.info("[%s] skipped: duplicate of a post already sent/selected", tag)
            if not dry:
                stat_add(state, cfg, "dup")
            continue
        eligible.append((tag, p, text, fp, st))
    chosen = pick_and_order(eligible, limit)
    for item in eligible:
        if item not in chosen:
            log.info("[%s] not chosen this time", item[0])
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
        except Skip as e:
            log.warning("[%s] skipped: %s", tag, e)
        except NetError as e:
            log.warning("[%s] network problem: %s", tag, e)
        except ApiError as e:
            log.error("[%s] Telegram refused: %s", tag, e.desc)
        save_state(state_path, state)
        if i < len(chosen) - 1:
            time.sleep(random.uniform(float(lo), float(hi)))
    if not posted and not dry:
        state["next_run_ts"] = max(state.get("next_run_ts", 0), time.time() + 120)
        save_state(state_path, state)
    if posted and not dry:
        a, b = (cfg["crisis_interval_minutes"] if crisis
                else cfg["night_interval_minutes"] if night else cfg["interval_minutes"])
        state["next_run_ts"] = time.time() + random.uniform(float(a), float(b)) * 60
        save_state(state_path, state)
        log.info("round finished: %d posted, next round in %d-%d min or later", posted, a, b)


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
        first = False
        if args.serve:
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
                    if time.time() - t0 < 1:       # never spin faster than once a second
                        time.sleep(1)
                continue
            break
        if args.once or args.dry_run:
            break
        time.sleep(max(60, int(cfg["check_every_seconds"])))


if __name__ == "__main__":
    main()
