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
import hashlib
import html
import json
import logging
import os
import re
import sys
import time
import urllib.error
import urllib.request
import uuid
from html.parser import HTMLParser

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")
MAX_UPLOAD = 49 * 1024 * 1024  # Bot API upload limit is 50 MB

DEFAULTS = {
    "bot_token": "",
    "target_channel": "",
    "sources": [],
    "check_every_seconds": 300,
    "initial_posts": 0,            # how many old posts to publish on the very first run
    "delay_between_posts": 3,
    "replacements": [],            # [["old text", "new text"], ...]
    "keep_mentions": [],           # @usernames that must NOT be replaced
    "add_footer": True,            # add your @channel at the end if it is missing
    "strip_all_links": False,      # True = remove every link, keep only the text
    "link_previews": False,
    "skip_forwarded": False,
    "skip_replies": True,
    "skip_invite_links": True,     # posts that contain t.me/+xxx or joinchat links
    # any of these pieces of text anywhere in the post => treated as an ad
    "ad_keywords": [
        "#تبلیغ", "#تبلیغات", "تبلیغات", "رزرو تبلیغ", "سفارش تبلیغ", "جهت تبلیغ",
        "#ad", "#ads", "sponsored", "#sponsored", "advertisement",
        "شرط بندی", "شرط‌بندی", "شرطبندی", "شرط بند", "کازینو", "پوکر", "اسلات",
        "رولت", "بونوس", "بونس", "کد معرف", "ثبت نام و دریافت", "ثبت‌نام و دریافت",
        "betting", "casino", "poker", "1xbet", "bet365", "bonus", "jackpot", "slot",
    ],
    # whole words only (so "بت" matches the word "بت" but not "ثبت")
    "ad_words": ["بت", "بت‌ها", "bet", "bets"],
    # ads almost always carry a link to a site/app: skip every post that has a
    # link to anything other than Telegram (links to the domains below are allowed)
    "extra_ad_keywords": [],      # your own additional ad words (added to ad_keywords)
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
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip() or str(cfg["bot_token"]).strip()
    if not token or "PASTE" in token.upper():
        die("bot_token is empty in config.json - paste the token you got from @BotFather.")
    cfg["bot_token"] = token
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
                return data.get("result")
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
    r'|<video\b[^>]*?\bsrc="([^"]+)"', re.S)
UNSUPPORTED = ("message_media_not_supported", "tgme_widget_message_poll",
               "tgme_widget_message_voice", "tgme_widget_message_document_wrap",
               "tgme_widget_message_sticker", "tgme_widget_message_tgsticker",
               "tgme_widget_message_location", "tgme_widget_message_contact",
               "tgme_widget_message_roundvideo")
EMOJI_RE = re.compile(r'<i class="emoji"[^>]*>\s*<b>(.*?)</b>\s*</i>', re.S)
INVITE_RE = re.compile(r"(?:t|telegram)\.me/(?:\+|joinchat/)", re.I)


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
                media.append(("video", html.unescape(mm.group(2))))
        seen, uniq = set(), []
        for item in media:
            if item[1] not in seen:
                seen.add(item[1])
                uniq.append(item)
        posts.append({
            "id": int(m.group(1)),
            "text_html": tm.group(1) if tm else "",
            "media": uniq,
            "forwarded": "tgme_widget_message_forwarded_from" in chunk,
            "reply": "tgme_widget_message_reply" in chunk,
            "unsupported": any(u in chunk for u in UNSUPPORTED),
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
        s = TME_RE.sub(self.own, s)
        return MENTION_RE.sub(
            lambda m: m.group(0) if m.group(0).lower() in self.keep else self.own, s)

    def link(self, href, inner):
        if TME_HREF_RE.match(href):
            return self.own
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
    t = re.sub(r"[ \t]+\n", "\n", t)
    t = re.sub(r"\n{3,}", "\n\n", t).strip()
    own = re.escape(rules.own)
    t = re.sub(r"(%s)(?:[\s|\-–•·,،/]*%s)+" % (own, own), rules.own, t, flags=re.I)
    if cfg["add_footer"] and rules.own.lower() not in plain(t).lower():
        t = (t + "\n\n" + rules.own) if t else rules.own
    return t


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


def send_single(net, cfg, kind, url, caption):
    method = "sendPhoto" if kind == "photo" else "sendVideo"
    payload = {"chat_id": cfg["target_channel"], kind: url}
    if kind == "video":
        payload["supports_streaming"] = True
    if caption:
        payload["caption"] = caption
        payload["parse_mode"] = "HTML"
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
    for i in range(0, len(media), 10):
        chunk = media[i:i + 10]
        cap = caption if i == 0 else ""
        if len(chunk) == 1:
            send_single(net, cfg, chunk[0][0], chunk[0][1], cap)
            continue
        items = []
        for j, (kind, url) in enumerate(chunk):
            it = {"type": kind, "media": url}
            if kind == "video":
                it["supports_streaming"] = True
            if cap and j == 0:
                it["caption"] = cap
                it["parse_mode"] = "HTML"
            items.append(it)
        try:
            net.api("sendMediaGroup", {"chat_id": cfg["target_channel"], "media": items})
        except ApiError as e:
            log.info("album by link failed (%s) - sending items one by one", e.desc)
            for j, (kind, url) in enumerate(chunk):
                send_single(net, cfg, kind, url, cap if j == 0 else "")
        time.sleep(1)


def deliver(net, cfg, post, text):
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
        mem = net.api("getChatMember", {"chat_id": chat["id"], "user_id": me["id"]})
        if mem.get("status") == "creator" or (
                mem.get("status") == "administrator" and mem.get("can_post_messages", True)):
            print("OK: the bot is an admin of %s and can post" % shown)
        else:
            ok = False
            print("PROBLEM: the bot is not an admin with 'Post messages' permission in %s"
                  % shown)
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
        skipped = sum(1 for p in posts if skip_reason(cfg, p))
        print("OK: [%s] %d recent posts visible, %d of them would be skipped (ads/unsupported)"
              % (name, len(posts), skipped))
        if skipped == len(posts) and len(posts) > 3:
            print("   WARNING: everything is being skipped - run  python repost.py --dry-run  to see why")
    print("\n" + ("ALL GOOD - you can start run.bat" if ok else "Fix the problems above, then run check again"))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default=os.path.join(BASE_DIR, "config.json"))
    ap.add_argument("--state", default=os.path.join(BASE_DIR, "state.json"))
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--once", action="store_true")
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
    state = load_state(args.state)
    log.info("Started. %d source channel(s) -> %s", len(cfg["sources"]),
             "your channel" if IN_CLOUD else cfg["target_channel"])
    while True:
        try:
            run_cycle(cfg, net, rules, state, args.state, args.dry_run)
        except Exception:
            log.exception("cycle failed (will try again)")
        if args.once or args.dry_run:
            break
        time.sleep(max(60, int(cfg["check_every_seconds"])))


if __name__ == "__main__":
    main()
