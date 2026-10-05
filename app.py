# ============================================================
#  WhatsApp Group Link Hunter — v2 (container-hardened)
#  Fixes: Streamlit-Cloud-safe Chromium + crash recovery,
#  domain-keyed politeness, retries, thread-safe sessions,
#  subdomain focus, low-value page filtering.
# ============================================================

import csv, io, re, sys, time, heapq, threading, subprocess, itertools
from collections import deque, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from urllib.parse import urljoin, urldefrag, urlparse, urlunparse
import urllib.robotparser as robotparser

import requests
import urllib3
from bs4 import BeautifulSoup
import streamlit as st
import pandas as pd

try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_OK = True
except ImportError:
    PLAYWRIGHT_OK = False

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# ------------------------------------------------------------------
# Constants
# ------------------------------------------------------------------
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

CODE = r"[A-Za-z0-9_\-]{18,32}"
_SL = r"(?:\\/|/)"   # matches "/" AND JSON-escaped "\/"

WA_PATTERNS = [
    re.compile(rf"https?:{_SL}{_SL}chat\.whatsapp\.com{_SL}(?:invite{_SL})?(?P<code>{CODE})", re.I),
    re.compile(rf"whatsapp:{_SL}{_SL}chat\?code=(?P<code>{CODE})", re.I),
    re.compile(rf"(?<![\w./@-])chat\.whatsapp\.com{_SL}(?:invite{_SL})?(?P<code>{CODE})", re.I),
]

SKIP_EXT = (".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".bmp", ".ico",
            ".css", ".js", ".json", ".xml", ".zip", ".rar", ".7z", ".gz", ".tar",
            ".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
            ".mp3", ".mp4", ".avi", ".mov", ".woff", ".woff2", ".ttf", ".eot", ".otf")

BAD_HOST_WORDS = ("whatsapp.com", "wa.me", "facebook.com", "instagram.com", "twitter.com",
                  "x.com", "youtube.com", "google.com", "goo.gl", "bit.ly", "t.me",
                  "telegram.me", "pinterest.com", "linkedin.com", "amazon.com",
                  "microsoft.com", "apple.com", "tiktok.com", "reddit.com", "medium.com")

BAD_PATH_RE = re.compile(
    r"(wp-login|wp-admin|/login|/logout|/register|/signup|/admin|/cart|/checkout"
    r"|/feed|/embed|replytocom|\?share=|/print)", re.I)

MULTI_TENANT = ("blogspot.", "wordpress.com", "github.io", "weebly.com", "wixsite.com",
                "glitch.me", "vercel.app", "netlify.app", "pages.dev", "webnode",
                "business.site", "godaddysites")

ENGINE_LABEL = {"static": "📄 HTML", "browser": "🖥️ Browser",
                "js/xhr": "⚙️ JS / API", "click": "🖱️ Button"}
STATUS_LABEL = {"active": "✅ Active", "invalid": "❌ Invalid", "revoked": "🚫 Revoked",
                "expired": "⌛ Expired", "unknown": "❔ Unknown", "": "—"}

# --- NEW in v2: container-safe Chromium & lighter pages -----------------
LAUNCH_ARGS = [
    "--no-sandbox",
    "--disable-setuid-sandbox",
    "--disable-dev-shm-usage",   # <- critical fix for Streamlit Cloud (tiny /dev/shm)
    "--disable-gpu",
    "--disable-extensions",
    "--disable-background-networking",
    "--disable-default-apps",
    "--disable-sync",
    "--disable-translate",
    "--mute-audio",
    "--no-first-run",
    "--window-size=1366,900",
]
# Block heavy junk inside the browser (CSS is KEPT so visibility checks stay correct)
ASSET_URL = re.compile(
    r"\.(png|jpe?g|gif|webp|svg|ico|bmp|avif|mp4|webm|mp3|ogg|wav|woff2?|ttf|eot|otf)(\?|#|$)", re.I)
AD_HOSTS = re.compile(
    r"(google-analytics|googletagmanager|doubleclick|adservice|adsystem|adsys"
    r"|criteo|taboola|outbrain|hotjar|mixpanel|segment\.io|clarity\.ms"
    r"|scorecardresearch|quantserve|amazon-adsystem|facebook\.net|connect\.facebook)", re.I)
# Pages that rarely contain invite links: don't waste browser renders on them
LOW_VALUE = re.compile(
    r"(crear|create|login|log-in|signin|sign-in|register|signup|sign-up|contact"
    r"|about|privacy|terms|dmca|disclaimer|policy|advert)", re.I)

# ------------------------------------------------------------------
# Helpers
# ------------------------------------------------------------------
def site_key(host: str) -> str:
    h = (host or "").split(":")[0].lower()
    if any(m in h for m in MULTI_TENANT):
        return h
    parts = h.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else h

def short(url: str, n: int = 48) -> str:
    try:
        p = urlparse(url)
        s = f"{p.netloc}{p.path}"
        return s if len(s) <= n else s[: n - 1] + "…"
    except Exception:
        return str(url)[:n]

def normalize(url, base=None):
    if not url:
        return None
    url = url.strip()
    if url.startswith(("javascript:", "mailto:", "tel:", "data:", "#")):
        return None
    if base:
        url = urljoin(base, url)
    url, _ = urldefrag(url)
    p = urlparse(url)
    if p.scheme not in ("http", "https") or not p.netloc:
        return None
    path = p.path or "/"
    if path != "/" and path.endswith("/"):
        path = path.rstrip("/")
    out = urlunparse((p.scheme, p.netloc.lower(), path, "", p.query, ""))
    return out if len(out) <= 500 else None

def parse_seeds(raw):
    seeds = []
    for line in (raw or "").splitlines():
        line = line.strip()
        if not line:
            continue
        if not line.startswith(("http://", "https://")):
            line = "https://" + line
        u = normalize(line)
        if u:
            seeds.append(u)
    return seeds

def make_soup(html):
    try:
        return BeautifulSoup(html, "lxml")
    except Exception:
        return BeautifulSoup(html, "html.parser")

def looks_js_heavy(html):
    if not html:
        return False
    low = html.lower()
    markers = ('id="root"', "id='root'", 'id="app"', "id='app"', 'id="__next"',
               "__next_data__", "window.__nuxt__", "data-reactroot", "ng-app",
               "data-sveltekit", 'id="q-app"')
    if any(m in low for m in markers):
        return True
    # v2: a page with a form + few links is a form page, not a JS app
    if low.count("<a ") <= 3 and len(low) > 600 and "<form" not in low:
        return True
    if len(low) < 3500 and low.count("<script") >= 2:
        return True
    return False

def extract_invites(text, source, engine, state):
    if not text:
        return 0
    new, seen_here = 0, set()
    for pat in WA_PATTERNS:
        for m in pat.finditer(text):
            code = m.group("code")
            if code in seen_here:
                continue
            seen_here.add(code)
            if state.add_hit(code, source, engine) == "new":
                new += 1
    return new

def extract_links(html, base_url):
    out = set()
    if not html:
        return out
    soup = make_soup(html)
    for a in soup.find_all(["a", "area"], href=True):
        u = normalize(a["href"], base_url)
        if u:
            out.add(u)
    for l in soup.find_all("link", attrs={"rel": True}):
        rel = l["rel"] if isinstance(l["rel"], list) else [l["rel"]]
        if "next" in rel:
            u = normalize(l.get("href", ""), base_url)
            if u:
                out.add(u)
    return out

# ------------------------------------------------------------------
# Shared state
# ------------------------------------------------------------------
@dataclass
class Hit:
    code: str
    source: str
    engine: str
    found_at: str
    url: str = ""
    def __post_init__(self):
        if not self.url:
            self.url = f"https://chat.whatsapp.com/{self.code}"

class CrawlState:
    def __init__(self):
        self.lock = threading.RLock()
        self.stop = threading.Event()
        self.hits: dict[str, Hit] = {}
        self.order: list[str] = []
        self.duplicates = 0
        self.pages_done = 0
        self.errors = 0
        self.log: deque = deque(maxlen=300)
        self.phase = "idle"
        self.last_summary = ""

    def begin_run(self):
        self.stop.clear()
        with self.lock:
            self.duplicates = self.pages_done = self.errors = 0
            self.log.clear()
            self.phase = "crawling"
            self.last_summary = ""

    def add_log(self, msg):
        with self.lock:
            self.log.append(f"{datetime.now().strftime('%H:%M:%S')}  {msg}")

    def add_hit(self, code, source, engine):
        with self.lock:
            if code in self.hits:
                self.duplicates += 1
                return "dup"
            self.hits[code] = Hit(code, source, engine,
                                  datetime.now().strftime("%H:%M:%S"))
            self.order.append(code)
            return "new"

    def update_status(self, code, status):
        with self.lock:
            if code in self.hits:
                self.hits[code].status = status

    def rows(self):
        with self.lock:
            return [(c, self.hits[c]) for c in reversed(self.order)]

    def log_tail(self, n=12):
        with self.lock:
            return list(self.log)[-n:]

# ------------------------------------------------------------------
# Politeness — v2: keyed by MAIN DOMAIN, with adaptive penalty
# ------------------------------------------------------------------
class Politeness:
    def __init__(self, delay):
        self.delay = max(0.0, float(delay))
        self.ts: dict[str, float] = {}
        self.extra: dict[str, float] = defaultdict(float)
        self.locks = defaultdict(threading.Lock)

    def wait(self, key: str):
        """key = site_key (main domain), so fr./hn./il./www. share one queue."""
        with self.locks[key]:
            now = time.time()
            wait_for = self.ts.get(key, 0.0) + self.delay + self.extra.get(key, 0.0) - now
            if wait_for > 0:
                time.sleep(wait_for)
            self.ts[key] = time.time()

    def penalize(self, key: str, secs=2.0):
        self.extra[key] = min(self.extra.get(key, 0.0) + secs, 12.0)

    def forgive(self, key: str):
        self.extra[key] = 0.0

class RobotCache:
    def __init__(self, respect=True):
        self.respect = respect
        self.cache: dict = {}
        self.lock = threading.Lock()

    def allowed(self, url):
        if not self.respect:
            return True
        p = urlparse(url)
        key = f"{p.scheme}://{p.netloc.lower()}"
        with self.lock:
            if key not in self.cache:
                rp = robotparser.RobotFileParser()
                rp.set_url(key + "/robots.txt")
                try:
                    rp.read()
                    self.cache[key] = rp
                except Exception:
                    self.cache[key] = None
            rp = self.cache[key]
        if rp is None:
            return True
        try:
            return rp.can_fetch("*", url)
        except Exception:
            return True

# ------------------------------------------------------------------
# Browser engine — v2: container-safe, crash-detecting, lightweight
# ------------------------------------------------------------------
CONSENT_SELECTORS = [
    "#onetrust-accept-btn-handler", ".fc-cta-consent", ".fc-primary-button",
    "#didomi-notice-agree-button", "#cookiescript_accept", "#cookie_action_close_header",
    ".js-cookie-consent-agree",
    "button:has-text('accept all')", "button:has-text('accept')", "a:has-text('accept')",
    "button:has-text('agree')", "button:has-text('allow')", "button:has-text('got it')",
    "button:has-text('i understand')", "button:text-is('OK')", "button:text-is('Ok')",
]

CLICK_RE = re.compile(
    r"\b(join|reveal|show|view|open|see|load\s*more|more|next|older|group|link|copy|part\s*\d+)\b", re.I)
AVOID_RE = re.compile(
    r"(share|tweet|facebook|twitter|instagram|telegram|login|sign|register|subscribe"
    r"|comment|policy|privacy|cookie|advert|app store|play store|close|cancel|search|menu)", re.I)

class BrowserSession:
    WA_ROUTE = re.compile(r"^https?://chat\.whatsapp\.com/.*", re.I)

    def __init__(self, state, allowed_keys, click_buttons=True, scroll=True, dismiss_consent=True):
        self.state = state
        self.allowed_keys = allowed_keys
        self.click_buttons = click_buttons
        self.scroll = scroll
        self.dismiss_consent = dismiss_consent
        self.xhr_bodies: list[str] = []
        self.click_urls: list[str] = []
        self.dead = False          # v2: session knows when Chromium has died

        self._pw = sync_playwright().start()
        self._browser = self._pw.chromium.launch(headless=True, args=LAUNCH_ARGS)
        ctx = self._browser.new_context(
            user_agent=UA, viewport={"width": 1366, "height": 900}, locale="en-US")
        ctx.set_default_timeout(12000)
        ctx.add_init_script("Object.defineProperty(navigator,'webdriver',{get:()=>undefined})")

        def _block(route):
            try:
                route.abort()
            except Exception:
                pass

        def _catch_wa(route):
            try:
                self.click_urls.append(route.request.url)
            finally:
                try:
                    route.abort()
                except Exception:
                    pass

        # v2: block images/media/fonts + analytics → far less RAM & bandwidth
        ctx.route(ASSET_URL, _block)
        ctx.route(AD_HOSTS, _block)
        ctx.route(self.WA_ROUTE, _catch_wa)   # registered last → checked first

        def _on_response(resp):
            try:
                if resp.request.resource_type in ("xhr", "fetch", "document"):
                    ct = (resp.headers or {}).get("content-type", "")
                    if any(k in ct for k in ("json", "text", "javascript", "html")):
                        body = resp.text()
                        if body and 0 < len(body) < 400_000 and len(self.xhr_bodies) < 200:
                            self.xhr_bodies.append(body)
            except Exception:
                pass
        ctx.on("response", _on_response)

        def _on_page(pg):
            try:
                if pg.url and pg.url != "about:blank":
                    self.click_urls.append(pg.url)
                pg.close()
            except Exception:
                pass
        ctx.on("page", _on_page)

        self.ctx = ctx
        self.page = ctx.new_page()

        # v2: fail fast — if this container can't render at all, say so NOW
        try:
            self.page.goto("data:text/html,<title>ok</title>", timeout=10000)
        except Exception as e:
            self.dead = True
            self.close()
            raise RuntimeError(f"Chromium starts but crashes on first render "
                               f"({type(e).__name__})")

    def render(self, url):
        if self.dead:
            return "", "session-dead"
        self.xhr_bodies, self.click_urls = [], []
        page = self.page
        try:
            page.goto(url, wait_until="domcontentloaded", timeout=30000)
        except Exception as e:
            if "TargetClosed" in type(e).__name__ or "BrowserClosed" in type(e).__name__:
                self.dead = True          # Chromium died → recycle me
            return "", type(e).__name__
        try:
            page.wait_for_load_state("networkidle", timeout=5000)
        except Exception:
            pass
        if self.dismiss_consent:
            self._dismiss_consent(page)
        if self.scroll:
            self._scroll(page)
        if self.click_buttons:
            self._smart_clicks(page)
        try:
            page.wait_for_timeout(600)
            return page.content(), None
        except Exception as e:
            if "TargetClosed" in type(e).__name__:
                self.dead = True
            return "", type(e).__name__

    def _dismiss_consent(self, page):
        for sel in CONSENT_SELECTORS:
            try:
                loc = page.locator(sel).first
                if loc.count() and loc.is_visible():
                    loc.click(timeout=1200, no_wait_after=True)
                    page.wait_for_timeout(350)
                    return True
            except Exception:
                continue
        return False

    def _scroll(self, page, rounds=4):
        try:
            for _ in range(rounds):
                page.evaluate("window.scrollBy(0, document.body.scrollHeight*0.4)")
                page.wait_for_timeout(400)
            page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            page.wait_for_timeout(400)
        except Exception:
            pass

    def _smart_clicks(self, page, max_clicks=8):
        clicked = 0
        try:
            for _round in range(2):
                locs = page.locator(
                    "button, [role='button'], a[href='#'], a[onclick], .btn, "
                    "[class*='button'], [class*='Button'], [class*='btn'], [class*='Btn']")
                count = min(locs.count(), 80)
                for i in range(count):
                    if clicked >= max_clicks or self.state.stop.is_set():
                        return clicked
                    el = locs.nth(i)
                    try:
                        if not el.is_visible():
                            continue
                        txt = (el.inner_text(timeout=800)
                               or el.get_attribute("aria-label") or "").strip().replace("\n", " ")
                    except Exception:
                        continue
                    if not txt or len(txt) > 60:
                        continue
                    if AVOID_RE.search(txt) or not CLICK_RE.search(txt):
                        continue
                    before = page.url
                    try:
                        el.scroll_into_view_if_needed(timeout=1500)
                        el.click(timeout=2000, no_wait_after=True)
                        clicked += 1
                        page.wait_for_timeout(700)
                    except Exception:
                        continue
                    now = page.url
                    if now != before:
                        host = urlparse(now).netloc.lower()
                        if site_key(host) not in self.allowed_keys and "whatsapp.com" not in host:
                            try:
                                page.go_back(timeout=8000)
                            except Exception:
                                try:
                                    page.goto(before, timeout=20000)
                                except Exception:
                                    pass
                    if self.dismiss_consent:
                        self._dismiss_consent(page)
        except Exception:
            pass
        return clicked

    def close(self):
        for closer in (lambda: self.ctx.close(),
                       lambda: self._browser.close(),
                       lambda: self._pw.stop()):
            try:
                closer()
            except Exception:
                pass

# ------------------------------------------------------------------
# Crawler
# ------------------------------------------------------------------
@dataclass
class CrawlConfig:
    seeds: list[str]
    max_pages: int = 80
    max_depth: int = 2
    workers: int = 4
    delay: float = 0.8
    mode: str = "smart"
    follow_external: bool = False
    respect_robots: bool = True
    click_buttons: bool = True
    scroll: bool = True
    dismiss_consent: bool = True
    verify: bool = False
    same_host_only: bool = True     # v2: skip clone subdomains (fr./hn./il.…)
    keywords: list[str] = field(default_factory=list)

class Crawler:
    def __init__(self, cfg, state):
        self.cfg, self.state = cfg, state
        self.browser = None
        self.browser_failed = False
        self.render_crashes = 0
        self.robots_skipped = 0
        self.host_fails = defaultdict(int)   # v2: consecutive failures per HOST
        self.dead_hosts = set()              # v2: blacklisted hosts
        self._tl = threading.local()         # v2: thread-local HTTP sessions

    def run(self):
        try:
            self._run()
        except Exception as e:
            self.state.add_log(f"💥 Crawler error: {e!r}")
        finally:
            self._shutdown()
            self.state.phase = "done"

    # ---------- internals ----------
    def _sess(self):
        """v2: one requests.Session PER THREAD (Session is not thread-safe)."""
        s = getattr(self._tl, "s", None)
        if s is None:
            s = requests.Session()
            s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9",
                              "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"})
            s.verify = False
            self._tl.s = s
        return s

    def _run(self):
        cfg, st8 = self.cfg, self.state
        st8.add_log(f"🚀 {cfg.mode.upper()} mode • {len(cfg.seeds)} seed(s) • "
                    f"max {cfg.max_pages} pages • depth {cfg.max_depth} • "
                    f"{cfg.workers} workers • {cfg.delay}s/domain delay")
        if cfg.mode == "deep" and cfg.max_pages > 60:
            st8.add_log("🐢 Deep mode renders every page in a real browser (~5–10 s/page).")
        if not PLAYWRIGHT_OK and cfg.mode != "fast":
            st8.add_log("ℹ️ Playwright missing — browser features off. "
                        "Run: pip install playwright && playwright install chromium")

        self.polite = Politeness(cfg.delay)
        self.robots = RobotCache(cfg.respect_robots)
        self.seen, self.visited, self.frontier = set(), set(), []
        self._ctr = itertools.count()
        self.allowed_keys = {site_key(urlparse(s).netloc) for s in cfg.seeds}
        self.seed_hosts = set()              # v2: exact hosts we're allowed on
        for s in cfg.seeds:
            h = urlparse(s).netloc.lower()
            self.seed_hosts.update({h, h[4:] if h.startswith("www.") else "www." + h})
        self.executor = ThreadPoolExecutor(max_workers=cfg.workers, thread_name_prefix="fetch")

        for s in cfg.seeds:
            if not st8.stop.is_set():
                self._seed_sitemap(s)
        for s in cfg.seeds:
            self._push(s, 0)

        while self.frontier and st8.pages_done < cfg.max_pages and not st8.stop.is_set():
            batch = self._pop_batch()
            if not batch:
                continue
            for u, _ in batch:
                self.visited.add(u)
            st8.add_log(f"📄 Fetching {len(batch)} page(s): "
                        + ", ".join(short(u) for u, _ in batch[:3])
                        + ("…" if len(batch) > 3 else ""))
            futures = {self.executor.submit(self._fetch_static, u): (u, d) for u, d in batch}
            for fut in as_completed(futures):
                u, d = futures[fut]
                try:
                    html, final_url, err = fut.result()
                except Exception as e:
                    html, final_url, err = None, u, repr(e)[:100]
                if err == "stopped":
                    continue
                if html is None and err is None:
                    continue
                if err:
                    with st8.lock:
                        st8.errors += 1
                    st8.add_log(f"⚠️ {short(u)} → {err}")
                    continue
                with st8.lock:
                    st8.pages_done += 1
                new = self._process(html, final_url, d, "static")
                if new:
                    st8.add_log(f"🎯 {new} new link(s) on {short(final_url)}")
                if cfg.mode in ("smart", "deep") and not st8.stop.is_set():
                    # v2: never burn browser time on create/login/privacy pages
                    trigger = cfg.mode == "deep" or (
                        new == 0 and looks_js_heavy(html) and not LOW_VALUE.search(u))
                    if trigger:
                        self._browser_task(u, d)

        if st8.stop.is_set():
            st8.add_log("🛑 Stopped by user.")
        summary = (f"🏁 Done — {len(st8.hits)} unique link(s) • {st8.duplicates} duplicates "
                   f"skipped • {st8.pages_done} pages • {st8.errors} errors"
                   + (f" • {self.robots_skipped} blocked by robots.txt" if self.robots_skipped else ""))
        st8.add_log(summary)
        st8.last_summary = summary

        if cfg.verify and st8.hits and not st8.stop.is_set():
            st8.phase = "verifying links"
            verify_hits(st8)
            st8.add_log("✅ Verification finished.")

    def _pop_batch(self):
        cfg, st8 = self.cfg, self.state
        batch = []
        while (self.frontier and len(batch) < cfg.workers
               and st8.pages_done + len(batch) < cfg.max_pages):
            _, _, depth, url = heapq.heappop(self.frontier)
            if url in self.visited:
                continue
            if urlparse(url).netloc.lower() in self.dead_hosts:
                continue
            try:
                ok = self.robots.allowed(url)
            except Exception:
                ok = True
            if not ok:
                self.robots_skipped += 1
                continue
            batch.append((url, depth))
        return batch

    def _fetch_static(self, url):
        """v2: retries with backoff, domain-keyed politeness, host blacklisting."""
        host = urlparse(url).netloc.lower()
        key = site_key(host)
        if host in self.dead_hosts:
            return None, url, None
        last_err = None
        for attempt in range(3):
            if self.state.stop.is_set():
                return None, url, "stopped"
            self.polite.wait(key)                    # one queue per MAIN domain
            try:
                r = self._sess().get(url, timeout=20, allow_redirects=True)
                self.polite.forgive(key)
                self.host_fails[host] = 0
                if r.status_code in (403, 429):
                    self.polite.penalize(key, 3.0)   # site is annoyed → slow down
                    return None, url, f"HTTP {r.status_code} (rate-limited — backing off)"
                if r.status_code >= 400:
                    return None, url, f"HTTP {r.status_code}"
                ctype = (r.headers.get("content-type") or "").lower()
                if ctype and not any(x in ctype for x in ("html", "xml", "text", "json", "javascript")):
                    return None, url, "non-HTML"
                text = r.text
                if "<" not in text[:2000]:
                    return None, url, "not markup"
                return text, r.url, None
            except requests.exceptions.RequestException as e:
                last_err = type(e).__name__
                self.polite.penalize(key, 2.0)       # transient error → bigger gap
                if attempt < 2:
                    time.sleep(1.5 * (attempt + 1))  # backoff before retry
        self.host_fails[host] += 1
        if self.host_fails[host] >= 3 and host not in self.dead_hosts:
            self.dead_hosts.add(host)
            self.state.add_log(f"🚫 Skipping rest of {host} — repeated connection failures")
        return None, url, f"{last_err} (after 3 tries)"

    def _process(self, html, source_url, depth, engine):
        new = extract_invites(html or "", source_url, engine, self.state)
        if depth < self.cfg.max_depth:
            for link in extract_links(html or "", source_url):
                self._push(link, depth + 1)
        return new

    def _browser_task(self, url, depth):
        """v2: recycles the browser session when Chromium dies; gives up after 3 crashes."""
        st8 = self.state
        html, err = "", None
        for _attempt in range(2):
            b = self._ensure_browser()
            if b is None:
                return
            if b.dead:
                self._kill_browser()
                continue
            self.polite.wait(site_key(urlparse(url).netloc))
            st8.add_log(f"🖥️ Browser rendering {short(url)}")
            html, err = b.render(url)
            if err and b.dead:                       # Chromium crashed mid-render
                self.render_crashes += 1
                self._kill_browser()
                if self.render_crashes >= 3:
                    self.browser_failed = True
                    st8.add_log("❌ Browser keeps crashing on this host — switching to "
                                "HTTP-only mode for the rest of this run.")
                    return
                st8.add_log(f"⚠️ Browser crashed on {short(url)} — restarting session "
                            f"({self.render_crashes}/3)")
                continue
            break
        if err:
            with st8.lock:
                st8.errors += 1
            st8.add_log(f"⚠️ browser {short(url)} → {err}")
        b = self.browser
        if b is not None and not b.dead:
            for text, engine in (("\n".join(b.click_urls), "click"),
                                 ("\n".join(b.xhr_bodies), "js/xhr")):
                if text:
                    n = extract_invites(text, url, engine, st8)
                    if n:
                        st8.add_log(f"🖱️ {n} link(s) revealed via {ENGINE_LABEL[engine]} on {short(url)}")
        new = extract_invites(html or "", url, "browser", st8)
        if new:
            st8.add_log(f"🎯 {new} new link(s) after rendering {short(url)}")
        if depth < self.cfg.max_depth:
            for link in extract_links(html or "", url):
                self._push(link, depth + 1)

    def _kill_browser(self):
        if self.browser is not None:
            try:
                self.browser.close()
            except Exception:
                pass
            self.browser = None

    def _ensure_browser(self):
        if self.browser is not None and not self.browser.dead:
            return self.browser
        if self.browser is not None:
            self._kill_browser()
        if self.browser_failed or not PLAYWRIGHT_OK:
            return None
        try:
            self.browser = BrowserSession(self.state, self.allowed_keys,
                                          self.cfg.click_buttons, self.cfg.scroll,
                                          self.cfg.dismiss_consent)
            self.state.add_log("🧭 Headless Chromium ready")
            return self.browser
        except RuntimeError as e:
            # launched but can't render → container too constrained
            self.browser_failed = True
            self.state.add_log(f"❌ {e} — this host can't run the browser engine "
                               "(common on free containers). Continuing HTTP-only.")
            return None
        except Exception as e:
            if "Executable doesn't exist" not in str(e):
                self.browser_failed = True
                self.state.add_log(f"❌ Chromium failed to start ({str(e)[:90]}) — "
                                   "continuing HTTP-only. On Streamlit Cloud, check that "
                                   "packages.txt is deployed.")
                return None
            self.state.add_log("⏳ Chromium binary missing — downloading (one time)…")
            try:
                subprocess.run([sys.executable, "-m", "playwright", "install", "chromium"],
                               check=True, timeout=900, capture_output=True)
                self.browser = BrowserSession(self.state, self.allowed_keys,
                                              self.cfg.click_buttons, self.cfg.scroll,
                                              self.cfg.dismiss_consent)
                self.state.add_log("✅ Chromium installed and ready")
                return self.browser
            except Exception as e2:
                self.browser_failed = True
                self.state.add_log(f"❌ Browser unavailable ({str(e2)[:80]}) — continuing HTTP-only")
                return None

    def _score(self, url):
        u = url.lower()
        s = sum(u.count(k) for k in self.cfg.keywords)
        if LOW_VALUE.search(u):
            s -= 2
        return s

    def _host_ok(self, host):
        if any(b in host for b in BAD_HOST_WORDS):
            return False
        if self.cfg.same_host_only:            # v2: ignore clone subdomains
            return host in self.seed_hosts
        if site_key(host) in self.allowed_keys:
            return True
        return self.cfg.follow_external

    def _push(self, url, depth):
        if depth > self.cfg.max_depth or url in self.seen or url in self.visited:
            return
        if len(self.frontier) >= 9000:
            return
        p = urlparse(url)
        host = p.netloc.lower()
        if host in self.dead_hosts:
            return
        if not self._host_ok(host):
            return
        if p.path.lower().endswith(SKIP_EXT) or BAD_PATH_RE.search(p.path):
            return
        self.seen.add(url)
        heapq.heappush(self.frontier, (-self._score(url), next(self._ctr), depth, url))

    def _seed_sitemap(self, seed_url):
        st8, p = self.state, urlparse(seed_url)
        base = f"{p.scheme}://{p.netloc}"
        key = site_key(p.netloc)
        sm_urls = [base + "/sitemap.xml", base + "/sitemap_index.xml",
                   base + "/sitemap-index.xml"]
        try:
            self.polite.wait(key)
            r = self._sess().get(base + "/robots.txt", timeout=8)
            if r.status_code == 200:
                sm_urls += [l.split(":", 1)[1].strip()
                            for l in r.text.splitlines() if l.lower().startswith("sitemap:")]
        except Exception:
            pass
        locs, seen_sm = [], set()
        for sm in sm_urls:
            if sm in seen_sm:
                continue
            seen_sm.add(sm)
            try:
                self.polite.wait(site_key(urlparse(sm).netloc))
                r = self._sess().get(sm, timeout=12)
                if r.status_code != 200:
                    continue
                found = re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", r.text, re.I)
                if "<sitemapindex" in r.text.lower():
                    for child in found[:5]:
                        if child in seen_sm:
                            continue
                        seen_sm.add(child)
                        try:
                            self.polite.wait(site_key(urlparse(child).netloc))
                            r2 = self._sess().get(child, timeout=12)
                            if r2.status_code == 200:
                                locs += re.findall(r"<loc>\s*([^<\s]+)\s*</loc>", r2.text, re.I)
                        except Exception:
                            pass
                else:
                    locs += found
            except Exception:
                continue
        urls = [u for u in (normalize(x) for x in locs) if u]
        if not urls:
            return
        urls.sort(key=lambda u: -self._score(u))
        take = urls[: min(len(urls), max(60, self.cfg.max_pages * 2))]
        for u in take:
            self._push(u, 0)
        st8.add_log(f"🗺️ Sitemap: queued {len(take)} pages from {p.netloc}")

    def _shutdown(self):
        self._kill_browser()
        ex = getattr(self, "executor", None)
        if ex:
            try:
                ex.shutdown(wait=False)
            except Exception:
                pass

# ------------------------------------------------------------------
# Optional verification
# ------------------------------------------------------------------
def verify_hits(state, workers=3):
    codes = list(state.hits.keys())
    polite = Politeness(0.4)

    def check(code):
        polite.wait("chat.whatsapp.com")
        try:
            s = requests.Session()
            s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
            r = s.get(f"https://chat.whatsapp.com/{code}", timeout=15)
            low = r.text.lower()
            if r.status_code in (404, 410):
                return "invalid"
            if "invite link is invalid" in low:
                return "invalid"
            if "revoked" in low:
                return "revoked"
            if "expired" in low:
                return "expired"
            if any(k in low for k in ("join group", "join community", "join chat")):
                return "active"
            return "unknown"
        except Exception:
            return "unknown"

    done = 0
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for code, res in zip(codes, ex.map(check, codes)):
            state.update_status(code, res)
            done += 1
            if done % 10 == 0:
                state.add_log(f"🔍 Verified {done}/{len(codes)}")

# ------------------------------------------------------------------
# Streamlit UI
# ------------------------------------------------------------------
if hasattr(st, "fragment"):
    _fragment = st.fragment
else:
    def _fragment(run_every=None, **_):
        def deco(fn):
            return fn
        return deco

st.set_page_config(page_title="WhatsApp Group Hunter", page_icon="🔎", layout="wide")

st.markdown("""
<style>
  .block-container{padding-top:1.1rem; max-width:1250px;}
  [data-testid="stMetric"]{
      background:#0d1626; border:1px solid #22304a; border-radius:14px;
      padding:14px 16px;}
  [data-testid="stMetricLabel"] p{color:#9fb3d1 !important; font-size:.82rem;}
  [data-testid="stMetricValue"]{color:#25D366; font-weight:800;}
  section[data-testid="stSidebar"]{background:#0b1220;}
</style>""", unsafe_allow_html=True)

MODES = {
    "⚡ Fast — HTTP only (quickest)": "fast",
    "🧠 Smart — auto hybrid (recommended)": "smart",
    "🐢 Deep — full browser on every page": "deep",
}

@_fragment(run_every=1.0)
def live_view():
    s = st.session_state.crawl_state
    t = st.session_state.get("crawl_thread")
    alive = bool(t and t.is_alive())

    c = st.columns(4)
    c[0].metric("🌐 Pages crawled", s.pages_done)
    c[1].metric("🔗 Unique links", len(s.hits))
    c[2].metric("♻️ Duplicates skipped", s.duplicates)
    c[3].metric("⚠️ Errors", s.errors)
    st.progress(min(s.pages_done / max(1, st.session_state.get("cfg_max_pages", 80)), 1.0))

    with st.container(border=True):
        st.caption("📡 Live activity")
        st.code("\n".join(s.log_tail(12)) or "…", language=None)

    b1, b2, _ = st.columns([1.3, 1.3, 2.4])
    if b1.button("⏹️ Stop", type="primary", use_container_width=True, disabled=not alive):
        s.stop.set()
        st.toast("Stopping after current page…")
    b2.button("🔄 Refresh now", use_container_width=True)

    if alive:
        st.info(f"🟢 {s.phase} — auto-refreshing every second…")
    else:
        st.success("🏁 Finished.")
        st.rerun()

def show_results(state):
    if not state.hits:
        st.info("👋 Paste one or more seed URLs in the sidebar and press **Start crawl**.\n\n"
                "The hunter will dig through the site — listing pages, sitemaps, pagination, "
                "JS-rendered content, API responses and button-revealed links — and collect "
                "every `chat.whatsapp.com` invite link it can reach.")
        with st.expander("ℹ️ How the three modes differ"):
            st.markdown(
                "- **⚡ Fast** — plain HTTP requests + regex over raw source. Catches links in HTML, "
                "`data-*` attributes, `onclick` handlers and embedded JSON. Best for Blogger/classic PHP sites.\n"
                "- **🧠 Smart** — Fast first; if a page looks JS-rendered it re-renders in headless Chromium, "
                "auto-scrolls, dismisses cookie banners, clicks join/reveal/load-more buttons and sniffs "
                "XHR/JSON responses. If Chromium can't run on the host, it falls back to HTTP-only automatically.\n"
                "- **🐢 Deep** — browser on *every* page. Slowest, most thorough.")
        return

    st.subheader(f"🔗 {len(state.hits)} unique invite links")
    if state.last_summary:
        st.caption(state.last_summary + "  •  results persist for this session — duplicates are "
                   "auto-skipped on every future run. Export before closing the tab.")

    f1, f2 = st.columns([3, 2])
    q = f1.text_input("🔍 Filter by code or source page", key="q").lower()
    hide_dead = f2.checkbox("Hide dead links", value=False, key="hide_dead")

    data = []
    for code, h in state.rows():
        if q and q not in f"{code} {h.source}".lower():
            continue
        if hide_dead and h.status in ("invalid", "revoked", "expired"):
            continue
        data.append({"invite": h.url, "code": code, "source": h.source,
                     "via": ENGINE_LABEL.get(h.engine, h.engine),
                     "status": STATUS_LABEL.get(h.status, h.status or "—"),
                     "time": h.found_at})
    if not data:
        st.warning("No links match the filter.")
        return

    st.dataframe(
        pd.DataFrame(data), use_container_width=True, height=470, hide_index=True,
        column_config={
            "invite": st.column_config.LinkColumn("Invite link", display_text="Open ↗"),
            "code": st.column_config.TextColumn("Code"),
            "source": st.column_config.LinkColumn("Found on", display_text="Source ↗"),
            "via": "Found via",
            "status": "Status",
            "time": "Time",
        })

    rows = state.rows()
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["invite_url", "code", "source_page", "found_via", "status", "time"])
    for code, h in rows:
        w.writerow([h.url, code, h.source, h.engine, h.status, h.found_at])
    all_links = "\n".join(h.url for _, h in rows)

    d1, d2, d3 = st.columns(3)
    d1.download_button("⬇️ Download CSV", buf.getvalue().encode("utf-8"),
                       "whatsapp_group_links.csv", "text/csv", use_container_width=True)
    d2.download_button("⬇️ Download TXT (links only)", all_links,
                       "whatsapp_group_links.txt", "text/plain", use_container_width=True)
    with d3.popover("📋 Copy all links"):
        st.code(all_links or "—", language=None)

def main():
    st.title("🔎 WhatsApp Group Link Hunter")
    st.caption("Deep crawler for `chat.whatsapp.com` invite links — static HTML, JS frameworks, "
               "JSON/API payloads, lazy-load, cookie banners and button-revealed links. "
               "Duplicates are skipped automatically.")

    if "crawl_state" not in st.session_state:
        st.session_state.crawl_state = CrawlState()
    state = st.session_state.crawl_state
    thread = st.session_state.get("crawl_thread")
    running = bool(thread and thread.is_alive())

    with st.sidebar:
        st.header("⚙️ Crawl settings")
        seeds_raw = st.text_area("🌱 Seed URLs — one per line", height=120, key="seeds",
                                 placeholder="https://example.com/whatsapp-group-links")
        mode_label = st.radio("Engine", list(MODES), key="mode")
        mode = MODES[mode_label]
        if not PLAYWRIGHT_OK:
            st.caption("⚠️ Playwright not installed — browser features disabled.")

        left, right = st.columns(2)
        max_pages = left.number_input("Max pages", 5, 2000, 80, 10, key="max_pages")
        max_depth = right.number_input("Crawl depth", 1, 6, 2, key="max_depth")
        workers = left.slider("Parallel requests", 1, 8, 4, key="workers")
        delay = right.slider("Delay per domain (s)", 0.0, 3.0, 0.8, 0.1, key="delay")

        kw = st.text_input("🎯 Priority keywords", "whatsapp, group, join, invite, link, chat",
                           key="kw")
        st.toggle("🔒 Stay on seed subdomains (skip clone mirrors)", True, key="same_host",
                  help="Sites like gruposwats.com link to fr./hn./il. mirrors that are usually "
                       "exact clones — they waste your page budget. Turn off to allow other "
                       "subdomains of the same domain.")
        st.toggle("🖱️ Click buttons to reveal links", True, key="click")
        st.toggle("📜 Dismiss cookie/consent banners", True, key="consent")
        st.toggle("↕️ Auto-scroll (lazy-loaded content)", True, key="scroll")
        st.toggle("🚪 Follow links to external sites", False, key="ext")
        st.toggle("🤖 Respect robots.txt", True, key="robots")
        st.toggle("✅ Verify links against WhatsApp (slower)", False, key="verify")

        start = st.button("🚀 Start crawl", type="primary",
                          use_container_width=True, disabled=running)
        clear = st.button("🗑️ Clear all results", use_container_width=True, disabled=running)

    if clear:
        st.session_state.crawl_state = CrawlState()
        st.rerun()

    if start:
        seeds = parse_seeds(seeds_raw)
        if not seeds:
            st.sidebar.warning("Add at least one valid seed URL.")
        else:
            state.begin_run()
            cfg = CrawlConfig(
                seeds=seeds, max_pages=int(max_pages), max_depth=int(max_depth),
                workers=int(workers), delay=float(delay), mode=mode,
                follow_external=st.session_state.ext, respect_robots=st.session_state.robots,
                click_buttons=st.session_state.click, scroll=st.session_state.scroll,
                dismiss_consent=st.session_state.consent, verify=st.session_state.verify,
                same_host_only=st.session_state.same_host,
                keywords=[k.strip().lower() for k in kw.split(",") if k.strip()])
            st.session_state.cfg_max_pages = cfg.max_pages
            t = threading.Thread(target=Crawler(cfg, state).run, daemon=True, name="crawler")
            st.session_state.crawl_thread = t
            t.start()
            st.rerun()

    if running:
        live_view()
    else:
        show_results(state)

if __name__ == "__main__":
    main()
