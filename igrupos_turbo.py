#!/usr/bin/env python3
"""
igrupos_turbo.py — super-speed WhatsApp-only invite harvester for igrupos.com
GET-only, no browser, never touches votar-*/denunciar*/reportar*/masvistos/search
or any telegram/discord/signal/facebook section.
Usage:
    python igrupos_turbo.py
    python igrupos_turbo.py --workers 4 --delay 0.3
    python igrupos_turbo.py --entries https://www.igrupos.com/whatsapp
"""
import re
import csv
import time
import threading
import argparse
from urllib.parse import urlparse
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

GROUP_RE  = re.compile(r'''href=["'](?:(https?://[^/"']+)?/)?grupo/(\d+)["']''')
NEXT_RE   = re.compile(r'''<link[^>]*rel=["']next["'][^>]*href=["']([^"']+)["']''', re.I)
INVITE_RE = re.compile(r"https?://chat\.whatsapp\.com/(?:invite/)?([A-Za-z0-9_\-]{18,32})", re.I)
TITLE_RE  = re.compile(r"<title>(.*?)</title>", re.S | re.I)

# ------------------------------------------------------------ plumbing
class Throttle:
    def __init__(self, delay=0.0):
        self.delay, self.t, self.lock = delay, 0.0, threading.Lock()
    def wait(self):
        if not self.delay:
            return
        with self.lock:
            now = time.time()
            sleep_for = self.t + self.delay - now
            self.t = max(now, self.t + self.delay)
        if sleep_for > 0:
            time.sleep(sleep_for)

THROTTLE = Throttle()
_local = threading.local()

def sess():
    if getattr(_local, "s", None) is None:
        s = requests.Session()
        s.headers.update({"User-Agent": UA, "Accept-Language": "en-US,en;q=0.9"})
        _local.s = s
    return _local.s

def get(url, timeout=15):
    THROTTLE.wait()
    return sess().get(url, timeout=timeout)

# ------------------------------------------------------------ parsing
def group_refs(html, origin):
    """(origin, group_id) pairs on a listing page — same site only."""
    host = urlparse(origin).netloc
    out = set()
    for m in GROUP_RE.finditer(html):
        abs_origin = m.group(1)
        if abs_origin is None or urlparse(abs_origin).netloc == host:
            out.add((origin, m.group(2)))
    return out

def rel_next(html):
    m = NEXT_RE.search(html)
    return m.group(1) if m else None

# ------------------------------------------------------------ listing crawl
def harvest_listing(entry, ex, workers, max_pages):
    entry = entry.rstrip("/")
    origin = f"{urlparse(entry).scheme}://{urlparse(entry).netloc}"
    found = set()
    try:
        r = get(entry)
    except Exception as e:
        print(f"   ✗ {entry} → {type(e).__name__}")
        return found
    if r.status_code != 200:
        print(f"   ✗ {entry} → HTTP {r.status_code}")
        return found
    refs = group_refs(r.text, origin)
    found |= refs
    nxt = rel_next(r.text)
    print(f"   page 1 → {len(refs)} groups" + (f" · next: {nxt}" if nxt else " · single page"))
    if not nxt:
        return found

    # Fast path: pagination is entry/{n} → probe pages in parallel
    if urlparse(nxt).path.rstrip("/") == urlparse(entry).path.rstrip("/") + "/2":
        page, dead_chunks, dupe_chunks = 2, 0, 0
        while page <= max_pages and dead_chunks < 2 and dupe_chunks < 3:
            chunk = [n for n in range(page, page + workers) if n <= max_pages]
            page += workers
            futs = {ex.submit(get, f"{entry}/{n}"): n for n in chunk}
            got, statuses = set(), []
            for f in as_completed(futs):
                n = futs[f]
                try:
                    resp = f.result()
                    statuses.append(resp.status_code)
                    if resp.status_code == 200 and resp.url.rstrip("/").endswith(f"/{n}"):
                        got |= group_refs(resp.text, origin)
                except Exception:
                    statuses.append(0)
            new = got - found
            found |= got
            if not got:                                   # truly empty/dead pages
                dead_chunks += 1
                if any(s in (403, 429, 503) for s in statuses):
                    print("   ⚠ throttled (403/429/503) — rerun with --workers 4 --delay 0.3")
                    break
            elif not new:                                 # pages repeat content
                dupe_chunks += 1
            else:
                dead_chunks = dupe_chunks = 0
                print(f"   pages {chunk[0]}–{chunk[-1]} → +{len(new)} new (total {len(found)})")
        return found

    # Fallback: unusual pagination → walk the rel="next" chain
    seen, url, guard = {entry}, nxt, 0
    while url and url not in seen and guard < max_pages:
        guard += 1
        seen.add(url)
        try:
            resp = get(url)
        except Exception:
            break
        if resp.status_code != 200:
            break
        found |= group_refs(resp.text, origin)
        url = rel_next(resp.text)
    return found

# ------------------------------------------------------------ group pages
def fetch_group(origin, gid):
    r = get(f"{origin}/grupo/{gid}")
    if r.status_code != 200:
        return None
    m = INVITE_RE.search(r.text)          # the onclick="window.open('https://chat.whatsapp.com/CODE'…)"
    if not m:
        return None
    t = TITLE_RE.search(r.text)
    return {"origin": origin, "id": gid, "code": m.group(1),
            "invite": f"https://chat.whatsapp.com/{m.group(1)}",
            "title": (t.group(1).strip() if t else "")[:100]}

def harvest_groups(refs, ex, results, lock):
    refs = list(refs)
    total, done = len(refs), 0
    futs = {ex.submit(fetch_group, o, g): (o, g) for o, g in refs}
    for f in as_completed(futs):
        try:
            rec = f.result()
        except Exception:
            rec = None
        with lock:
            done += 1
            if rec:
                results[futs[f]] = rec
            if done % 100 == 0 or done == total:
                print(f"   {done}/{total} group pages → {len(results)} invites")

# ------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser(description="igrupos.com WhatsApp invite harvester")
    ap.add_argument("--entries", nargs="*", default=[
        "https://www.igrupos.com/whatsapp",
        "https://www.igrupos.com/tag/whatsapp/stickers",
        "https://www.igrupos.com/whatsapp/andaluz/amistad",
        "https://www.igrupos.com/grupo/20261005",
    ])
    ap.add_argument("--workers", type=int, default=10)
    ap.add_argument("--delay", type=float, default=0.0, help="seconds between requests (0 = fastest)")
    ap.add_argument("--max-pages", type=int, default=300, help="max pagination pages per listing")
    ap.add_argument("--out", default="igrupos_whatsapp")
    args = ap.parse_args()

    THROTTLE.delay = args.delay

    listings, singles = [], set()
    for e in args.entries:
        p = urlparse(e)
        origin = f"{p.scheme}://{p.netloc}"
        m = re.fullmatch(r"/grupo/(\d+)/?", p.path)
        (singles.add((origin, m.group(1))) if m else listings.append(e.rstrip("/")))

    all_ids, results, lock = set(singles), {}, threading.Lock()
    ex = ThreadPoolExecutor(max_workers=args.workers)
    try:
        for e in listings:
            print(f"▶ Listing: {e}")
            all_ids |= harvest_listing(e, ex, args.workers, args.max_pages)
        print(f"\n▶ Fetching {len(all_ids)} unique group pages "
              f"({args.workers} workers, {args.delay}s delay)…")
        harvest_groups(all_ids, ex, results, lock)
    except KeyboardInterrupt:
        print("\n⏹ Interrupted — saving partial results…")
    finally:
        try:
            ex.shutdown(wait=False, cancel_futures=True)
        except TypeError:
            ex.shutdown(wait=False)

    # newest groups first, deduped by invite code (same group is often listed twice)
    seen_codes, rows = set(), []
    for key in sorted(results, key=lambda k: (k[0], -int(k[1]))):
        if results[key]["code"] in seen_codes:
            continue
        seen_codes.add(results[key]["code"])
        rows.append(results[key])

    print(f"\n✅ {len(rows)} unique WhatsApp invite links · "
          f"{len(all_ids) - len(results)} group pages had no/dead link")
    with open(f"{args.out}.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["origin", "id", "title", "invite", "code"])
        w.writeheader()
        w.writerows(rows)
    with open(f"{args.out}.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(r["invite"] for r in rows))
    print(f"💾 Saved → {args.out}.csv · {args.out}.txt")

if __name__ == "__main__":
    main()
