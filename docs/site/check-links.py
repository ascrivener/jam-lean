#!/usr/bin/env python3
"""Check the built site's internal links and anchors.

Usage:  python3 -I docs/site/check-links.py docs/site/_site        (exit 1 on a broken link)

Pages checked: the landing page, every book page, and the API pages of PVM, JAM and JamCrypto.
Internal links are relative links and absolute links into the Pages site
(https://ascrivener.github.io/jam-lean/…, which the book uses for API links): each must name an
existing file, and its #fragment an id or name in that page. Verso's `<base href>` is honoured.
`#top` is the top of the page (HTML's own rule). Into doc-gen4's pages of core and Std only the file
is checked (they link to some undocumented auxiliary declarations). External links are not fetched.
"""

import html.parser
import os
import re
import sys
import urllib.parse

SITE = "https://ascrivener.github.io/jam-lean/"


class Page(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links, self.ids, self.base = [], set(), None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "base" and a.get("href") and self.base is None:
            self.base = a["href"]
        for k in ("id", "name"):
            if a.get(k):
                self.ids.add(a[k])
        for k in ("href", "src"):
            if a.get(k) and tag in ("a", "link", "script", "img"):
                self.links.append(a[k])


def ours(path):
    """Pages whose anchors we answer for: the book, the landing page and our API pages (doc-gen4's
    pages of core and Std link to some undocumented auxiliary declarations, e.g. `Eq.ndrec`)."""
    p = os.path.normpath(path)
    return (p in ("index.html", ".") or p.startswith("book") or p == os.path.join("api", "index.html")
            or re.match(r"api/(PVM|JAM|JamCrypto)(\.html|/)", p) is not None)


def main():
    if len(sys.argv) != 2:
        sys.exit("usage: check-links.py <site dir>")
    root = sys.argv[1]
    cache = {}

    def parse(f):
        if f not in cache:
            p = Page()
            p.feed(open(f, encoding="utf-8", errors="replace").read())
            cache[f] = p
        return cache[f]

    pages = ["index.html"]
    for d, _, fs in os.walk(os.path.join(root, "book")):
        pages += [os.path.relpath(os.path.join(d, f), root) for f in fs if f.endswith(".html")]
    pages.append("api/index.html")
    for top in ("PVM", "JAM", "JamCrypto"):
        if os.path.exists(os.path.join(root, "api", top + ".html")):
            pages.append(f"api/{top}.html")
        for d, _, fs in os.walk(os.path.join(root, "api", top)):
            pages += [os.path.relpath(os.path.join(d, f), root) for f in fs if f.endswith(".html")]

    bad, n = [], 0
    for page in sorted(set(pages)):
        p = parse(os.path.join(root, page))
        here = "/" + os.path.dirname(page) + "/"
        if p.base:
            here = urllib.parse.urljoin(here, p.base)
        for link in p.links:
            if link.startswith(("mailto:", "javascript:", "data:")) or link in ("#", ""):
                continue
            if link.startswith(SITE):
                target = link[len(SITE):]
            elif re.match(r"[a-z]+:", link) or link.startswith("//"):
                continue  # external
            elif link.startswith("#"):
                target = page + link
            else:
                target = urllib.parse.urljoin(here, link).lstrip("/")
            path, _, frag = target.partition("#")
            path = urllib.parse.unquote(path.split("?")[0]) or page
            f = os.path.join(root, path)
            if os.path.isdir(f):
                f = os.path.join(f, "index.html")
            n += 1
            if not os.path.exists(f):
                bad.append(f"{page}: {link}: no such file")
            elif (frag and frag != "top" and f.endswith(".html") and ours(path)
                  and urllib.parse.unquote(frag) not in parse(f).ids):
                bad.append(f"{page}: {link}: no such anchor")
    for b in bad:
        print("BROKEN", b)
    print(f"check-links: {n} internal links from {len(set(pages))} pages, {len(bad)} broken")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
