#!/usr/bin/env bash
# Build the documentation site into docs/site/_site (run from anywhere; used by .github/workflows/docs.yml).
#   _site/index.html   the landing page (landing/index.html)
#   _site/api/         doc-gen4 pages for PVM, JAM and JamCrypto
#   _site/book/        A Companion to the Gray Paper (Verso; Companion/, CompanionMain.lean)
set -euo pipefail
cd "$(dirname "$0")"

# Source links point at the GitHub source view of the commit being documented.
export DOCGEN_SRC="${DOCGEN_SRC:-github}"

lake build PVM:docs JAM:docs JamCrypto:docs
lake build companion
rm -rf _book
lake exe companion --output _book

rm -rf _site
mkdir -p _site
cp -r .lake/build/doc _site/api
cp -r _book/html-multi _site/book
# Verso links a chapter as "<dir>/#<tag>" but gives the chapter's top <h1> no id: give it that id,
# so the link lands at the top instead of failing to find its target.
python3 - _site/book <<'EOF'
import os, re, sys
book = sys.argv[1]
pages = {}
for d, _, fs in os.walk(book):
    if "index.html" in fs:
        pages[os.path.relpath(d, book).replace(os.sep, "/")] = os.path.join(d, "index.html")
want = {}
for p in pages.values():
    for href in re.findall(r'href="([^"#:]*)#([^"]+)"', open(p, encoding="utf-8").read()):
        want.setdefault(href[0].rstrip("/") or ".", set()).add(href[1])
fixed = 0
for d, frags in want.items():
    p = pages.get(d)
    if not p:
        continue
    s = open(p, encoding="utf-8").read()
    missing = [f for f in frags if f'id="{f}"' not in s]
    # Only a chapter's own tag (no "--" path, as Verso's section ids have): one per page.
    missing = [f for f in missing if "--" not in f]
    if len(missing) == 1:
        m = re.search(r"<main>(.*?)<h1>", s, re.S)
        if m:
            k = m.end() - len("<h1>")
            s = s[:k] + f'<h1 id="{missing[0]}">' + s[k + len("<h1>"):]
            open(p, "w", encoding="utf-8").write(s)
            fixed += 1
print(f"build-site.sh: chapter-top ids added on {fixed} page(s)")
EOF
# An introduction on the API index page, in place of doc-gen4's generic heading.
python3 - _site/api/index.html landing/api-intro.html <<'EOF'
import sys
page, intro = sys.argv[1], open(sys.argv[2], encoding="utf-8").read()
s = open(page, encoding="utf-8").read()
head = "<h1> Welcome to the documentation page </h1>"
if head not in s:
    sys.exit("build-site.sh: doc-gen4's index heading changed; update the API intro injection")
open(page, "w", encoding="utf-8").write(s.replace(head, intro, 1))
EOF
cp landing/index.html _site/index.html
touch _site/.nojekyll
echo "site: $(du -sh _site | cut -f1) in $(pwd)/_site"
