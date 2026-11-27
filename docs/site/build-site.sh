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
