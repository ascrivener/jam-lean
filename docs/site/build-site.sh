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
cp landing/index.html _site/index.html
touch _site/.nojekyll
echo "site: $(du -sh _site | cut -f1) in $(pwd)/_site"
