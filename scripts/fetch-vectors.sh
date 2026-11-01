#!/usr/bin/env bash
# Fetch the pinned PVM test vectors into vendor/jamtestvectors.
set -euo pipefail
REPO=https://github.com/koute/jamtestvectors.git
COMMIT=6bf3768e5b37bbe4ca5d6e1306284ecb27c0198f   # branch master_pvm_initial
DEST="$(dirname "$0")/../vendor/jamtestvectors"
if [ ! -d "$DEST/.git" ]; then
  git clone --quiet --filter=blob:none --no-checkout "$REPO" "$DEST"
fi
git -C "$DEST" fetch --quiet origin "$COMMIT" 2>/dev/null || git -C "$DEST" fetch --quiet origin master_pvm_initial
git -C "$DEST" -c advice.detachedHead=false checkout --quiet "$COMMIT"
echo "vectors at $(git -C "$DEST" rev-parse HEAD)"
