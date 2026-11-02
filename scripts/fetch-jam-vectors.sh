#!/usr/bin/env bash
# Fetch the Gray Paper v0.8.0 JAM test vectors (codec and accumulate STF only) into vendor/jam-test-vectors.
set -euo pipefail
REPO=https://github.com/davxy/jam-test-vectors.git
TAG=v0.8.0
DEST="$(dirname "$0")/../vendor/jam-test-vectors"
if [ ! -d "$DEST/.git" ]; then
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$TAG" --filter=blob:none \
    --sparse "$REPO" "$DEST"
  git -C "$DEST" sparse-checkout set codec stf/accumulate
fi
echo "jam-test-vectors at $(git -C "$DEST" describe --tags)"
