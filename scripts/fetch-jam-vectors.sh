#!/usr/bin/env bash
# Fetch the Gray Paper v0.8.0 JAM test vectors (codec, the STFs the model checks, trie, shuffle and
# erasure) into vendor/jam-test-vectors.
set -euo pipefail
REPO=https://github.com/davxy/jam-test-vectors.git
TAG=v0.8.0
DEST="$(dirname "$0")/../vendor/jam-test-vectors"
if [ ! -d "$DEST/.git" ]; then
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$TAG" --filter=blob:none \
    --sparse "$REPO" "$DEST"
fi
git -C "$DEST" sparse-checkout set codec stf/accumulate stf/history stf/authorizations stf/statistics \
  stf/preimages stf/disputes stf/assurances stf/reports stf/safrole trie shuffle erasure
echo "jam-test-vectors at $(git -C "$DEST" describe --tags)"
