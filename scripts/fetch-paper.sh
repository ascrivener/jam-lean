#!/usr/bin/env bash
# Fetch the pinned Gray Paper source into vendor/graypaper.
set -euo pipefail
REPO=https://github.com/gavofyork/graypaper.git
TAG=v0.8.1
DEST="$(dirname "$0")/../vendor/graypaper"
if [ ! -d "$DEST/.git" ]; then
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$TAG" "$REPO" "$DEST"
fi
if ! git -C "$DEST" rev-parse -q --verify "refs/tags/$TAG" >/dev/null; then
  git -C "$DEST" fetch --quiet --depth 1 origin tag "$TAG"
fi
git -C "$DEST" -c advice.detachedHead=false checkout --quiet "$TAG"
echo "graypaper at $(git -C "$DEST" describe --tags)"
