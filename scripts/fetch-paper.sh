#!/usr/bin/env bash
# Fetch the pinned Gray Paper source into vendor/graypaper.
set -euo pipefail
REPO=https://github.com/gavofyork/graypaper.git
TAG=v0.8.0
DEST="$(dirname "$0")/../vendor/graypaper"
if [ ! -d "$DEST/.git" ]; then
  git clone --quiet --depth 1 --branch "$TAG" "$REPO" "$DEST"
fi
git -C "$DEST" -c advice.detachedHead=false checkout --quiet "$TAG"
echo "graypaper at $(git -C "$DEST" describe --tags)"
