#!/usr/bin/env bash
# Fetch the binary block-import traces of the Gray Paper v0.8.0 JAM test vectors
# (davxy/jam-test-vectors `traces/*/*.bin`, about 1.3 GB) into vendor/jam-traces.
# The JSON copies are left out. Pass trace names to fetch only those, e.g.
#   scripts/fetch-trace-vectors.sh fallback safrole storage_light
set -euo pipefail
REPO=https://github.com/davxy/jam-test-vectors.git
TAG=v0.8.0
DEST="$(dirname "$0")/../vendor/jam-traces"
if [ ! -d "$DEST/.git" ]; then
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$TAG" --filter=blob:none \
    --no-checkout "$REPO" "$DEST"
fi
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  names=(fallback safrole storage storage_light preimages preimages_light fuzzy fuzzy_light)
fi
patterns=()
for n in "${names[@]}"; do patterns+=("/traces/$n/*.bin"); done
git -C "$DEST" sparse-checkout set --no-cone "${patterns[@]}"
git -C "$DEST" -c advice.detachedHead=false checkout --quiet "$TAG"
echo "jam-test-vectors traces at $(git -C "$DEST" describe --tags): ${names[*]}"
