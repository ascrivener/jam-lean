#!/usr/bin/env bash
# Fetch the Gray Paper v0.8.0 JAM test vectors (codec, the STFs the model checks, trie, shuffle and
# erasure) into vendor/jam-test-vectors. During the v0.8.1 migration, stf/reports comes from master
# commit REPORTS_REV instead, which adds the GP #563 work-report-limit vectors (errors 28–31) and
# fixes the vectors' lookup anchor slots (decided by the coordinator, 2026-11-25).
set -euo pipefail
REPO=https://github.com/davxy/jam-test-vectors.git
TAG=v0.8.0
REPORTS_REV=5e8d2a2423256d6138a3f265a251429a4c63f66f
DEST="$(dirname "$0")/../vendor/jam-test-vectors"
if [ ! -d "$DEST/.git" ]; then
  git -c advice.detachedHead=false clone --quiet --depth 1 --branch "$TAG" --filter=blob:none \
    --sparse "$REPO" "$DEST"
fi
git -C "$DEST" sparse-checkout set codec stf/accumulate stf/history stf/authorizations stf/statistics \
  stf/preimages stf/disputes stf/assurances stf/reports stf/safrole trie shuffle erasure
if ! git -C "$DEST" cat-file -e "$REPORTS_REV^{commit}" 2>/dev/null; then
  git -C "$DEST" fetch --quiet --depth 1 --filter=blob:none origin "$REPORTS_REV"
fi
git -C "$DEST" -c gc.auto=0 checkout --quiet "$REPORTS_REV" -- stf/reports
echo "jam-test-vectors at $(git -C "$DEST" describe --tags), stf/reports at ${REPORTS_REV:0:7}"
