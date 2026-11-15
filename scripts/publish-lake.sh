#!/usr/bin/env bash
# Publish this checkout's .lake as the `lake-cache` release, for scripts/fetch-lake.sh. Run by CI after a
# green build on main (needs GH_TOKEN with contents: write, and gh, zstd).
#
# Assets: lake-<sha>.tar.zst.NN (parts under GitHub's 2 GiB asset limit) and meta.txt, which names the
# current parts. New parts are uploaded before meta.txt moves to them, and the previous build's parts are
# kept, so a download in progress never sees a half-replaced set. Older parts are deleted, so the release
# holds at most two builds. meta.txt only moves forward (by commit time), since main's runs can overlap.
set -euo pipefail
REPO="${GITHUB_REPOSITORY:?}"; SHA="${GITHUB_SHA:?}"; TAG=lake-cache
time=$(git show -s --format=%cI "$SHA")
work=$(mktemp -d -p "${RUNNER_TEMP:-/tmp}")

if ! gh release view "$TAG" -R "$REPO" >/dev/null 2>&1; then
  gh release create "$TAG" -R "$REPO" --prerelease --target "$SHA" --title "main's latest .lake (for cloud sessions)" \
    --notes "Written by CI on every green main run; fetch it with scripts/fetch-lake.sh. Not a release of the project."
fi

cur_time=$(gh release download "$TAG" -R "$REPO" -p meta.txt -O - 2>/dev/null | sed -n 's/^time=//p' || true)
if [ -n "$cur_time" ] && [ "$(date -d "$cur_time" +%s)" -gt "$(date -d "$time" +%s)" ]; then
  echo "the published build ($cur_time) is newer than $SHA ($time); not publishing"; exit 0
fi
cur_sha=$(gh release download "$TAG" -R "$REPO" -p meta.txt -O - 2>/dev/null | sed -n 's/^sha=//p' || true)

df -h "$work" .lake | sed 1d
tar -cf - .lake | zstd -T0 -6 -q | split -b 1900M -d - "$work/lake-$SHA.tar.zst."
parts=$(cd "$work" && ls lake-"$SHA".tar.zst.* | tr '\n' ' ')
ls -l "$work"
gh release upload "$TAG" -R "$REPO" --clobber "$work"/lake-"$SHA".tar.zst.*
printf 'sha=%s\ntime=%s\ntoolchain=%s\nparts=%s\n' "$SHA" "$time" "$(cat lean-toolchain)" "$parts" > "$work/meta.txt"
gh release upload "$TAG" -R "$REPO" --clobber "$work/meta.txt"

# keep this build's parts and the previous one's; delete the rest
gh release view "$TAG" -R "$REPO" --json assets -q '.assets[].name' | while read -r a; do
  case "$a" in
    meta.txt|lake-"$SHA".*) ;;
    lake-"${cur_sha:-none}".*) ;;
    *) gh release delete-asset "$TAG" "$a" -R "$REPO" -y ;;
  esac
done
rm -rf "$work"
