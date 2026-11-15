#!/usr/bin/env bash
# Start a cloud session from main's latest build instead of a cold one (~4.5–5 h).
#
#   scripts/fetch-lake.sh [--force]
#
# 1. Installs the pinned Lean toolchain under ~/.lean (from its GitHub release) unless `lake` of that
#    version is already on PATH, and prints the PATH line to use.
# 2. Downloads the .lake that CI published from its latest green run on main (release `lake-cache`,
#    written by scripts/publish-lake.sh) and unpacks it here. `lake build` then rebuilds only what
#    differs from that commit.
# The repository is public, so no token is needed; downloads go to github.com release assets.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

REPO=ascrivener/jam-lean
TAG=lake-cache
force=0; [ "${1:-}" = --force ] && force=1

toolchain=$(cut -d: -f2 lean-toolchain)          # e.g. v4.36.0-rc1
ver=${toolchain#v}
tcdir="$HOME/.lean/lean-$ver-linux"

# zstd: the binary if present, else Python's zstandard module (installed if missing).
unzstd() {
  if command -v zstd >/dev/null; then zstd -dc; else
    python3 -c 'import zstandard' 2>/dev/null || pip install -q zstandard >&2
    python3 -c 'import sys,zstandard; zstandard.ZstdDecompressor().copy_stream(sys.stdin.buffer, sys.stdout.buffer)'
  fi
}

if command -v lake >/dev/null && lake --version | grep -q "$ver"; then
  echo "toolchain: $(command -v lake) ($ver)"
else
  if [ ! -x "$tcdir/bin/lake" ]; then
    echo "installing Lean $ver into $tcdir"
    mkdir -p "$HOME/.lean"
    curl -sSfL --retry 5 "https://github.com/leanprover/lean4/releases/download/$toolchain/lean-$ver-linux.tar.zst" \
      | unzstd | tar -x -C "$HOME/.lean"
  fi
  export PATH="$tcdir/bin:$PATH"
  echo "toolchain: $tcdir/bin — run: export PATH=\"$tcdir/bin:\$PATH\""
fi

if [ -d .lake ] && [ "$force" -ne 1 ]; then
  echo ".lake already exists; pass --force to replace it" >&2; exit 1
fi

api="https://api.github.com/repos/$REPO/releases/tags/$TAG"
rel=$(curl -sSfL --retry 5 "$api") || { echo "no $TAG release yet: build cold with lake build" >&2; exit 1; }
base="https://github.com/$REPO/releases/download/$TAG"

# meta.txt names the published build: sha=, time=, toolchain=, parts= (in order).
meta=$(curl -sSfL --retry 5 "$base/meta.txt")
get() { printf '%s\n' "$meta" | sed -n "s/^$1=//p"; }
sha=$(get sha); parts=$(get parts); pub_tc=$(get toolchain)
[ "$pub_tc" = "$(cat lean-toolchain)" ] || { echo "published build uses $pub_tc, not $(cat lean-toolchain)" >&2; exit 1; }
for p in $parts; do
  printf '%s' "$rel" | grep -q "\"name\": *\"$p\"" || { echo "asset $p missing (a publish in progress?); retry shortly" >&2; exit 1; }
done
echo "published build: main@${sha:0:12} ($(get time))"
git cat-file -e "$sha^{commit}" 2>/dev/null && ! git merge-base --is-ancestor "$sha" HEAD \
  && echo "note: HEAD does not contain main@${sha:0:12}; lake rebuilds whatever differs" >&2

# Each part goes to a file first: a proxy can reset a long transfer, and only a file can resume
# (`curl -C -`). Its size is checked against the release, then it is fed to the unpacker and deleted,
# so the disk holds at most one part (< 2 GiB) next to the growing .lake (~11 GB).
asset_size() {  # size of release asset $1, from the release JSON
  printf '%s' "$rel" | python3 -c 'import json,sys; print(next(a["size"] for a in json.load(sys.stdin)["assets"] if a["name"]==sys.argv[1]))' "$1"
}
fetch_part() {  # download part $1 to file $2, resuming after resets
  local want n=0; want=$(asset_size "$1"); rm -f "$2"
  while [ "$(stat -c %s "$2" 2>/dev/null || echo 0)" -lt "$want" ]; do
    [ "$n" -ge 30 ] && { echo "download of $1 kept failing" >&2; return 1; }
    [ "$n" -gt 0 ] && { echo "resuming $1 ($n)" >&2; sleep 2; }
    curl -sSfL --retry 5 -C - -o "$2" "$base/$1" || true
    n=$((n+1))
  done
  [ "$(stat -c %s "$2")" -eq "$want" ] || { echo "$1: size mismatch" >&2; return 1; }
}
rm -rf .lake.partial .lake.dl; mkdir .lake.partial
for p in $parts; do fetch_part "$p" .lake.dl; cat .lake.dl; rm -f .lake.dl; done \
  | unzstd | tar -x -C .lake.partial
rm -rf .lake; mv .lake.partial/.lake .lake; rmdir .lake.partial
echo "unpacked .lake ($(du -sh .lake | cut -f1)); now: lake build"
