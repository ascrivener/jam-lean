#!/usr/bin/env bash
# Check declarations' closures with nanoda, the kernel witness-lean runs on chain, and report each
# node's checking time against one refine's budget.
#   scripts/nanoda-profile.sh OUT_DIR MODULE DECL...
# Needs WITNESS_LEAN (a witness-lean checkout, `cargo build --release -p lean-host` built) and
# LEAN4EXPORT (lean4export built for this lean-toolchain).
set -euo pipefail
OUT=$1; MOD=$2; shift 2
HOST=${WITNESS_LEAN:?set WITNESS_LEAN}/target/release/lean-host
: "${LEAN4EXPORT:?set LEAN4EXPORT}"
rm -rf "$OUT"; mkdir -p "$OUT"
lake env "$LEAN4EXPORT" "$MOD" -- "$@" 2>"$OUT/export.err" | "$HOST" convert - "$OUT/pack" --pack >"$OUT/convert.log" 2>&1
python3 -c "import json, sys; [print(json.dumps(e)) for e in json.load(open(sys.argv[1]))]" \
  "$OUT/pack/manifest.json" >"$OUT/pack/manifest.jsonl"
(ulimit -s unlimited 2>/dev/null || true; "$HOST" profile "$OUT/pack" "$OUT/profile" >"$OUT/profile.log" 2>&1)
python3 "$(dirname "$0")/nanoda_report.py" "$OUT"
