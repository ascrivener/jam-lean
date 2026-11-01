#!/usr/bin/env bash
# Regenerate PVM/Tables.lean from the pinned Gray Paper and fail on any difference.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
"$ROOT/scripts/fetch-paper.sh"
OUT="$(mktemp)"
python3 -I "$ROOT/scripts/gen_tables.py" "$ROOT/vendor/graypaper/text/pvm.tex" "$OUT"
if diff -u "$ROOT/PVM/Tables.lean" "$OUT"; then
  echo "PVM/Tables.lean matches the paper"
else
  echo "PVM/Tables.lean differs from the table generated from the paper" >&2
  exit 1
fi
