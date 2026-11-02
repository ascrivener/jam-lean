#!/usr/bin/env bash
# Regenerate PVM/Tables.lean and JAM/Constants.lean from the pinned Gray Paper; fail on any difference.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
"$ROOT/scripts/fetch-paper.sh"
OUT="$(mktemp)"
python3 -I "$ROOT/scripts/gen_tables.py" "$ROOT/vendor/graypaper/text/pvm.tex" "$OUT"
status=0
if diff -u "$ROOT/PVM/Tables.lean" "$OUT"; then
  echo "PVM/Tables.lean matches the paper"
else
  echo "PVM/Tables.lean differs from the table generated from the paper" >&2
  status=1
fi
python3 -I "$ROOT/scripts/gen_constants.py" "$ROOT/vendor/graypaper/text/definitions.tex" "$OUT"
if diff -u "$ROOT/JAM/Constants.lean" "$OUT"; then
  echo "JAM/Constants.lean matches the paper"
else
  echo "JAM/Constants.lean differs from the constants generated from the paper" >&2
  status=1
fi
exit $status
