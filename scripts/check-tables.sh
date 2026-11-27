#!/usr/bin/env bash
# Regenerate PVM/Tables.lean, JAM/Constants.lean, the docs site's GP macro table
# (docs/site/gp-macros.json, gp-macros.js) and the book's paper tables (docs/site/gp-labels.json, gp-equations.json)
# from the pinned Gray Paper; fail on any difference.
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
python3 -I "$ROOT/scripts/gen_gp_labels.py" "$ROOT/vendor/graypaper" "$OUT"
if diff -u "$ROOT/docs/site/gp-labels.json" "$OUT"; then
  echo "docs/site/gp-labels.json matches the paper"
else
  echo "docs/site/gp-labels.json differs from the section table generated from the paper" >&2
  status=1
fi
python3 -I "$ROOT/scripts/gen_equations.py" "$ROOT/vendor/graypaper" "$OUT"
if diff -q "$ROOT/docs/site/gp-equations.json" "$OUT" > /dev/null; then
  echo "docs/site/gp-equations.json matches the paper"
else
  diff -u "$ROOT/docs/site/gp-equations.json" "$OUT" | head -40
  echo "docs/site/gp-equations.json differs from the equation table generated from the paper" >&2
  status=1
fi
OUTJS="$(mktemp)"
python3 -I "$ROOT/scripts/gen_macros.py" "$ROOT/vendor/graypaper" "$OUT" "$OUTJS"
if diff -u "$ROOT/docs/site/gp-macros.json" "$OUT" && diff -u "$ROOT/docs/site/gp-macros.js" "$OUTJS"; then
  echo "docs/site/gp-macros.{json,js} match the paper"
else
  echo "docs/site/gp-macros.{json,js} differ from the macro table generated from the paper" >&2
  status=1
fi
exit $status
