#!/usr/bin/env bash
# The companion book's worked examples (docs/site/examples/*.json) must be what the current model
# computes: rebuild the generator (Tests/Examples.lean), write the examples afresh into a temporary
# directory and fail on any difference, including a missing or extra file. Needs the vectors
# (scripts/fetch-vectors.sh, scripts/fetch-jam-vectors.sh). To update the committed files after a
# model change: lake build examples-exe && .lake/build/bin/examples
set -euo pipefail
cd "$(dirname "$0")/.."
lake build examples-exe
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
.lake/build/bin/examples "$OUT"
if ! diff -ru docs/site/examples "$OUT"; then
  echo "check-examples: docs/site/examples differs from what the model computes;" >&2
  echo "  regenerate with: lake build examples-exe && .lake/build/bin/examples" >&2
  exit 1
fi
echo "check-examples: $(ls "$OUT" | wc -l) worked examples match the model"
