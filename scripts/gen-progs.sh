#!/usr/bin/env bash
# Regenerate the symbolic executor's `Prog` modules (PVM/SymExec/gen_prog.py,
# docs/symexec-spike.md) from the code facts, in place. CI runs this and fails if any
# output differs from the committed file.
#
# Usage: scripts/gen-progs.sh            (from the repository root)
#
# Covered:
#   Services/Bootstrap/SymExec/ProgF.lean  Code, then every CodeF slice (via CodeFAll)
#   Services/Bootstrap/SymExec/ProgU.lean  the CodeF slices with from_utf8 (instructions in L10/L11,
#                                          block starts in L28/L29), then Code
# Source order matters: a fact at an index is taken from the first source that has it.
set -euo pipefail
cd "$(dirname "$0")/.."
G=PVM/SymExec/gen_prog.py
B=Services/Bootstrap

python3 "$G" $B/SymExec/ProgF.lean Services.Bootstrap.SymExec F \
  "Services.Bootstrap.Code=$B/Code.lean" \
  "Services.Bootstrap.CodeF@Services.Bootstrap.CodeFAll=$B/CodeF/L*.lean"

python3 "$G" $B/SymExec/ProgU.lean Services.Bootstrap.SymExec U \
  "Services.Bootstrap.CodeF=$B/CodeF/L10.lean,$B/CodeF/L11.lean,$B/CodeF/L28.lean,$B/CodeF/L29.lean" \
  "Services.Bootstrap.Code=$B/Code.lean"
