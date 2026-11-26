import PVM.Fast.Basic
import PVM.Fast.Mem
import PVM.Fast.Alu
import PVM.Fast.Gas
import PVM.Fast.Parse
import PVM.Fast.Step
import PVM.Fast.Host

/-!
# The fast compiled forms of the PVM

Every module here defines a faster implementation of a spec definition, proves it equal, and
registers the equality with `@[csimp]`. The kernel and every theorem see only the spec definitions.
A `@[csimp]` replacement takes effect where a *caller* is compiled with the lemma imported, so
executables import this module (through `PVM` or `JAM.Fast`), and the few spec modules whose own
compiled code must be fast import the specific fast modules they need (see `docs/fast-paths.md`,
checked by `scripts/check-fast-imports.py`).
-/
