import PVM.Fast
import JAM.Fast.Blake2b
import JAM.Fast.Keccak
import JAM.Fast.Trie
import JAM.Fast.HostGeneral

/-!
# All fast compiled forms

Imports every fast module of the model (`PVM.Fast` and `JAM.Fast.*`). Each defines a faster
implementation of a spec definition, proves it equal, and registers the equality with `@[csimp]`;
the kernel and every theorem see only the spec definitions. Executables import this module
(through `JAM`). See `docs/fast-paths.md` for the list of pairs and for the spec modules that import
fast modules so that their own compiled code is fast.
-/
