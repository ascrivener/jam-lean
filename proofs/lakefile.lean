import Lake
open Lake DSL

/-! Proofs about the jam-lean model that use Mathlib (Adam, 2026-11-26, jam-lean#272).

A separate Lake package so that the model, its executables and tests never resolve or fetch
Mathlib: nothing outside `proofs/` imports anything here. `lake build` from this directory builds
the model modules it needs in the root package and then these proofs. -/

package «jam-proofs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «jam-lean» from ".."

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc1"

/-- Erasure coding (GP v0.8.1 Appendix H): recovery inverts encoding. -/
@[default_target]
lean_lib ErasureProofs
