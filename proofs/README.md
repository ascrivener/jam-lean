# Mathlib proofs about the model

A separate Lake package (Adam, 2026-11-26, jam-lean#272): Mathlib (tag `v4.36.0-rc1`, matching the
toolchain) is allowed only here. Nothing outside `proofs/` imports these modules, so the model, its
executables and tests never resolve or fetch Mathlib. The package requires the root package by
path (`require «jam-lean» from ".."`) and does not change the model's definitions.

```
cd proofs
lake exe cache get        # Mathlib's prebuilt oleans
lake build                # builds the model modules it needs (in ../.lake) and the proofs
lake env lean CheckAxioms.lean   # only propext, Classical.choice, Quot.sound
```

## `ErasureProofs`: erasure-code recovery (GP v0.8.1 Appendix H)

Against `JAM/Erasure.lean` as it is (namespace `JAM.Erasure.Proofs`):

| Module | Content |
| --- | --- |
| `Field` | GF(2¹⁶) = `AdjoinRoot (X¹⁶ + X⁵ + X³ + X² + 1)` over `ZMod 2`; `φ` maps a 16-bit number to the element with those coordinates in 1, α, …, α¹⁵. α has order 2¹⁶ − 1 (small kernel computations by `decide +kernel`, no `native_decide`), so the ring is a field (`instField`). |
| `Tables` | The model's table loops (`expTable`, `logTable`, `toFieldTable`, `ofFieldTable`) by loop invariants, never evaluated: `GF.add`/`GF.mul`/`GF.inv` are +, ·, ⁻¹ through `φ`; `toField`/`ofField` (Cantor basis) are inverse bijections below 2¹⁶. |
| `Interp` | `interpolate (lagrange src tgt) words` evaluates Mathlib's `Lagrange.interpolate` through the points (x_{src[k]}, words[k]~) at each x_t, for distinct source indices below 2¹⁶ (`interpolate_lagrange`). |
| `Recovery` | Every coded word is an evaluation of the piece's polynomial of degree < d' (`encode_word`, `msgPoly_degree_lt`), so any d' points determine it; the headline results below. |

Headline theorems (`ErasureProofs/Recovery.lean`):

```lean
theorem recover_encode {v : ℕ} (hv : v ≤ 32768) {data : ByteArray} {chunks : List ByteArray}
    (henc : encode v data = some chunks) {J : List ℕ} (hJ : J.Nodup)
    (hlen : J.length = originalShards v) (hJv : ∀ j ∈ J, j < v) :
    recover v (J.map fun j => (chunks[j]!, j)) = some data

theorem erasure_recovery {v : ℕ} (hv : v ≤ 32768) (data : ByteArray)
    (hsize : data.size % (2 * originalShards v) = 0) :
    ∃ chunks, encode v data = some chunks ∧ chunks.length = v ∧
      ∀ J : List ℕ, J.Nodup → J.length = originalShards v → (∀ j ∈ J, j < v) →
        recover v (J.map fun j => (chunks[j]!, j)) = some data

theorem encode_isSome_iff (v : ℕ) (data : ByteArray) :
    (encode v data).isSome ↔ data.size % (2 * originalShards v) = 0

-- the two chains of the vectors: 1023 validators / any 342 chunks, 6 validators / any 3 chunks
theorem recover_encode_full ... (hlen : J.length = 342) (hJv : ∀ j ∈ J, j < 1023) : ...
theorem recover_encode_tiny ... (hlen : J.length = 3) (hJv : ∀ j ∈ J, j < 6) : ...
```

`v ≤ 2¹⁵` keeps every code index (below v + d' − d) under 2¹⁶, so distinct indices are distinct
field points; it covers both chains. The chunks may be given in any order.
