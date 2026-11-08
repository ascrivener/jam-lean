# Upstream candidates

Findings from this model worth reporting to the Gray Paper or the test vectors. The full notes
are in the README, under "Notes on the paper and the vectors"; the numbers below are theirs.
None has been filed yet.

Before filing, check each against the latest Gray Paper: some may be fixed after v0.8.0.

## Gray Paper issues

Inconsistencies, where the paper contradicts itself:

| Note | Section | Finding |
|---|---|---|
| 1 | §A.10 | 𝔓_S compares ω_A = ω_D, which read literally compares register values. The gas model has no values, so it must mean the indices r_A = r_D. |
| 3 | §A.4 | The prose says RAM below 2^16 always panics, but the formula for ε^μ only considers inaccessible indices. |
| 12 | Ψ_H | The handler type 𝔉_X returns gas in ℕ_G, but Ψ_H's result is ℤ_G and the host functions compute ϱ − g, which can be negative. |

Gaps, where the paper leaves behaviour undefined:

| Note | Section | Finding |
|---|---|---|
| 13 | Ψ_H | Ψ_H* need not terminate: a handler that returns more gas than it was given can recurse forever. Termination holds for handlers that do not add gas (`JAM/Theorems/HostGas.lean`). |
| 2 | 𝔟 | A branch target ı + 𝒵(…) can be negative, where ζ is undefined. |
| 4 | three-register instructions | r_D = min(12, ζ_{ı+2}): the paper does not say how values ≥ 16 should be read. |
| 17 | Y | **a** ∈ 𝔹_{:𝖹_I}; the paper does not say what happens to a longer argument. |
| 18 | Ψ_R | The refine dispatcher passes x̄ to `fetch`, but Ψ_R's arguments do not include that data. The account state **d** is also implicit. |
| 19 | Ψ_R, §14.3 | A looked-up preimage that is not of the form ℰ(↕**m**, **c**). |
| 20 | Ω_Z (`pages`) | The row defines only (ω'_7, **m**'), with no ε'. |
| 21 | §8, F(c) | α[c] ⊖ {(g_w)_a} names a g bound only in the case condition; it should say the guarantee on core c. |
| 23 | §13.1 | The guarantee count tests κ'_v ∈ G, a validator key against a set of Ed25519 keys. The fresh accumulator [(0, …), …] has no stated length (|κ'| is implied). |
| 24 | §13.2 | The provision sum ∑_{(s, **d**) ∈ E_P} reuses s, already bound by ∀ s ∈ **s**. It reads as a fresh binding unless the reader knows it is a filter. |
| 25 | §12.4 | No error is named for an invalid E_P, and no order is given between the ordering check and the providable check. |

## Paper and vectors

| Note | Finding | Where |
|---|---|---|
| 5 | Ψ returns ı = 0 on ∎ and ☇; the vectors report the exiting instruction. | Paper or vector docs: which one is meant? |
| 15 | The accumulate vectors follow later GP PRs rather than v0.8.0: `bless_from_non_manager-1` and `-2`. | Already in the vectors' CHANGELOG; no issue needed. |

## Vector coverage

These cases have no test vector, so the readings above are untested:

| Note | Missing case |
|---|---|
| 11 | Any program using `cmov_nz_imm` (opcode 148). |
| 2 | A branch with a target outside [0, \|**c**\|). |
| 3 | A program that maps a page below 2^16. |
| 4 | A three-register instruction with ζ_{ı+2} ≥ 16. |
| 24 | Core statistics π_C, and the refinement and accumulation parts of π_S, in the statistics and preimages suites. They are covered by the reports and accumulate suites. |

## Not for upstream

- **The picoalloc model's alignment rounding.** A bug in this repository's own model, not in the
  paper or the vectors. The model rounded the data unit from the heap base; the binary rounds it
  in the address space. Fixed in `Services/Picoalloc/Model.lean`.
- **Notes 6–10, 14, 16 and 22.** Points where the vectors confirm a subtle reading, or observations
  that need no change.
