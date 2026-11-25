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

Gaps, where the paper leaves behaviour undefined:

| Note | Section | Finding |
|---|---|---|
| 13 | Ψ_H | Ψ_H* need not terminate: a handler that returns more gas than it was given can recurse forever. Termination holds for handlers that do not add gas (`JAM/Theorems/HostGas.lean`). |
| 2 | 𝔟 | A branch target ı + 𝒵(…) can be negative, where ζ is undefined. |
| 17 | Y | **a** ∈ 𝔹_{:𝖹_I}; the paper does not say what happens to a longer argument. |
| 18 | Ψ_R | The refine dispatcher passes x̄ to `fetch`, but Ψ_R's arguments do not include that data. The account state **d** is also implicit. |
| 19 | Ψ_R, §14.3 | A looked-up preimage that is not of the form ℰ(↕**m**, **c**). |
| 20 | Ω_Z (`pages`) | The row defines only (ω'_7, **m**'), with no ε'. |
| 21 | §8, F(c) | α[c] ⊖ {(g_w)_a} names a g bound only in the case condition; it should say the guarantee on core c. |
| 23 | §13.1 | The guarantee count tests κ'_v ∈ G, a validator key against a set of Ed25519 keys. The fresh accumulator [(0, …), …] has no stated length (|κ'| is implied). |
| 24 | §13.2 | The provision sum ∑_{(s, **d**) ∈ E_P} reuses s, already bound by ∀ s ∈ **s**. It reads as a fresh binding unless the reader knows it is a filter. |
| 25 | §12.4 | No error is named for an invalid E_P, and no order is given between the ordering check and the providable check. |
| 31 | §6.7 | Tickets are ordered by their identifier y ∈ ℍ, but no order on ℍ is defined (lexicographic on octets is the evident reading and the vectors use it). `$jam_ticket_seal` ⌢ η_2' ⌢ e appends a natural number to an octet sequence without saying how it is encoded. No errors are named for an invalid E_T, and no order is given between its conditions. |
| 26 | Appendix C | No encoding of Booleans {⊤, ⊥} is defined, though 𝔼_D's judgments and faults contain them; 0/1 is the evident reading and the vectors use it. |
| 29 | §10.2 | The fault condition r ∈ ψ_B' ⇔ r ∉ ψ_G' ⇔ v can be read as a chain or as ((… ⇔ …) ⇔ v); the second accepts a ⊤ fault on a good report. No errors are named and no order is given between the conditions. |
| 30 | §11.2 | No errors are named and no order is given between the assurance conditions. |
| 33 | Appendix D, §13.2 | D.1 says every non-discriminator number in the state is serialized fixed-length by the size of its term, but π_C and π_S (C(13)) hold ℕ and ℕ_G terms with no stated encoding; the traces use the general encoding ℰ for all of them, gas included. §11.4.1 does not say whether the ancestor set 𝒜 includes the block being imported (needed when the lookup anchor is the parent). |
| 32 | §11.3–§11.4 | R and P divide by 3 (\|**c**\|/3, ⌊i/3⌋) without saying what happens when \|κ'\| is not a multiple of 3; M* uses τ' − 𝖱, which is negative when τ' < 𝖱. No errors are named and no order is given between the guarantee conditions; a segment-root lookup key outside the extrinsic and β fails two conditions at once. |
| v0.8.1-A1 | eq. `accpar`, N(**o**) | GP v0.8.1: the discard function N(**o**) gives every field a value except the post-state, written bare. The prose ("discard all results of the service's execution", except provided preimages) suggests the round's input state; reading it as **o**'s post-state would keep a discarded run's new services and privilege, staging and queue changes while M(s) drops its own account change. The model uses the input state (`JAM/Accumulation.lean`, `accPar`). |

## Resolved in GP v0.8.1

| Note | Resolution |
|---|---|
| 4 | #554: r_D = min(12, ζ_{ı+2} mod 16). |
| 12 | #533: Ψ_H, 𝔉_X and the host functions all use gas in ℕ_G. |

## Paper and vectors

| Note | Finding | Where |
|---|---|---|
| 5 | Ψ returns ı = 0 on ∎ and ☇; the vectors report the exiting instruction. | Paper or vector docs: which one is meant? |
| 15 | The accumulate vectors follow later GP PRs rather than v0.8.0: `bless_from_non_manager-1` and `-2`. | Already in the vectors' CHANGELOG; no issue needed. |
| 33 | The `fuzzy` and `fuzzy_light` block-import traces follow GP #519 (`bless` from a non-manager accepted), like the accumulate vectors (note 15): `fuzzy_light` blocks 77, 86, 118, 148, 151, 163, 165, 179 and `fuzzy` block 17. | Already in the vectors' CHANGELOG; no issue needed. |
| 32 | The vectors' README tiny chainspec omits 𝖫; the tiny vectors (`stf/reports/tiny/lookup_anchor_not_recent-1`, master) use 24, the fuzzer protocol's value. | Vectors: list `max_lookup_anchor_age` in the README's tiny chainspec. |
| 27 | `trie/trie.json` gives 32-octet keys; GP §D.1 state keys are 31 octets. The roots match with the last octet dropped. | Vectors: say keys are cut to 31 octets, or give 31-octet keys. |
| 28 | **Resolved in GP v0.8.1 (#580):** §H.3 now defines the vectors' layout, and the model follows it (all erasure vectors match). Was: every erasure vector pads the message polynomial with zeroes to degree < n = 2^⌈log₂ R(v)⌉ and puts parity word i at point (n + i − R(v))~; §H.3 says degree < R(v) and point ĩ. No GP release (v0.1.1–v0.8.0) describes the vectors' layout; it is the "low rate" layout `reed-solomon-simd` documents (originals in one zero-padded power-of-two chunk, recovery shards in the chunks after). | Paper: if that code is intended (the cited Lin–Chung–Han transform works on power-of-two blocks), §H.3 should define p of degree < n with zeroes at d̃ … (n−1)~ and parity at (n + i − d)~; otherwise the vectors should follow §H.3. |

## Vector coverage

These cases have no test vector, so the readings above are untested:

| Note | Missing case |
|---|---|
| 11 | Any program using `cmov_nz_imm` (opcode 148). |
| 2 | A branch with a target outside [0, \|**c**\|). |
| 3 | A program that maps a page below 2^16. |
| 31 | A tickets extrinsic whose tickets are valid but not all kept in γ_A' (**n** ⊄ γ_A'). |
| 24 | Core statistics π_C, and the refinement and accumulation parts of π_S, in the statistics and preimages suites. They are covered by the reports and accumulate suites. |
| 29 | Ed25519 verification is a parameter of the model, so the disputes, assurances and reports vectors' signatures are not verified; the runner rejects all of them exactly when a vector expects `bad_signature`. |
| 32 | The lookup-anchor conditions of §11.4.1 (x_t ≥ H_T − 𝖫, and h, h' in the ancestor set A): the reports vectors carry no ancestor set. (Master after v0.8.0 adds `lookup_anchor_not_recent`; on its tiny vector see the table above.) |

## Bootstrap service binary

Behaviour of the bootstrap service's PVM binary that differs from the instruction set it implements.
These would go to the service's authors, not to the Gray Paper.

| Where | Finding |
|---|---|
| `Designate` decode, 35300 … 35315 | The bound check on `keys: BoundedVec<[u8; 336], 3·𝖢>` loads 𝖢 sign-extended (`loadI16`), computes 3·𝖢 and zero-extends it from 16 bits, so the decoder accepts n ≤ (3·𝖢) mod 2¹⁶ instead of n ≤ 3·𝖢. The two agree for 𝖢 < 21846 (the full parameters' 𝖢 = 341 gives 1023); for 𝖢 ≥ 21846 the bound wraps and valid key lists are rejected. Proven as stated in `Decode.Designate.designate_heap` (`hnC : n ≤ 3 * C % 65536`). |
| `remove`, 48481 … 48533 | A removal (`write` of an empty value) panics when the host replies FULL, i.e. when the account's threshold balance after the removal still exceeds its balance. A removal only lowers the threshold, so failing it rolls back the whole accumulate where going on would be harmless. Quirk Q18 in `docs/bootstrap-target.md`. |
| `add_recent_work_item`, 8293 … 8323 | The next ring slot is `(c + 1) % (2·𝖢·𝖨)` computed in 32 bits: `2·𝖢·𝖨` is `(𝖢·𝖨 << 1) mod 2³²` (`shloLImm32`, a panic if it is 0) and `c + 1` is reduced mod 2³² by `remU32`. So a stored counter 2³² − 1 wraps to slot 0 rather than to 2³² mod 2·𝖢·𝖨 (quirk Q19 in `docs/bootstrap-target.md`), and parameters with 2·𝖢·𝖨 ≥ 2³² would size the ring mod 2³² (or panic when that is 0). Harmless for the full parameters (2·341·16 = 10912) and for any counter the service itself wrote (always below 2·𝖢·𝖨). The proofs assume 0 < 2·𝖢·𝖨 < 2³² (`RingFits`). |
| SDK `get` (`read` wrapper), 47888 … 47907 | The length returned by Ω_R in ω₇ is compared against the host error codes (≥ 2⁶⁴ − 9) before it is used. A value of exactly 2⁶⁴ − 1 octets is therefore indistinguishable from NONE and `get` returns `None` for a key that is present; lengths in [2⁶⁴ − 9, 2⁶⁴ − 2] trap (47929), and lengths in [2⁶³, 2⁶⁴ − 9) trap as a negative `isize` (47901). The same ambiguity is in Ω_R's interface itself (GP Appendix B: a length and an error code share ω₇), so it may also be a note for the paper. Unreachable in practice; T2 assumes values shorter than 2⁶³ octets (`ValuesFit`). |
| SDK `foreign_historical_lookup` (refine's eager `Lookup`), 49015 … 49074 | The preimage length Ω_H returns in ω₇ is checked against the host error codes and then used as a signed size: lengths in [2⁶³, 2⁶⁴ − 9) trap, and so do lengths above 2³⁷ − 32 (the allocator's limit, counted as heap exhaustion). `Spec.refine` (GP Appendix B.6, Ω_H) returns `lookedUp (some d)` for any preimage d. Unreachable in practice; T1's eager `Lookup` step takes preimages shorter than 2⁶³ octets as an internal hypothesis (`hlen`, whether refine_t1c assumes it is pending with Adam). |

## Bandersnatch VRF-AD specification, Draft 35 (cited by GP v0.8.1)

GP v0.8.1 cites Draft 35 (davxy/bandersnatch-vrf-spec commit 181aba2) for all of Appendix G. Where
its prose and its own vectors (Appendix C, ark-vrf 0.5.0) disagree, JamCrypto's v0.8.1 path
follows the prose by default (`Reading.prose`) and the vectors on request (`Reading.vectors`;
Adam, 2026-11-25). Details in `docs/jamcrypto.md`. For the draft's author, or for the GP if it
should cite a later draft.

| Where | Prose | What the vectors need |
|---|---|---|
| App. A.2, hash_to_curve | "`expand_message_xmd` with SHA-512 (section 5.3.1)" of RFC 9380, whose step 4 is Z_pad = I2OSP(0, s_in_bytes): 128 zero octets for SHA-512. | 48 zero octets. Draft 36 (fcf7012) states the 48 as a deliberate deviation and announces a suite `…-v2` with RFC 9380's 128; GP v0.8.1 cites Draft 35, which does not state it. |
| §4, §5, the fixed points B, S, □ | Each "is defined as" printed coordinates, and is "derived using the `hash_to_curve` function as described in Appendix A.2" from its name. With A.2 read as RFC 9380, the two disagree: the printed coordinates are the 48-octet derivation. | The printed coordinates. |
| §5, Fiat–Shamir of the ring proof | "Begin with empty transcript and "ring-proof" label." | The suite id `Bandersnatch-SHA512-ELL2-v1` as the label; no ring vector verifies with "ring-proof". |
| §5, Fiat–Shamir of the ring proof | "Push R to the transcript after instancing." R is not defined in §5 (Pedersen's nonce commitment is R in §4), and no framing is given. | Nothing is pushed after the instance (Ȳ) other than the proof's own columns. Not modelled under either reading. |

## Not for upstream

- **The picoalloc model's alignment rounding.** A bug in this repository's own model, not in the
  paper or the vectors. The model rounded the data unit from the heap base; the binary rounds it
  in the address space. Fixed in `Services/Picoalloc/Model.lean`.
- **The lookup anchor's state root in `lookupAnchorKnown`.** A bug in this repository's own
  model, found by the jam-lean-target fuzzing work. §11.4.1 (GP eq. 11.36) requires the lookup
  anchor's child to have h'_R = x_lookupanchorpoststate; the model compared it with the anchor's
  x_stateroot, rejecting valid blocks whose lookup anchor differs from their anchor. Fixed in
  `JAM/BlockImport.lean`, with a regression test in `Tests/TraceTest.lean`.
- **The `$` of the context strings.** A bug in this repository's own model, reported by the
  jam-lean-target crypto work. The model kept the GP's `$` as the first octet of `$jam_ticket_seal`
  and the other context strings. In the paper `$` only marks the set of ASCII strings
  (`notation.tex`), though its wording leaves this open; the v0.8.0 vectors settle it: their 58
  ticket proofs verify only with "jam_ticket_seal" ⌢ …. Fixed in `JAM.contextString` (it drops a
  leading `$`), with `#guard`s on X_T, X_E and X_G.
- **Notes 6–10, 14, 16 and 22.** Points where the vectors confirm a subtle reading, or observations
  that need no change.
