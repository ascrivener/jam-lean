# Migrating the model from GP v0.8.0 to v0.8.1

Decided by Adam on 2026-11-25. Source: tag v0.8.1 of gavofyork/graypaper (2026-11-16).

- **Integration branch `gp-v0.8.1`.** Migration PRs target this branch, not `main`. Until the
  migration is done, `main` stays a coherent v0.8.0 model, and jam-lean-target keeps pinning it.
  When every row below is done, `gp-v0.8.1` merges into `main`, and the last v0.8.0 commit of
  `main` is tagged `gp-v0.8.0`.
- **The checklist is the text diff, not only the PR list.** `git diff v0.8.0 v0.8.1 -- text` is
  authoritative (17 files, 971+/711−). The PRs below are a guide to it. Each area's owner checks
  every hunk of its files and says in its PR which hunks it covered.
- **Storage-key stage 2** lands on `main` first (as v0.8.0), then `main` is merged into
  `gp-v0.8.1`, then phase 2 starts.
- **Checks.** Paper-only modelling; every existing vector suite stays green except vector edits
  dictated by v0.8.1 (CLAUDE.md, "Vectors during the migration"). Validation against v0.8.1 vectors
  and the 0.8.1 fuzzer happens when they are published.
- **Proofs** (Services) are not migrated; they stay as last checked (docs/whats-proven.md).

## Phase 1 (now; does not touch the stage-2 files)

Stage-2 files, off limits in phase 1: JAM/Account.lean, JAM/Host/General.lean, JAM/Accumulate.lean,
JAM/Accumulation.lean, JAM/Preimages.lean, JAM/State.lean, Tests/TraceState.lean.

| Area | Paper files | GP PRs | Owner |
|---|---|---|---|
| PVM | pvm.tex; pvm_invocations.tex: Ψ, Ψ_M, refine host calls | #554, #559, #538, #582, #588, #530, #589 | child "PVM" |
| Blocks | safrole, reporting_assurance, statistics (not its C(13) serialization), work_packages_and_reports, serialization, header, erasure_coding, auditing, definitions (constants), bandersnatch.tex | #534, #537, #543, #557, #560, #562, #563, #564, #565 (stats), #566, #568, #574, #575, #580, #583, #587 | child "Blocks" |
| Crypto (jam-lean-target JamCrypto) | bandersnatch.tex | #550 Thin VRF | child "VRF" (jam-lean-target) |

Phase 1 notes (Blocks):
- No change needed: auditing (#534) and the Ξ / A / paged-proof hunks (#568, #583), because the model
  has no auditing, no Ξ and no availability specifier (the target's refine extension computes the
  erasure root; see the follow-ups below).
- 𝖪_P and 𝖪_D (#567) are generated in JAM/Constants.lean; their rules are phase 2.
- Vectors run with the chain values they were generated with (v0.8.0), so expected outputs are not
  edited; Params.full is v0.8.1. Reports vectors come from davxy/jam-test-vectors master 5e8d2a2.

## Phase-1 sweep: hunk coverage (2026-11-25)

Every hunk of `git diff v0.8.0 v0.8.1` in the phase-1 paper files, checked against `gp-v0.8.1`.
Status is one of: **done** (with the PR), **no change** (wording, or not modelled), **phase 2**, or
**open**.

### pvm.tex

| Hunk | Status | Where |
|---|---|---|
| Ψ: ϱ̃ = ⊥ on ∎ and ☇ (#588) | done #244 | `PVM.runFuel`, `Prepared.run`, `psi_eq` |
| deblob: \label, **c** ∈ 𝔹_{:𝖹_C}, **j** ∈ ⟦ℕ_R⟧_{:𝖹_J}, z ≤ 4 (#559) | done #244 | `Blob.parse?`, `Blob.parse?_limits` |
| "except as indicated" layout | no change | wording |
| r_D = min(12, ζ_{ı+2} mod 16) (#554) | done #244 | `Program.decode` (and `CodeView.decode`) |
| Ψ_H: ℕ_G gas, `\context`, 𝔉_X without ∎; Φ → Ψ typo (#533, #536) | done #244 | `HostStatus`, `HostFn`, `psiHFuel` |
| Y: metadata ℰ(↕**m**), eqs. `jamblobformat` and `ramlayoutfits`, closing note (#582) | done #251 | `skipMetadata?`, `JamBlob.parseStd?`, `standardInit` |
| Ψ_M: `\context`, u = ϱ − ϱ' (#533) | done #244 | `invocationResult` |
| š counts the destination of the cmov instructions (#559) | done (already modelled) | `Instr.srcRegs` |

### pvm_invocations.tex (Ψ_I, Ψ_R, general and refine functions)

| Hunk | Status | Where |
|---|---|---|
| Ψ_I prose: "the work-package p and the core c" | no change | wording |
| Ψ_I dispatcher: context {∅}, unknown id → (∞, 0, ω', μ) (#533) | done #248 | `RefineHost.dispatchI`, `unknown` (context `Unit`) |
| PVM instance type with handle (#530) | done #255 | `InnerPvm.handle` |
| Export prose "may be assumed" | no change | wording |
| Ψ_R: BAD / BIG on the full blob, Ψ_M on the full blob (#582) | done #251 | `psiR` |
| Ψ_R: context (**m**, **P**, **e**), F with `compile` = 9 and machine … expunge = 10 … 15, unknown id (#530, #533) | done #255, #248 | `RefineCtx`, `RefineHost.dispatch` |
| Host Functions intro: ϱ* = max(ϱ − g, 0), (ε*, ω*, μ*, x*), defaults (#533) | done #248 | `charged` |
| Ω_G: ω'_7 = ϱ* | done #248 | `hostGas` |
| Ω_♊: no own (ε', ϱ'); g with ω'_7; (**o**, s) per eq. `jamblobformat` | done #248, #251 | `hostGrowHeap`, `heapBounds` |
| Ω_♊: b uses Q(s) (#538) | phase 2 | `heapBounds` (phase 2, part 2) |
| Ω_Y: gas by ω_10, 𝖬_{Y,∅} otherwise; 𝖶_I in case 0 (#533, #563) | done #250 | `hostFetch`, `Constants.CgasY`, `Params.encode` |
| `lookup`, `read`, `write`, `info` moved to the accumulate functions | phase 2 | accumulate host calls |
| Refine Functions intro: context triple | done #255 | `RefineCtx` |
| Ω_H: **a** = **d**[s] or **d**[ω_7], no key guard; g in the right column (#533) | done #255 | `RefineHost.historicalLookup` |
| Ω_E: context argument | done #255 | `RefineHost.exportSeg` |
| Ω_Γ `compile` (#530) | done #255 | `RefineHost.compile` |
| Ω_M from a module handle, WHO, g = 𝖬_M (#530) | done #255, #250 | `RefineHost.machine` |
| Ω_P, Ω_O, Ω_Z, Ω_K: renumbered, g in the right column, ϱ* for Ω_K | done #255, #248 | `peek`, `poke`, `pages`, `invoke` |
| Ω_X: modes m = 0 / 1 / other (#530) | done #255 | `RefineHost.expunge` |
| Accumulate invocation and functions | phase 2 | — |

### Blocks-area files

| File | Hunk | Status | Where |
|---|---|---|---|
| safrole | 𝕂^∅ (`nullvalkey`); Φ uses it (#543) | done #246 | `Block.nullValidatorKey`, `Safrole.offendersFilter`, `Reports.blacklist` |
| reporting_assurance | ℝ field order, r_g 5th (#537) | done | `WorkReport` (encoding unchanged: Appendix C already had it 5th) |
| reporting_assurance | 𝔼_A without anchor; ordered-unique by a_v (#562, #574) | done #246 | `Assurance`, `checkAssurance` |
| reporting_assurance | eq. `reportrefineload`: per-report limits (#563) | done #253 | `Reports.checkReportLoad`: all seven rows, in the paper's order; error names from the vectors (28–31) |
| statistics | π_V preimage size; guarantees by (κ'_v)_e ∈ G; provisions filtered by service (#565, #567) | done | `Statistics.lean` |
| statistics | layout | no change | typesetting |
| work_packages_and_reports | 𝖶_B → 𝖶_I in `checkextractsize`; eq. `maxbundlesize`; `wplimits` < → ≤ (#563) | constants done #250; rules no change | no work-package validity in the model; on-chain use is `reportrefineload` (#253) |
| work_packages_and_reports | **p**_c is the whole preimage (#582) | done #251 | `WorkPackage.authCode` |
| work_packages_and_reports | Ξ tuple order, `countupexports`, ᵀ_m / s♣ / paged proofs (#537, #568, #583) | no change | no Ξ or availability specifier in the model (jam-lean-target follow-up) |
| serialization | ℰ(⊥) = [0], ℰ(⊤) = [1]; ℰ_A without anchor; O(a) (#560, #562) | done #246 | `Block.lean` encoders and decoders |
| serialization | deferred transfer gains u (#539) | phase 2 | `DeferredTransfer` in `JAM/Work.lean` (edit approved for the phase-2 child) |
| header | **g** of `extrinsichash` uses O(a) (#560) | done #246 | `Extrinsic.hashParts` |
| erasure_coding | example v = 1020; ᵀ_m | no change | prose; s♣ not modelled |
| erasure_coding | padded systematic code (#580) | done #246 | `Erasure.paddedShards`, `encodeWith`, `recover` |
| auditing | 16-bit tranche comparand (#534) | no change | no auditing in the model |
| definitions | 𝖦_A, 𝖦_I, 𝖦_R, 𝖦_T, 𝖶_A, 𝖶_B, 𝖶_I, 𝖹_C, 𝖹_J, 𝖬_M, 𝖬_Γ, 𝖬_{Y,∅}, 𝖭_P, 𝖭_D, 𝖬_V (#557, #559, #563, #567, #587, …) | done #250 | `JAM/Constants.lean` (rules for 𝖭_P / 𝖭_D and Ω_V: phase 2) |
| definitions | ℕ_P, 𝕏 / 𝕥 types, Ω_V (#539, #542, #558) | phase 2 | — |
| definitions | ℤ_G removed; instance type renamed; Ω_Γ / Ω_X descriptions | done #244, #248, #255 | — |
| definitions | 𝖣 refers to `forget`; 𝖬_B "per record"; blank line | no change | wording |
| bandersnatch | Thin VRF (#550) | no change in the model | crypto is a parameter; `JamCrypto` carries the v0.8.1 path (Draft 35 prose by default, its vectors as the switch `Reading.vectors`; `docs/jamcrypto.md`) |
| notation | "subscript implies the key exists" removed (#566) | no change | lookups are `Option`-typed, invalidity is explicit (phase-2 files not audited here) |
| notation | ZIP 215 citation; BLS aggregatable form (#541) | no change | `edVerify` is a parameter; BLS is never verified |
| overview | 𝔼 order (𝔼_T, 𝔼_P, 𝔼_G, 𝔼_A, 𝔼_D) (#575) | done | `Block.Extrinsic` |
| overview | ℤ_G removed from `gasregentry` | done #244 | — |

### Open after the sweep

Nothing in phase 1. Phase-2 items are marked in the tables.

Docstrings in the phase-1 areas now cite v0.8.1 (PVM, Refine, Safrole, Reports, Work, Codec, Decode,
BlockImport, Disputes, Authorization, History, Shuffle). The remaining "v0.8.0" mentions are
deliberate comparisons ("v0.8.0 had …") or cite the v0.8.0 test vectors. `JAM/Host/General.lean`
still cites v0.8.0 in its header and eq. `conditions`; it is left to phase 2, which is changing it.

## Phase 2 (after stage 2 is on `gp-v0.8.1`)

| Area | Paper files | GP PRs |
|---|---|---|
| Accounts and accumulation | accounts.tex, accumulation.tex, merklization.tex (C(12), C(13), C(255)), pvm_invocations.tex general and accumulate host calls | #533, #539 (junior services), #542, #545, #558, #565, #567, #571, #581; deferred from phase 1: #582 metadata in Y / Ψ_M with `ServiceAccount.code` and the Refine/Is-Authorized code fetch, #538 `heapBounds` in Host/General, #564 C(13) validator statistics serialization (State.lean) |
| Sweep | every file | re-read the whole diff; move remaining v0.8.0 citations to v0.8.1 |

## Suspended until v0.8.1 vectors

These checks of the `model` job are suspended on `gp-v0.8.1` because the published vectors are GP
v0.8.0 and cannot pass under v0.8.1 (decided 2026-11-25; `main` keeps full v0.8.0 coverage). Each
is restored as soon as davxy/jam-test-vectors publishes v0.8.1 vectors.

| Check | Why suspended | What still runs |
|---|---|---|
| `acctest` (accumulate STF vectors) | The vectors' service binaries are v0.8.0 programs: v0.8.0 host-call ids (bless 15 … provide 27) and register layouts (write's key at ω_7, and so on), so under v0.8.1's host calls (#533, #539) even plain storage writes answer WHO (15 of 63 pass). | The runner is built; hand-written v0.8.1 guards in `Tests/HostGeneralTest.lean` cover the accumulate host calls (write, supervisor, new, transfer, eject, bless), the discard rule N and the transfer partition T. `preimagestest` runs no service code and stays. |
| `tracetest` block import | Every trace header's H_R is a v0.8.0 state root; v0.8.1's C(255) (#539) and C(13) (#564) encodings give other roots, so Υ rejects every block. Rewriting headers would fabricate vectors. | The T(σ) round trip of every raw state, after the test-only conversion `Tests.TraceState.upgradeRaw` (C(255): a_u = s, a_u' = a_r, a_b' = 0; C(13) re-encoded). |

## jam-lean-target follow-ups (after the merge to `main`)

- Refine extension: the erasure root (#580) and the "exports nothing" case (#583) are now defined by
  v0.8.1; replace the v0.8.0 choices (§H.3 erasure root, Error on nothing exported).
- Default `--gp` to 0.8.1 with the pin bump.

## Suspended until v0.8.1 vectors

Checks that the v0.8.0 vectors cannot exercise faithfully under the v0.8.1 model. Each comes back
when the v0.8.1 vectors are pinned.

- **Block traces, H_X under v0.8.1 (#562).** The trace blocks' assurances carry the v0.8.0
  anchor, so their H_X commits to the v0.8.0 encoding. `Tests/TraceTest.lean` reads the blocks
  with `Tests/V080.lean` and calls `JAM.importBlockCommitted xh`, giving the block's v0.8.0
  commitment as `xh`. `importBlockCommitted` differs from `importBlock` only in where the expected
  H_X comes from (`importBlock` passes v0.8.1's eq. `extrinsichash`); every other check runs.
  So on the traces, H_X is checked against v0.8.0's formula, not v0.8.1's. v0.8.1's formula is
  covered by `Extrinsic.hash` and the `#guard`s in `Tests/V080.lean`.
- **Assurances STF, `assurance_with_bad_attestation_parent-1` (tiny, full) (#562).** v0.8.1 has
  no anchor condition, so the vector has no counterpart. It is listed in
  `Tests/AssurancesTest.lean`.
