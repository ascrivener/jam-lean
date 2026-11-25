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

## Phase 2 (after stage 2 is on `gp-v0.8.1`)

| Area | Paper files | GP PRs |
|---|---|---|
| Accounts and accumulation | accounts.tex, accumulation.tex, merklization.tex (C(12), C(13), C(255)), pvm_invocations.tex general and accumulate host calls | #533, #539 (junior services), #542, #545, #558, #565, #567, #571, #581; deferred from phase 1: #582 metadata in Y / Ψ_M with `ServiceAccount.code` and the Refine/Is-Authorized code fetch, #538 `heapBounds` in Host/General, #564 C(13) validator statistics serialization (State.lean), work_packages "p_c without metadata" (with #582) |
| Sweep | every file | re-read the whole diff; move remaining v0.8.0 citations to v0.8.1 |

## Suspended until v0.8.1 vectors

These checks of the `model` job are suspended on `gp-v0.8.1` because the published vectors are GP
v0.8.0 and cannot pass under v0.8.1 (decided 2026-11-25; `main` keeps full v0.8.0 coverage). Each
is restored as soon as davxy/jam-test-vectors publishes v0.8.1 vectors.

| Check | Why suspended | What still runs |
|---|---|---|
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
