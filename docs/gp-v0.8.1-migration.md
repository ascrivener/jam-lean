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

## Phase 2 (after stage 2 is on `gp-v0.8.1`)

| Area | Paper files | GP PRs |
|---|---|---|
| Accounts and accumulation | accounts.tex, accumulation.tex, merklization.tex (C(12), C(13), C(255)), pvm_invocations.tex general and accumulate host calls | #533, #539 (junior services), #542, #545, #558, #565, #567, #571, #581 |
| Sweep | every file | re-read the whole diff; move remaining v0.8.0 citations to v0.8.1 |
