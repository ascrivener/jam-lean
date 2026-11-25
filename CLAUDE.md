# Working on jam-lean

jam-lean is a Lean 4 model of JAM from the Gray Paper v0.8.1 (migrating from v0.8.0 on branch `gp-v0.8.1`, see `docs/gp-v0.8.1-migration.md`). It is used to prove theorems about
the real compiled service binaries in `services/`. Read `docs/whats-proven.md` for what is proved,
`docs/bootstrap-target.md` for the Bootstrap targets (T1 refine, T2 accumulate), and
`docs/HANDOFF.md` for the state of work in flight.

**Start of session:** run `scripts/fetch-lake.sh` before building. It installs the toolchain and
unpacks main's latest CI build (about 2–3 min; needs about 13 GB of free disk), so `lake build`
rebuilds only what changed since then instead of building cold for 4.5–5 h.

## Rules

- **Source.** Model only from the Gray Paper **v0.8.1** (tag v0.8.1 of gavofyork/graypaper,
  2026-11-16; Adam moved the model from v0.8.0 on 2026-11-25). Don't copy other implementations,
  especially JAR. Docstrings cite the paper (section and equation); code changed for v0.8.1 cites
  v0.8.1. Don't follow paper changes made after the v0.8.1 tag. `JamCrypto` carries both the
  v0.8.0 and v0.8.1 paths, selected by `JamCrypto.GpVersion`.
- **Vectors during the migration.** An expected output of a v0.8.0 vector may change only where a
  v0.8.1 paper change dictates it. List each such edit in the PR body with the GP PR and the
  equation. Prefer the vectors' own updates (davxy/jam-test-vectors master) where they cover it.
- **Toolchain.** Lean v4.36.0-rc1, with core and Std only. If installing elan is blocked, download
  the official release.
- **Forbidden:** `sorry`, `partial def`, `implemented_by`, `native_decide` and `bv_decide`.
  Axioms may be only `propext`, `Classical.choice` and `Quot.sound`. Check with `#print axioms` or
  `scripts/CheckAxioms.lean`.
- **Git.**
  - Never push to `main`.
  - Use PRs, squash-merged once CI is green.
  - Commit messages end with a `Co-Authored-By:` trailer for Claude and a `Claude-Session:` link.
  - PR bodies end with "🤖 Generated with [Claude Code](https://claude.com/claude-code)".
  - Don't name the model in commits or PRs.
- **Findings.** Report disagreements between the paper and the test vectors, or between the model
  and the binary, in the PR body, and add them to `docs/upstream-candidates.md`.
- **Build pitfalls.**
  - `pvm_go` runs out of memory above about 25 instructions with stores. Use the symbolic
    executor (`PVM/SymExec`, see `docs/symexec-spike.md`) for longer straight-line stretches.
  - Pass `(S0 := S0) (S1 := S1)` explicitly.
  - Elaboration can die silently, so check exit codes.
  - Before each PR, run `lake build` (the model: `PVM` and `JAM`) and the model job's tests in the
    background. Since storage-key stage 2 the Services proofs do not build against the current
    model (last kernel-checked at `c22c197`; see `docs/whats-proven.md`), so `Services` is no
    longer a default target. When proof work resumes, restate them through the account accessors
    (`storageGet`, `requestGet`, …) and run `lake build Services` before each proof PR.
  - New code facts go in a new append-only tier, not a regeneration of an existing one: see
    `docs/code-fact-tiers.md`.

## CI

- Bounds:
  - A cold full build takes about 4.5–5 h; the model alone takes minutes.
  - Each attempt's build steps are bounded at 300 min, inside a 355-min job.
- **Timeouts resume on their own.** An attempt that runs out of time saves its partial build, skips
  the checks and ends green; the next attempt job (`attempt-2`, `attempt-3`) resumes from it. Only
  `attempt-3` running out fails the run; re-run it and it resumes from the cache. See
  `docs/BUILD-INFRA.md`.
- Runs on `main` are never cancelled, and they save the cache.
- **Two lines of jobs.** `model` builds PVM, JAM and the tests and runs every vector suite, in
  minutes, on every run. The proofs (`attempt-1..3`) build everything, including Services, and run
  **only on demand** (Adam, 2026-11-25): Actions → CI → Run workflow, on `main` or a branch. Pushes
  and PRs skip them. A model change that breaks a Services proof is found when proof work resumes:
  start that work with a manual run on `main`, and fix what it finds first.
- **Merge rule.** A PR may merge when `model` is green and the attempts are green or skipped. The
  `proofs` job checks exactly that and is the check branch protection requires.
- **Proof work.** A PR that changes Services or the proofs needs a green manual run on its branch
  before merging. To gate PRs automatically again, restore the `scripts/services-affected.py` step in
  `ci.yml`'s `changes` job.
- **Re-sync rule.** After a PR that regenerates code facts (`Services/Bootstrap/Code*`) lands on
  `main`, re-sync an open PR only if it imports the regenerated module, directly or transitively.
  Otherwise merge it on its own green CI. Sequence code-fact regenerations after the PRs that
  import them, to avoid extra cold rebuilds.

## Standing decisions (Adam)

- **Crypto** stays a parameter. SHA-512 is in plain Lean.
- **JamCrypto** (moved from jam-lean-target, 2026-11-25) implements the crypto parameter in plain
  Lean. The model never imports it.
- **Logging:** the text of log messages is never specified. Log sites are proved frame-only:
  terminates, keeps memory and the allocator context, and writes only its own buffer.
- **Heap exhaustion** is an allowed outcome, not a quirk. A failed allocation, and a request that
  is too large (more than 2^37 − 32 octets), count as heap exhaustion. T1 carries it as the
  `ExhaustsHeap` disjunct, and T2 as "some n".
- **T1 excludes `RandomStorageRefine`** (`hrsr`). Modelling `SmallRng` comes later.
- **T2 assumes `ValuesFit`** (`hvals`): storage values, preimages and encoded inputs are shorter
  than 2^63 octets (decided 2026-11-15, tightened from 2^64: a value of 2^64 − 1 octets collides with
  NONE in the SDK's `get`, and lengths in [2^63, 2^64 − 1) trap at 47901 / 47929).
- **First milestone: T1c for canonical payloads** (M1), via an interim milestone covering only the
  fixed-width and Export instructions.
- **The findings report** for Parity waits until full T1 and T2 are proved.
- **Named hypotheses until they land** are allowed. Examples: facts about the vendored blob
  (`VendoredFacts` and `FmtRO`, discharged in step 10 of `docs/bootstrap-target.md`), and the Fmt
  log-site hypotheses. Each must be listed in the theorem's docstring and in
  `docs/whats-proven.md`.

## Decision rules for agents

- **Implementation details:** decide yourself.
- **Escalate to Adam, with options and a recommendation:**
  - anything that changes what a theorem claims or assumes;
  - anything outward-facing or irreversible;
  - any new line of work.
- **Fine without asking:**
  - weakening a hypothesis;
  - adding a lemma;
  - generalising a statement in place while keeping every existing statement unchanged.
- **Usage limits.** Keep the number of parallel sessions within the limit Adam sets (see docs/HANDOFF.md). When a session's
  context gets large (about 400k tokens), compact it instead of restarting: first update
  `docs/HANDOFF.md` (decisions, open items, where things are) and merge it, so the state survives in
  git as well as in the summary. The cost of each turn grows with context.
