# Working on jam-lean

jam-lean is a Lean 4 model of JAM from the Gray Paper v0.8.0. It is used to prove theorems about
the real compiled service binaries in `services/`. Read `docs/whats-proven.md` for what is proved,
`docs/bootstrap-target.md` for the Bootstrap targets (T1 refine, T2 accumulate), and
`docs/HANDOFF.md` for the state of work in flight.

## Rules

- **Source.** Model only from the Gray Paper v0.8.0. Don't copy other implementations, especially
  JAR. Docstrings cite the paper (section and equation). Stay on v0.8.0: don't switch to later
  paper changes such as #519.
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
  - Run the full `lake build` in the background before each PR.

## CI

- Bounds:
  - A cold full build takes about 4.5–5 h.
  - The build step is bounded at 290 min, inside a 355-min job.
  - A partial build is saved to the cache.
- **A timed-out run (exit 137 at ~module 2280) is not a proof error.** Re-run it once; it resumes
  from the cache.
- Runs on `main` are never cancelled, and they save the cache.
- **Re-sync rule.** After a PR that regenerates code facts (`Services/Bootstrap/Code*`) lands on
  `main`, re-sync an open PR only if it imports the regenerated module, directly or transitively.
  Otherwise merge it on its own green CI. Sequence code-fact regenerations after the PRs that
  import them, to avoid extra cold rebuilds.

## Standing decisions (Adam)

- **Crypto** stays a parameter. SHA-512 is in plain Lean.
- **Logging:** the text of log messages is never specified. Log sites are proved frame-only:
  terminates, keeps memory and the allocator context, and writes only its own buffer.
- **Heap exhaustion** is an allowed outcome, not a quirk. A failed allocation, and a request that
  is too large (more than 2^37 − 32 octets), count as heap exhaustion. T1 carries it as the
  `ExhaustsHeap` disjunct, and T2 as "some n".
- **T1 excludes `RandomStorageRefine`** (`hrsr`). Modelling `SmallRng` comes later.
- **T2 assumes `ValuesFit`** (`hvals`): storage values, preimages and encoded inputs are shorter
  than 2^64 octets.
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
- **Usage limits.** Keep the number of parallel sessions small, at most 3. Restart sessions fresh,
  with a handoff note, before their context gets large: the cost of each turn grows with context.
