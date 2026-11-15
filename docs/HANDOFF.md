# Handoff: coordinator state (2026-11-15, ~19:40 UTC)

The project resumed on 2026-11-15 after the 2026-11-14 pause. A coordinator (parent) session runs
up to 7 child sessions, all tagged `jam-lean`. Each line of work keeps its own handoff README in
the repo; read it before resuming that line. This file is the coordinator's state: if the
coordinator restarts, start here.

## Where things stand

- **T1 (refine ≡ Spec.refine).** `refine_milestone` (M1: 1–127 fixed-width or Export instructions)
  is PR **#197**, in CI. It doesn't include the `FmtRO` conjunct yet: that is a small follow-up once
  **#188** (fmt, which adds `Fmt/FmtRO.lean`) is on main. The T1 child merges #197 on green, after
  confirming that CheckAxioms printed `refine_milestone` with only the three axioms.
- **T2 (accumulate ≡ Spec.accumulate).** On main: the Impl framework, the input decode, the
  allocator/heap pieces, the storage wrappers (#166), `get_huge` and ValuesFit < 2^63 (#198), and the
  CodeA range for 51243 (#186). In flight:
  - T2 inputs (on_transfer composition);
  - Handlers A (recent-work ring, results store, Q18).
- **Symbolic executor.** On main: the core. In flight:
  - **#192**: KeyFmt and executor extensions (core change);
  - **#194** (draft, based on #192): path facts, forking, loop induction (`fork_sound`,
    `loop_sound(X)`, `loop_fork_sound(X)`), signed branches and sum facts.
  - `from_utf8` (60681): every piece is proved on `claude/symexec-loops`; the final theorem is being
    assembled.
- **Model fixes from the jam-lean-target fuzzing project:**
  - merged: #195 (lookup anchor uses `lookupAnchorStateRoot`, eq. 11.36) and #196 (context strings
    drop the leading `$`);
  - **#201** (Ψ_H fast path, csimp, 33× on the fuzzer's slow case);
  - **#204** (growHeapCore and Blake2b fast paths, based on #201, about 2× more).
- **Build and CI:**
  - **#193**: auto-resume of timed-out builds, plus a rolling public `lake-cache` prerelease and
    `scripts/fetch-lake.sh`;
  - **#202** (based on #193): CI split into a fast model job and a proofs job, which runs only when
    Services is affected;
  - **#205**: append-only code-fact tiers (P1);
  - profiling proposal merged as `docs/profiling/proposal.md` (#203).

## Merge order and rules

- **Merge on green, independently:** #188, #200, #201 (then #204), #205.
  - #200 and #201 don't force re-syncs under the re-sync rule, so they aren't batched.
  - #201 is merged by build infra.
  - #204 is merged by the perf child once #201 is in.
  - #205 is merged by the build-items child.
- **#193 → #202:** build infra reports green. The coordinator checks and OKs each merge, since both
  change the workflow.
- **#197 (T1) → #192 → #194.** These are executor-core changes, ordered so T1 rebuilds only once.
  - Before merging #192 and #194, re-sync them with main: #186 regenerated CodeA, and ProgAll
    imports the aggregate code modules.
  - Check that #194's CI completes, for downstream breakage.
- **When #188 merges:** tell the T1 child (FmtRO conjunct follow-up).
- **Once the lake-cache release exists** (after #193 plus a green main run):
  - sessions with 1.5 h or more of local build left switch to `scripts/fetch-lake.sh`;
  - then offer Adam a cloud-environment setup script (toolchain plus fetch-lake). It needs his
    approval.
- **Messaging rule (Adam, 2026-11-15):** children message the coordinator only when they open a PR,
  merge one, are blocked, need a decision, finish, or need a restart. Progress goes in READMEs.

## Children (as of this writing)

| Line | Session | Branch / PR | Next |
|---|---|---|---|
| T1 milestone | session_01FAPLsbkPzH8Yfj9VvZFM17 | #197 (from `claude/bootstrap-t1-exec-wip`) | merge on green; FmtRO follow-up after #188 |
| Executor (5th) | session_01FAPLsaSYRainAkdWH9CyDX | `claude/symexec-loops` (#194), `claude/keyfmt` (#192) | final from_utf8 theorem, then CodeF callers |
| Build infra | session_01FAPLscWuAjJ7U2ts3omA2r | #193, #202, #201 | report #193/#202 green, merge #201 |
| T2 Handlers A | session_01FAPLsZtzcvVn77qCM2yZKp | `claude/bootstrap-t2-handlers-a-wip` | Q18 spec PR, ResStore; merge #186's main |
| Build items P1/P3/P4 | session_01FAPLsbZuTvaqKJWtPwxEP7 | #205 | P3 module-system spike (report first), then P4 import trimming |
| Perf | session_01FAPLsaVzo2cgwafJUWm6CV | #204 | merge after #201 |
| T2 inputs | session_01FAPLsaRXf5F5n6msNwJKyg | `claude/bootstrap-t2-inputs-wip` | compose on_transfer |

**Queue for free slots:**
1. Vec / Decode (HeapHost): `claude/decode-heaphost`, `Services/Bootstrap/Decode/README.md`.
2. Field formatters: `claude/bootstrap-fields-wip`, `Services/Bootstrap/Fmt/FIELDS-HANDOFF.md`.
3. Storage-key stage 2, after T2's storage wrappers settle (`docs/storage-key-design.md`).

**jam-lean-target** (a separate project, the JAM conformance fuzzing target) has its own parent
session, session_01FAPLsdKXq86WuSpB5fCYVg. Adam allows the coordinator to message it. It reports
jam-lean bugs and perf requests, and it measures perf commits. Tell it when #201 and #204 merge, so it
can bump its pin.

## Adam's decisions on 2026-11-15

1. `remove` on a FULL result: the spec panics like the binary (quirk Q18).
2. Executor: extend it with forking and loop induction (done in #194).
3. CI continuation job: yes (#193).
4. ValuesFit is tightened to **< 2^63** octets: a length of 2^64−1 collides with NONE, and lengths
   from 2^63 up trap.
5. Up to **7** parallel sessions.
6. Build cache published as the public `lake-cache` prerelease (#193).
7. CI split (#202) ahead of the profiling work.
8. Lookup-anchor fix (#195) and `$` context-string fix (#196).
9. Storage keys: option (A) in stages (`docs/storage-key-design.md`).
   - Stage 1 is the accessors (#200).
   - Stage 2, the representation switch, comes after T2's wrappers settle.
   - The no-collision assumption is accepted; it is the paper's own. It appears only on the bridging
     theorem and is listed in whats-proven.md.
10. Profiling: P1, P3 and P4 go ahead. P6 (a bigger runner) and P2 (a code-fact re-layout) are
    revisited after #193/#202. P5 module splits are done later by the owning sessions.
11. Perf tasks for the fuzzer, csimp fast paths with no statement changes: #201 and #204.
12. Fmt failure disjunct strengthened: KeyFmt, LogFmt and the executor's fmt summaries say
    "Exhausts, and from there the run ends ☇ keeping (x, y)" (`ExhaustsP` on the T2 inputs branch).
    Proving it from the blob is a recorded obligation.

## Decisions the coordinator made (Adam may overturn)

- from_utf8: an all-inputs, frame-only theorem (c), plus an ASCII-only implication (b), under the
  logging decision. Its premises are calling-convention facts:
  - input readable, with p + len ≤ 2^32;
  - input and result disjoint from the 32-octet frame;
  - result and frame writable;
  - the [71078, +256) table readable;
  - strict address bounds.
  There is no table-contents hypothesis. The full UTF-8 spec is only for a caller that needs non-ASCII
  octets.
- Executor additions approved as additive, with no existing statement changed: `facts`, `validF`,
  `forkCheckW`, and the closed header `asm`.
- Storage keys: the four existing files are restated in stage 2, not now. An undecodable request
  reads as "absent".
- GenWitnessSteps imports narrowed to 8 JAM modules (output byte-identical), so the CI split can tell
  model-only PRs apart.

## Recorded obligations (not assumptions of the final theorems)

- **T1, allocation failure ends in ☇ with no exports.** Routes:
  - thread `ExhaustsT` through about 40 lemmas;
  - or a whole-program table of allocator return sites.
- **Fmt allocation failure ends in ☇** (`ExhaustsP`, decision 12). It shares the handle_alloc_error
  path with T1's obligation.
- **Step 10:** kernel-check the vendored blob, discharging `VendoredFacts`, `FmtRO` and the
  UTF8_CHAR_WIDTH readability.
- **T2, the output decode failure contract:** spec decode = none ⇒ the binary reaches 15361 or
  exhausts the heap.
- **Known looseness:** ArgOk/RefOk use a single C for the Ok bound and the Exhausts budget. It can be
  fixed additively (ArgOk2) with exact gas (T1′).
