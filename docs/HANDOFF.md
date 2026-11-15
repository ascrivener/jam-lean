# Handoff: coordinator state (2026-11-15, ~21:25 UTC)

The project resumed on 2026-11-15 after the 2026-11-14 pause. A coordinator (parent) session runs
up to 7 child sessions, all tagged `jam-lean`. Each line of work keeps its own handoff README in
the repo; read it before resuming that line. This file is the coordinator's state: if the
coordinator restarts, start here.

## Where things stand

- **T1 (refine ≡ Spec.refine).** `refine_milestone` (M1: 1–127 fixed-width or Export instructions)
  is on main (#197). The `FmtRO` conjunct of `VendoredFacts` is **#207** (T1 child merges on green).
  #188 (fmt) is on main.
- **T2 (accumulate ≡ Spec.accumulate).** On main: the Impl framework, the input decode, the
  allocator/heap pieces, the storage wrappers (#166), `get_huge` and ValuesFit < 2^63 (#198), and the
  CodeA range for 51243 (#186). In flight:
  - T2 inputs (on_transfer composition: tr_w1, tr_w2 written against the strengthened KeyFmt);
  - Handlers A: **#208** (handler pieces) and **#209** (Q18), both merged by the coordinator on green;
    then rows 8, 9, 11. Row 8 takes the premise `ParamStatics μ C I` (see below).
- **Symbolic executor.** On main: the core. In flight:
  - **#192**: KeyFmt and executor extensions (core change);
  - **#194** (draft, based on #192): path facts, forking, loop induction (`fork_sound`,
    `loop_sound(X)`, `loop_fork_sound(X)`), signed branches and sum facts.
  - `from_utf8` (60681): `from_utf8_call` (all inputs, frame-only) and `from_utf8_ascii` are proved on
    #194 (`SymExec/Utf8Final.lean`). Next: the CodeF callers (57327, 57556, 57624, 55106).
- **Model fixes from the jam-lean-target fuzzing project:**
  - merged: #195 (lookup anchor uses `lookupAnchorStateRoot`, eq. 11.36) and #196 (context strings
    drop the leading `$`);
  - **#201** (Ψ_H fast path, csimp, 33× on the fuzzer's slow case);
  - **#204** (growHeapCore and Blake2b fast paths, based on #201, about 2× more).
- **Build and CI:**
  - #193 is on main (auto-resume, the rolling public `lake-cache` prerelease, `scripts/fetch-lake.sh`).
    The first publish comes from main's first green run with it; build infra checks it and tests
    fetch-lake.sh on a fresh checkout;
  - **#202** (based on #193): CI split into a fast model job and a proofs job, which runs only when
    Services is affected;
  - **#205**: append-only code-fact tiers (P1);
  - profiling proposal merged as `docs/profiling/proposal.md` (#203); per-module build times for all
    1305 modules on `claude/profiling-data` (`docs/profiling/build-times.tsv`);
  - **P3 `module` conversion** (decision 13), by the build-items child:
    - stage 1 is PVM and JAM minus `PVM/SymExec` and `PVM.lean`, after #200, #201 and #204 merge;
    - stage 2 is SymExec and `PVM.lean`, after #192 and #194;
    - from stage 1 on, every new PVM/JAM file needs the module header (`docs/module-system.md`);
    - P4 import trimming comes after the conversion of the same files.

## Merge order and rules

- **Merge on green, independently:** #200, #201 (then #204), #205, #207, #208, #209.
  - #200 and #201 don't force re-syncs under the re-sync rule, so they aren't batched.
  - #201 is merged by build infra.
  - #204 is merged by the perf child once #201 is in.
  - #205 is merged by the build-items child; #207 by the T1 child.
  - #200, #208 and #209 are merged by the coordinator.
- **#202** (CI split, now based on main): build infra reports green, and the coordinator checks and
  OKs the merge, since it changes the workflow.
- **#192 → #194** (executor core; #197 is in). The executor child syncs #192 with main and merges it
  on green, then syncs #194 and marks it ready once green; the coordinator merges #194.
- **Once the lake-cache release exists** (after #193 plus a green main run):
  - sessions with 1.5 h or more of local build left switch to `scripts/fetch-lake.sh`;
  - then offer Adam a cloud-environment setup script (toolchain plus fetch-lake). It needs his
    approval.
- **Messaging rule (Adam, 2026-11-15):** children message the coordinator only when they open a PR,
  merge one, are blocked, need a decision, finish, or need a restart. Progress goes in READMEs.

## Children (as of this writing)

| Line | Session | Branch / PR | Next |
|---|---|---|---|
| T1 milestone | session_01FAPLsbkPzH8Yfj9VvZFM17 | #207 | merge #207 on green |
| Executor (5th) | session_01FAPLsaSYRainAkdWH9CyDX | `claude/keyfmt` (#192), `claude/symexec-loops` (#194) | sync and merge #192, sync #194, then hand off; a fresh session takes the CodeF callers |
| Build infra | session_01FAPLscWuAjJ7U2ts3omA2r | #201, #202 | merge #201, report #202 green, check the first lake-cache publish |
| T2 Handlers A (2) | session_01FAPLsZjqCgY6yAeJE4cPXV | `claude/bootstrap-t2-handlers-a-wip` | rows 8, 9, 11 |
| Build items P1/P3/P4 | session_01FAPLsbZuTvaqKJWtPwxEP7 | #205, P3 stages | P3 stage 1 after #200/#201/#204 |
| Perf | session_01FAPLsaVzo2cgwafJUWm6CV | #204 | merge after #201 |
| T2 inputs (2) | session_01FAPLsc8QZw3s37mRnjAqya | `claude/bootstrap-t2-inputs-wip` | on_transfer (tr_w1, tr_w2), then the prologue's `ParamStatics` |

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

13. P3 `module` conversion: go ahead with PVM and JAM (staged); Services and the generators later, by
    their owning sessions.
14. KeyFmt strengthened: its success case says the key text lies in a live, freshly allocated chunk's
    data (`∃ ch ∈ chunks s', ch.used ∧ ch.addr + 32 = kp ∧ fresh ∧ ∀ a ∈ [kp, kp+len), InDataA ch a`);
    the `kc = 0` disjunct is dropped. The executor discharges this version.

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
- from_utf8 premises also include input length < 2^32 (a premise of a new theorem only).
- The byte-slice Debug site at 55106 gets its own named Fmt log-site hypothesis (standing decision on
  named log-site hypotheses), added only when a caller theorem needs it. "Ok ⇒ well-formed UTF-8"
  (spec (a)) is a recorded obligation, not started.
- Row 8 (Handlers A) takes `ParamStatics μ C I` ([196616]₂ = C, [196696]₈ = I) as a premise; later
  summaries' frames keep 196616…196791. The T2-inputs session proves the prologue's `apply()` stores
  (56205, 56279; needs a CodeA range, sequenced by the coordinator).
- P3 split into two stages, stage 1 after #200/#201/#204 (they force a cold rebuild anyway).
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
- **T2, `ParamStatics`:** the prologue's `apply()` stores C and I, and later steps keep them.
- **from_utf8 at 55106:** Ok ⇒ well-formed UTF-8, if that Debug site's hypothesis is to be discharged.
- **Known looseness:** ArgOk/RefOk use a single C for the Ok bound and the Exhausts budget. It can be
  fixed additively (ArgOk2) with exact gas (T1′).
