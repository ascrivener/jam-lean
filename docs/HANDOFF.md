# Handoff: coordinator state (2026-11-16, ~09:30 UTC)

A coordinator (parent) session runs the child sessions, all tagged `jam-lean`. Each line of work keeps
its own handoff README; read it before resuming that line. This file is the coordinator's state: if
the coordinator restarts, start here. Scope since 2026-11-16: decision 19 below.

## Where things stand

- **T1 (refine).** On main: `refine_milestone` (#197, #207) and full M1 part A, refine for
  1 ≤ n ≤ 2^21 (#214). **#217** (parts B/C: variable-width DeleteItems/Imported, the eager Lookup
  step, the eight large `*_elem_bigC`) is in CI. On `claude/bootstrap-t1-m1d`: ReallocBig and the
  small-size C adapters. Remaining for `refine_t1c`: drop/EncOkMH arms for kinds 0, 11, 12, 13, 17,
  22, 24; threading realloc_call_big; the theorem.
- **T2 (accumulate).** On main: the Impl framework (#215 weakened its panic branch), wrappers, the
  handler pieces (#208), Q18 (#209). on_transfer is composed on `claude/bootstrap-t2-inputs-wip` (PR
  next). Handlers A: row 8 nearly done (slot write and counter get left), then rows 9 and 11.
- **Executor.** #192 merged. **#194** (forking, loops, from_utf8) fails to build against main (a
  `facts` field missing in `SymExec/Hosts.lean`); the executor session is fixing it.
- **Field formatters.** #213 (FieldInt) and #216 (write_str_heap) merged. Open PRs for N56*, the hex
  path and step-8 formatters come next; then the line pauses (decision 19).
- **Build and CI.** On main: auto-resume and `lake-cache` (#193, #211), the CI split (#202),
  code-fact tiers (#205), the perf fast paths (#204, incl. #201). New jam-lean cloud sessions fetch
  the cache via the environment's setup script. Next, in order: CodeF regeneration, P3 stage 1 (PVM
  and JAM as modules), the post_simp tactic pass (3–5× faster Decode proofs). Branches are listed in
  `docs/profiling/STATE-build-items.md` (on `claude/build-items-state`).

## Merge rules

- Each child merges its own PR on green, except #194, which the coordinator merges.
- Code-fact regenerations are sequenced by the coordinator (re-sync rule). New facts go in as tiers.
- After P3 stage 1 lands, every new PVM/JAM file needs the module header (`docs/module-system.md`).
- Whoever restarts `claude/decode-heaphost` must merge main and resolve the Decode/README.md add/add
  and the OkFD change from #214.
- Messaging rule (Adam, 2026-11-15): children message the coordinator only when they open or merge a
  PR, are blocked, need a decision, finish, or need a restart. Progress goes in READMEs.

## Children (as of this writing)

| Line | Session | Branch / PR | Next |
|---|---|---|---|
| T1 (6th) | session_01FAPLsZnE5YLqLpAmNt6jeJ | #217, `claude/bootstrap-t1-m1d` | merge #217; arms; refine_t1c |
| T2 Handlers A (5th) | session_01FAPLsdzswtDsCsKWorttaw | `claude/bootstrap-t2-handlers-a-wip` | finish row 8 (decisions 17, 18); rows 9, 11 |
| T2 inputs (3rd) | session_01FAPLsZyRGnqCpa8xKzDWWE | `claude/bootstrap-t2-inputs-wip` | on_transfer PR; ParamStatics prologue |
| Executor (6th) | session_01FAPLse7sPN4yxBDE4BaFtJ | #194 | fix and push #194, then pause |
| Field formatters (4th) | session_01FAPLsc3qjhviw4J2ADvaut | `claude/bootstrap-fields-3-wip` | open and merge its PRs, then pause |
| Build items (2nd) | session_01FAPLscnMqhsrcx7QX51DiF | `claude/codef-regen` etc. | CodeF, P3 stage 1, post_simp, then stop |

Paused lines with handoffs: Decode/HeapHost (`claude/decode-heaphost`), storage-key stage 2
(`docs/storage-key-design.md`). **jam-lean-target** (a separate project) has its own parent,
session_01FAPLsdKXq86WuSpB5fCYVg; it is pinned at or after 208cc20.

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
15. Critical-path build work after the P3 conversion. No bigger CI runner for now (cost estimate in
    `docs/BUILD-INFRA.md`).

## Adam's decisions on 2026-11-16

16. `refine_t1c` assumes every preimage an eager Lookup finds is shorter than 2^63 octets (a named
    hypothesis, like ValuesFit). The binary panics from 2^63 on; noted in upstream-candidates.
17. Row 8's premise is `ParamStatics μ C I ∧ 0 < 2·C·I < 2^32`, a named hypothesis on the chain
    parameters (an assumption of T2 unless discharged from the fetched parameters).
18. The recent-work counter's u32 wrap is a new spec quirk: `fixed 4 (((c + 1) % 2^32) % maxRecent)`.
19. **Narrowed scope.** Finish `refine_t1c` (full M1, with named hypotheses) and a T2 statement with
    named hypotheses. Deferred: discharging the Fmt hypotheses (the field-formatter line wraps up after
    its open PRs), the allocation-failure ☇ table, step 10, M2 (the real decoder), the from_utf8 step
    bound and CodeF callers, and further build work after the CodeF regen, P3 stage 1 and the
    post_simp pass. At most 4 working sessions.

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
- Impl's none branch keeps only y on ☇ (#215): on panic Ψ_A keeps the checkpoint, so x needn't be
  unchanged. The final T2 statement is unchanged.
- get_call / get_some gain frame conclusions (Glob statics, memory below 196608), additively.
- Weakenings in other areas' files: OkFD drops `es.length < 128` (#214).
- `refine_t1c`: a new theorem in T1's match form; `refine_milestone` unchanged. `VendoredFactsC` =
  VendoredFacts plus the 96-octet 4046 table (step 10). DRm widened and LookupFmtOk, as named Fmt
  hypotheses. The gas cap and the n ≤ 2^21 / capBound bounds stay internal; `ReallocBig` is a new
  file. Code-fact tier T1B (29181–29675), append-only.
- Field formatters: new files only; the RO slices they read are named RO hypotheses on their lemmas
  (FmtRO unchanged).
- Restart threshold about 400k tokens. A session being replaced is interrupted first.
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
- **T2, row 8:** `0 < 2·C·I < 2^32` from the fetched parameters (decision 17).
- **ReallocBig:** the single value units = 2^25 − 1 (two routes in the Refine README).
- **from_utf8 at 55106:** Ok ⇒ well-formed UTF-8, if that Debug site's hypothesis is to be discharged.
- **Known looseness:** ArgOk/RefOk use a single C for the Ok bound and the Exhausts budget. It can be
  fixed additively (ArgOk2) with exact gas (T1′).
