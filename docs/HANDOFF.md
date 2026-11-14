# Handoff: state of work at the pause (2026-11-14)

All work was paused on 2026-11-14 at about 12:10 UTC, to move to another account. Every line of
work below has its branch pushed and a handoff README in the repo; read that README before
resuming. "Not built" means a local build was stopped by the pause: rebuild before trusting it.

## Where things stand

- **T1 (refine ≡ Spec.refine).** The interim milestone `refine_milestone` is proved on T1's wip
  branch, with no sorry and clean axioms. It is not on `main` yet. It covers:
  - payloads of 1 to 127 fixed-width or Export instructions;
  - |payload| + 48 ≤ 2^24 (implied by the paper's W_B).
  Its named hypotheses are `VendoredFacts` (now including `FmtRO`) and `FmtHyps` (three log
  sites). Its heap-exhaustion case is `ExhaustsHeap` alone: "it then traps with no exports" is a
  recorded later obligation.
- **T2 (accumulate ≡ Spec.accumulate).** On `main`:
  - the Impl framework (`psiA_of_impl`, #158);
  - the input decode (#152);
  - the allocator and heap-context pieces (#150, #169).
  In flight:
  - the storage wrappers (#166);
  - the items loop and `on_transfer` (T2 inputs' wip);
  - the recent-work ring and results store (Handlers A's wip);
  - accumulate's output decode at 7073 (the Vec session's HeapHost generalisation).
- **The symbolic executor** is on `main` and in use. KeyFmt (`"transfer{n}"`) is proved on a wip
  branch.

## Open PRs, and the order to merge them

| PR | What | State at pause | Action |
|---|---|---|---|
| #166 | T2 storage wrappers | CI running | Merge on green. Then #186 may go. |
| #186 | CodeA range for 51243 (regenerates CodeA) | green | Only **after #166**: re-sync with main, then merge. |
| #182 | loopAFC (Vec) | CI running | Merge on green. T1's milestone PR depends on it. |
| #179 | T1 CodeX 3716–3790 | CI running (re-synced) | Merge on green. |
| #188 | fmt: 6159 builders and arms 15/16/20/23 | CI running, **stale** | Re-sync with main first (#187 changed Template/ResultDebug), rebuild, merge. |
| #189 | field formatters: ref_bool_ok, ref_u8x32_ok | CI running | Merge on green. |

Next PRs to open, from wip branches:
- **T1 milestone:** after #182 merges.
- **KeyFmt and the executor:** this changes the executor core, so check which open PRs it forces
  to re-sync.
- **fmt:** `write_str_heap` and `FmtRO`.

## Lines of work

| Line | Branch @ commit | Handoff | State |
|---|---|---|---|
| T1 top level | `claude/bootstrap-t1-exec-wip` @ 7632cf3 | `Services/Bootstrap/Refine/README.md` ("PAUSED 2026-11-14") | `refine_milestone` builds, with `S0 + 7560 ≤ M` and the read-only premise in the three Fmt hypotheses. To do: re-run `#print axioms refine_milestone`; add the `FmtRO vb.ro.toList` conjunct to `VendoredFacts` once fmt's FmtRO PR lands; open the milestone PR after #182. |
| T2 inputs | `claude/bootstrap-t2-inputs-wip` @ ec034c3 | `Services/Bootstrap/Acc/README.md` ("Handoff: T2 inputs…") | Items loop and `on_transfer`. Main merged in; **33 modules not rebuilt**. |
| T2 handlers A | `claude/bootstrap-t2-handlers-a-wip` @ f9b29af | `Services/Bootstrap/Acc/Handlers/README.md` | `kb_call` (33843) and `kf_call` (51243) built. `ResStore.lean` (36170) is an unchecked draft. Row 8 needs #166. |
| Vec / Decode | `claude/decode-heaphost` @ 85782dd | `Services/Bootstrap/Decode/README.md` | Generalising Decode in place to HeapHost (refine statements unchanged); **not built**. Then Encode G names for Handlers A, then 7073. |
| fmt (6159) | `claude/bootstrap-fmt-sink-heap` @ dec3f90, `claude/bootstrap-fmt-ro` @ 8c2561d, `claude/bootstrap-fmt-6` (#188) | `Services/Bootstrap/Fmt/README.md` ("Handoff") | Next: 29675 (Vec<Instruction> Debug), then `refine_debug_line`. The 8 remaining arms wait on the field formatters. |
| Field formatters | `claude/bootstrap-fields-wip` @ ae682db | `Services/Bootstrap/Fmt/FIELDS-HANDOFF.md` | `FieldInt.lean` and `N56Steps.lean` **not built**. 56340/57485 estimated at ~7 days: the string path, then hex, then 57485. |
| Executor / KeyFmt | `claude/fmt-text-wip` @ 59986bd | `Services/Bootstrap/SymExec/README.md` | Full build stopped at 2164/2596 with 0 errors. Next: full build, then a PR flagged "executor core changed". |

## Open questions for Adam

1. **`remove` on a FULL result.** Either (a) the spec panics like the binary, recorded as quirk
   Q18 (recommended), or (b) it becomes a named reason in T2 for stopping early.
2. **Loops in the symbolic executor.** Either (a) extend the executor with forking and loop
   induction, about 2–3 days and reusable (recommended), or (b) prove `from_utf8` by hand, about
   2–4 days. The field formatters' loops would benefit too.
3. **CI continuation job.** Should a second job automatically resume a build that hit the 290-min
   limit from the cache, so nobody has to re-run it by hand?

## Recorded obligations (not assumptions of the final theorems)

- **T1, allocation failure ends in ☇ with no exports.** Two routes:
  - thread `ExhaustsT` through about 40 lemmas, about 1–2 session-days;
  - a whole-program table of allocator return sites (to be scoped).
- **Step 10:** kernel-check the vendored blob, discharging `VendoredFacts` and `FmtRO`.
- **T2, the output decode failure contract:** spec decode = none ⇒ the binary reaches 15361 or
  exhausts the heap. Until it's proved, the operand arm is a local premise and TODO.
- **Known looseness:** ArgOk/RefOk use a single C for the Ok bound and the Exhausts budget. It can
  be fixed additively (ArgOk2) when exact gas (T1′) is done.
