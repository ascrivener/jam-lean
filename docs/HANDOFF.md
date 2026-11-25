# Handoff: coordinator state (2026-11-20)

A coordinator (parent) session runs the child sessions, all tagged `jam-lean`. Each line of work keeps
its own handoff README; read it before resuming that line. This file is the coordinator's state: if
the coordinator restarts, start here. Scope since 2026-11-16: decision 19, refined by 20–26 below.
Since 2026-11-20 jam-lean is run by the parent session of the `witness-toaster` project; the old
jam-lean parent session is archived.

## 2026-11-25: GP v0.8.1 (read first)

- **Ownership:** session_01FAPLsdKXq86WuSpB5fCYVg is the single parent for jam-lean, jam-lean-target
  and jam. All its children from 2026-11-25 are archived; nothing is in flight.
- **The model is GP v0.8.1 on `main`** (#261, `58d1b86`). The last v0.8.0 model is tagged `gp-v0.8.0`
  (`5055102`). Plan, hunk coverage, decisions and the checks suspended until v0.8.1 vectors exist:
  `docs/gp-v0.8.1-migration.md`.
- **Moved in from jam-lean-target:** `JamCrypto` (#249; v0.8.1 path reads the VRF spec's prose by
  default, vector reading as a switch, #260) and the state decoder `JAM/StateDecode.lean` (#247).
- **Adam's decisions (2026-11-25):** N(o) post-state = input state (raised as graypaper#592);
  Thin signature O‖R‖s (confirmed by davxy on graypaper#593); `psiA_confined` gains `NoSupervisee`;
  crypto prose default (v0.8.1 path only); proofs CI on demand only; Services proofs not migrated
  (option 2, last kernel-checked `c22c197`); jam-lean-target stays a separate repository, with the
  pin-bump rule in `CLAUDE.md`.
- **Open:** davxy's answers on the VRF ring label, Z_pad and "push R" (asked privately); v0.8.1
  test vectors and the 0.8.1 fuzzer (restore suspended checks then); graypaper#592; proof work
  (restate Services through the accessors, then a manual proofs run on main).

## Where things stand

**Storage-key stage 2 (2026-11-25, branch `claude/storage-key-stage2`).** The model now holds
storage and requests in one `entries` dictionary keyed by state-key hash, with a_o and a_i carried
(`docs/storage-key-design.md`, Status). Model and tests only (Adam's "option 2"): the `Services/`
proofs no longer build and were last kernel-checked at `c22c197` (#241). `Services` is no longer a
default `lake build` target; the manual proofs run builds `PVM JAM Services` and will fail until
proof work resumes. **First task when proof work resumes:** restate `ASemLemmas.lean` and the
`Acc/` files that read `.storage` through the accessors, then a manual proofs run on main.

Both targets of the narrowed scope (decision 19) are proved and on main, with named hypotheses.

- **T1: `refine_t1c`** (`Services/Bootstrap/Refine/T1c.lean`, #229). For the Bootstrap binary and
  every canonical payload of at least one instruction with no Import (decisions 20, 21) and no
  RandomStorageRefine (`hrsr`), with constants `Consts.ofParams Params.full rk` (decision 25): refine
  ends `ok (out, ex)` matching `Spec.refine`, or out of gas with no exports, or `ExhaustsHeap`.
  Hypotheses: `VendoredFactsC`, `FmtHypsC` (at gas cap 2^62), `IsBootstrapC`, `hnoimport`, `hrsr`,
  `hpre` (preimages < 2^63, decision 16), shape and range premises. For the deployed binary,
  `Vendored.refine_t1c_deployed` (#239) drops `VendoredFactsC` and `IsBootstrapC` (kernel-proved).
- **T2: `accumulate_spec`** (`Services/Bootstrap/Acc/Final/Spec.lean`, #231, #233, #234). For any
  bootstrap code, ≤ 89 inputs each `InputSized`, t, s < 2^32 and constants with
  `maxRecent = 2·341·16`: Ψ_A's (state, transfers, yield, provisions) equals the outcome of
  `Spec.accumulate` run for some n steps, unless the binary runs out of gas or aborts at an
  allocation failure (`AccAbort`: a heap trap pc, or 40611/40821 with ω₇ = 0). Hypotheses:
  - `AccVendoredFacts` (vendored blob) and `IsBootstrapCode` (accepted by the coordinator under the
    standing named-hypothesis decision); both kernel-proved for the deployed binary in step 10 (#239),
    and `Vendored.accumulate_spec_deployed` states T2 for `deployedCode` without them;
  - `AccHyps B C` (option B, decision 23): AccLogFail, Utf8Call, LogFmt, KeyFmt,
    ItemLogFmt, OutDecH, InstrLogH, ResultLogH, HandlerH (Ab = AccAbort), PushH, ExtendH, OkEncH,
    DropInstrsH, over an `InstrRep` bundle;
  - `ValuesFit` (decision 4), `InfoFits` (decision 26), G3 (≤ 89 inputs, `InputSized`).
  Discharged inside: ParamStatics and RingFits (from the prologue), StoreFit, the own account, and
  `InputsGlob` (#236, merged 2026-11-18: inputs_decode keeps the Glob statics).
- **In flight.** No proof work. #223 (CodeF regeneration, with CI diffing every code-fact tier)
  merged 2026-11-17. Small maintenance PRs from the witness-toaster project (CI sync check for the
  symbolic executor's `Prog` modules, these docs) may be open.
- **Step 10: done** (#239, `Services/Bootstrap/Vendored/`). The kernel checks the vendored blob
  (`layout_ok`, `heap_ok`, every read-only slice), proving `VendoredFacts` (with `FmtRO`),
  `VendoredFactsC`, `AccVendoredFacts`, `IsBootstrapC Blob.preimage` and `IsBootstrapCode deployedCode`;
  corollaries `refine_t1c_deployed` and `accumulate_spec_deployed`. The memory-level `RO70824` / `RO70833`
  and the UTF-8 table's readability stay with the field-formatter / from_utf8 lines; the blob's side of
  them is checked (`Vendored/FieldRO.lean`).
- **CI.** One check for branch protection: `proofs` (#232) passes exactly when the merge rule holds.
  Adam has added `proofs` as a required check on main. Main's runs are serialized (#225).
  A proofs build with a warm cache takes about 40 min to 2.5 h. Since 2026-11-25 the proofs run only
  on demand (Actions → CI → Run workflow); pushes and PRs run `model` only.
- **Not started, need Adam:** T1 Import and empty payloads, M2 (the real decoder), discharging the
  named hypotheses (Fmt sites, handlers), P3 stage 1 and post_simp (branches pushed).

## Merge rules

- Each child merges its own PR on green (`model` and `proofs`).
- Code-fact regenerations are sequenced by the coordinator (re-sync rule). New facts go in as tiers.
- Messaging rule (Adam, 2026-11-15): children message the coordinator only when they open or merge a
  PR, are blocked, need a decision, finish, or need a restart. Progress goes in READMEs.

## Children (as of this writing)

No jam-lean proof children are running. The T2 InputsGlob line finished with #236.

Paused lines (remote branches kept; do not delete them):

| Line | Branch(es) | Handoff |
|---|---|---|
| Field formatters | `claude/bootstrap-fields-3-wip`, `-2-alt`, `-2-wc`, `-2-wip`, `-wip` (`-1`, `-2`, `-hex`, `-n56`, `-step8` merged as #189, #213, #220, #219, #221) | `Services/Bootstrap/Fmt/FIELDS-HANDOFF.md` (newer copy on `-3-wip`) |
| Decode / HeapHost | `claude/decode-heaphost` | on the branch |
| Storage keys, stage 3 (optional bridging theorem) | none yet | `docs/storage-key-design.md` |
| P3 `module` conversion | `claude/p3-module-stage1`, `claude/p3-module-spike` | `docs/module-system.md` on stage1; `docs/profiling/proposal.md` |
| post_simp pass | `claude/post-simp-fast` | on the branch |

Open PRs as of 2026-11-20: none besides witness-toaster maintenance PRs. **jam-lean-target** (a
separate project) has its own parent.

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

## Adam's decisions on 2026-11-16 (continued) and 2026-11-17

20. `refine_t1c` excludes payloads containing Import, by a named hypothesis (`hnoimport`), like
    `hrsr`.
21. `refine_t1c` requires at least one instruction; empty payloads stay with `refine_milestone`.
22. KeyFmt, Utf8Call and LogFmt also say they keep 196616…196791 (the Glob statics), like decision 14.
23. **T2 option B:** a T2 statement soon, as a skeleton in which the handlers, output decode, results
    encoder and writer are named hypotheses (`AccHyps`).
24. At most **3** parallel working children. Restart at about 400k tokens.
25. `refine_t1c`'s constants are fixed to `Params.full`.
26. T2's three new named hypotheses (2026-11-17), all option A:
    - `InfoFits e s`: s's code hash in e is shorter than 2^64 − 73 octets (the SDK reads an info
      length ≥ 2^64 − 9 as an error code; implied by the paper's 32-octet hash);
    - `AccLogFail`: in the first accumulate log line (6501 → 6630), a failed allocation ends in
      `ExhaustsP`; the success branch is proved;
    - `InputsGlob`: inputs_decode (6630 → 6674) keeps the Glob octets. Temporary: discharged next
      by threading Glob through inputs_decode.

## Decisions the coordinator made since 2026-11-16 (Adam may overturn)

- T2: `AccVendoredFacts` (six RO slices and layoutOk) accepted under the standing named vendored-blob
  decision; `IsBootstrapCode` accepted as `IsBootstrap`'s T2 counterpart.
- T2 plan-B interfaces (`docs/t2-remaining.md`): the InstrRep bundle (with tag, notNone and
  footprint fields), ResultsOwn and DropInstrsH; ExtendH and OkEncH without length preconditions (a
  too-large result is heap exhaustion); hAbX requires ω₇ = 0; ItemsOwn proved via SlotsOwn.
- The `proofs` gate job (#232) as the single check branch protection requires.
- Merge order after the ruleset fix: #227, #225, #219–#222, #226, #228, #194, then #229, #230,
  #231, #233, #234; #223 (CodeF) last, per the re-sync rule.

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
- *(Done: **Step 10**, the vendored blob kernel-checked, #239. The memory-level RO and UTF-8
  readability premises stay with their lines.)*
- **T2, the output decode failure contract:** spec decode = none ⇒ the binary reaches 15361 or
  exhausts the heap.
- *(Done: **T2, `InputsGlob`** (decision 26), discharged in #236.)*
- *(Done in `accumulate_spec`: `ParamStatics` and row 8's `0 < 2·C·I < 2^32` are discharged from
  the prologue.)*
- **ReallocBig:** the single value units = 2^25 − 1 (two routes in the Refine README).
- **from_utf8 at 55106:** Ok ⇒ well-formed UTF-8, if that Debug site's hypothesis is to be discharged.
- **Known looseness:** ArgOk/RefOk use a single C for the Ok bound and the Exhausts budget. It can be
  fixed additively (ArgOk2) with exact gas (T1′).
