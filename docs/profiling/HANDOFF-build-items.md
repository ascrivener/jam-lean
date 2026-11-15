# Handoff: build items P1, P3, P4 (Adam's decision of 2026-11-15)

The proposal is `docs/profiling/proposal.md` (PR #203). Adam approved P1, P3 and P4, in that order,
as separate PRs. Each may be merged by its session on green CI if it is build-only and does exactly
what is described here. P2 and P6 are deferred until #193/#202 have run for a while. P5 is not
planned now; the owning sessions split their own files later.

## P1: append-only code-fact tiers (the mechanism only)

**Goal.** A session can add code facts without regenerating `CodeA`, `CodeX`, `CodeF` or `CodeR`:
- the facts go in a new tier module with its own class and kernel check;
- only the modules that import the new tier rebuild.

**Constraints.**
- Do not convert the existing tiers.
- Do not touch #186, which is in CI.
- Tell @parent when the mechanism is ready, so that the Acc, Refine and Fmt sessions can adopt it.

**What exists.** Everything is in `Tests/GenWitnessSteps.lean` (about 3250 lines):
- The service config fields are `fnRanges`, `fnRangesX`, `jumpRangesX`, `fnRangesA`, `fnRangesF` and
  `fnRangesR` (~l.94–113). Bootstrap's values are at ~l.214–245.
- Mode dispatch is at ~l.1134–1150:
  - `codef`, `coder` and `codea` all set `amode`; every `amode` also sets `xmode`;
  - `E` ∈ {X, A, F, R} picks the module name `Code{E}` and the class `HasCode{E}`;
  - `extFacts` (~l.1234) emits only the facts that the earlier tiers lack.
- What each tier excludes is hard-coded per mode:
  - `CodeA` excludes `Code` and `CodeX`;
  - `CodeF` excludes `Code` and `CodeA`, and its users never assume `HasCodeX`;
  - `CodeR` excludes `Code` and `CodeX`.
- The output of each tier is:
  - `Code{E}.lean`, holding the facts, `HasCode{E}` and the `@[pvm_code]` lemmas;
  - lemma slices `Code{E}/L*.lean`, 400 lemmas each (~l.1907), and the umbrella `Code{E}All.lean`;
  - kernel-check groups `Code{E}Check/G*.lean`;
  - `Code{E}Ok.lean`, holding `hasCode{E} : CodeOk … Code.facts P → HasCode{E} …`. This discharge
    is why a tier adds no assumption to headline theorems.
- `CLAUDE.md`'s CI section and `ci.yml` re-check the generated files. Find where the generated-file
  check lists the modes, and add the new tier there.

**Suggested design.**
- A generic tier: `lake exe genwitnesssteps --service bootstrap tier <Name> <base-tiers…> <steps>`.
  Its ranges come from a new config field, for example `tiers : List (String × List (Nat × Nat) × List String)`
  giving the name, the ranges and the tiers it excludes.
- It emits `Code<Name>*` the way the existing tiers do, and reuses the `E` machinery with `E := Name`.
- Write a short doc for sessions, either in `docs/` or as a section in `CLAUDE.md` (ask @parent
  which):
  - how to add facts: append a range to a new tier, never to an existing one, and never regenerate
    an existing tier just to add facts;
  - how to import the new tier;
  - when to fold tiers back together: only during a planned cold rebuild.
- To test, generate a small dummy tier and check that it builds and that its `…Ok` holds. Don't
  commit the dummy unless @parent wants an example.

## P3: module-system spike (about half a day, throwaway branch)

**Question.** On Lean v4.36.0-rc1, can a proof-only edit to a `module`-system file skip rebuilding
the modules downstream of it? And what breaks with `decide`, `simp` unfolding and reflection
(SymExec `check_sound`, code-fact `checkCode`) when definition bodies are not exposed?

**Method.**
1. Convert a single leaf-ish hub plus one consumer, for example `Services/Bootstrap/Alloc/Rep.lean`
   and a direct importer, to `module` with `public import`.
2. Build them, edit a proof body, rebuild, and see whether Lake recompiles the consumer (`lake build -v`
   shows it).
3. Also try one module that uses `decide` or reflection.

Report to @parent before changing anything outside the throwaway branch.

## P4: trim imports (build-confirmed, in batches)

**Scope.** Stay out of `Services/Bootstrap/Acc/`, `Refine/`, `PVM/SymExec/` and `Fmt/`; ask @parent
before touching them. The targets are:
- the linear Alloc chain (`Alloc/Rep` → `Arith` → `Writable` → `Register` → `FreeNext` → … →
  `AllocWrap` → `ReallocEntry`);
- `Reader`, `ReaderBig`, `Memcpy`, `MemcpyBig`, `DecodeU16`, `DecodeU32` and `Decode/Tag`.

**Candidates.**
- `proposal.md` explains the heuristic. Rerun it with
  `scripts/import-graph.py` (branch `claude/profiling-data`) plus a name check: a direct import whose
  declared names the importer never mentions.
- About 201 hits in `Services/**`. Examples: `AllocFind`←`AllocPro`, `AllocSplit`←`AllocSearch`,
  `MemcpyBig`←`DecodeU16`, `Alloc.Rep`←`Picoalloc.Init`, `Alloc.Register`←`PVM.Logic.Go`.
- Simp sets and instances are used without being named, so expect false positives.

**Method.**
1. Get a warm `.lake`. Once #193 has merged and published the `lake-cache` release, use
   `scripts/fetch-lake.sh`. A cold build takes about 5 h.
2. For each candidate, replace the import with whatever the module still needs from that import's
   ancestors, then build that one module. Check exit codes, because elaboration can die silently.
3. Batch the confirmed removals into PRs.
4. Each PR changes imports only. It must leave a chain's downstream modules importing what they use.
   The full build in CI is the final check.
