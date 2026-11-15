# Build-time profiling: analysis and ranked proposal

This is the analysis for task 3 of `docs/BUILD-INFRA.md`. It makes no restructuring changes. Adam
decides which of the proposals below go ahead. Every proposal changes the build only. None changes a
theorem statement. Where a proposal would change the hypotheses of *internal* lemmas, it says so.

## Data and method

- **Data.** The data are on branch `claude/profiling-data`, which is not yet on `main`:
  `docs/profiling/build-times.tsv`, `docs/profiling/README.md` and `scripts/import-graph.py`.
- **Times.** `build-times.tsv` (interim) holds 1082 of 1340 modules, from a cold local
  `lake build` on 4 shared cores (see `README.md`). The times are wall times while sharing the
  machine, not CPU costs.
  - The 258 missing modules are almost all in `Services/Bootstrap/{Decode,Encode,Alloc,Fmt,Refine,Acc}`.
  - I imputed each missing module as the median of the measured modules in its directory.
  - With imputation the serial total is **15.4 h**, against 10.0 h measured. Every
    "downstream minutes" figure below uses the imputed times.
  - Re-run the numbers when the complete TSV lands. I expect the ranking to hold, because the missing
    modules sit downstream of the hubs ranked here, so the hubs' costs can only grow.
- **Serial minutes and wall time.** A cold build is 15.4 serial hours and takes about 5 h on CI, so
  the build overlaps about 3 modules at a time. As a rule of thumb, divide serial minutes by about 3
  to get CI wall time. That ratio is lower for long linear chains, which cannot overlap.
- **Rebuild cost of a change** means the serial minutes of every module that depends on the changed
  module, directly or transitively. Lake rebuilds all of them, because a module's trace includes its
  imports' traces, and a proof-only edit changes the trace too.
- **What a typical PR costs** is measured by **replaying history**. For each of the last 87
  first-parent commits on `main`, I took the modules the commit touched, found everything downstream
  of them in today's import graph, and added up the serial minutes.
  - Median: **37 serial min**. Mean: **98 serial min**. Total over the 87 commits: 8560.
  - Over the last 42 commits: median 25, mean 66.
  - The mean is driven by a few heavy PRs, and those are what the proposals target.

## 1. Top modules

### By downstream rebuild cost (what changing them costs)

| module (family) | dependents | downstream serial min | own s | note |
|---|---:|---:|---:|---|
| `PVM.{Basic,Instr,Exec,…}`, `PVM.Logic.*`, `JAM.{Codec,Account,Accumulate,Refine,…}`, `JAM.Theorems.{HostGas,RefineContract,GrowHeap}` | 1190–1313 | 594–599 | ≤10 | model core; everything is downstream of it (near-full rebuild) |
| `Services.Bootstrap.Code` (8.4 MB, generated) | 1008 | 545 | 596 | the base code facts; 184 direct importers |
| `PVM.Logic.Chase`, `PVM.Logic.Words` | 630–697 | 400–415 | ≤4 | |
| `Services.Bootstrap.Memcpy`, `Reader`, `DecodeU32`, `DecodeU16`, `MemcpyBig`, `ReaderBig` | 221–267 | 400–467 | 41–312 | the bottom of the Bootstrap proof stack |
| `Services.Bootstrap.Alloc.*`: a linear chain of ~25 modules (`Rep` → `Arith` → … → `AllocWrap`) | 221–257 | 318–389 | 1–489 | each link has only 2 direct importers |
| `Services.Bootstrap.CodeA` (1.1 MB, generated) | 278 | 150 | 54 | 144 direct importers |
| `Services.Bootstrap.Blob` | 369 | 113 | 2 | |
| `PVM.SymExec.{Core,Sound,Check}` | 178–180 | 103 | 1–8 | a linear chain; consumers import `Cut` (86 direct importers) |
| `Services.Bootstrap.CodeAAll` (umbrella) | 116 | 100 | 1 | 30 direct importers; includes `SymExec.ProgAll` |
| `Services.Bootstrap.CodeF` / `CodeX` | 218 / 215 | 91 / 71 | 58 / 137 | |
| `Services.Bootstrap.Encode.Writer` … `Encode.Top` | 50–75 | 92–145 | | |

The `Services.lean` umbrella has no importers, so it costs nothing to rebuild. The aggregates that do
cost something are the generated `Code*All` umbrellas and `SymExec.ProgAll`.

### By own build time (measured)

| s | module | dependents |
|---:|---|---:|
| 2261 | `Services.Bootstrap.SymExec.ProgAll` (3.1 MB, generated) | 13 |
| 1021 | `Services.Bootstrap.Decode.Lookup` | 36 |
| 713 | `Services.Bootstrap.Acc.Inputs.CompactU64` | 19 |
| 706 | `Services.Bootstrap.Acc.Inputs.ItemOperand` | 19 |
| 705 | `Services.Bootstrap.Alloc.ReallocShrink` | 173 |
| 630 | `Services.Bootstrap.NoInstrArgs` | 6 |
| 596 | `Services.Bootstrap.Code` | 1008 |
| 594 | `Services.Bootstrap.Alloc.AllocAlignImpl` | 2 |
| 549 | `Services.Bootstrap.Refine.ArgsRun` | 3 |
| 506 | `Services.Bootstrap.Decode.Bless` | 17 |
| 489 | `Services.Bootstrap.Alloc.FreeNext` | 242 |
| 482 | `Services.Bootstrap.EmptyPayload` | 3 |
| 477 | `Services.Bootstrap.Encode.Dispatch` | 55 |
| 452 | `Services.Bootstrap.Fmt.LogSteps` | 12 |
| 443 | `Services.Bootstrap.Decode.HashU64` | 108 |

By directory, the largest own times are: `Decode` 79 min, `Alloc` 78, `Acc` 46, `SymExec` 44 (of
which `ProgAll` is 38), `Fmt` 40, and the `Code*Check` kernel checks 30–39 each.

### What drove the cost in history

Each commit is attributed to the touched module with the largest downstream cost.

| driver | all 87 commits | last 42 commits |
|---|---:|---:|
| code-fact regenerations (`Code`, `CodeA`, `CodeF`, `CodeR`, `CodeX`) | 35% | 30% |
| model core (`JAM.Theorems.RefineContract`, `PVM.CostExpr`: one commit each, ~920 min each) | 22% | 33% |
| `Bootstrap/Decode` hubs | 25% | 2% |
| `Bootstrap/Encode` hubs | 4% | 13% |
| `Bootstrap/Alloc` chain | 8% | <1% |
| `PVM/SymExec` | 6% | 9% |

**Code-fact regenerations are the largest recurring cost.**
- A regeneration costs 158 (`CodeF`), 270 (`CodeA`) or 320 (`CodeX`) serial minutes, which is
  roughly 1–2 h of CI wall time.
- The cost comes from the generator's layout, not from the size of the change. Facts are numbered by
  position (`facts_N`, `factGroup_k (n := i)`), so adding a single fact shifts the indices of every
  later fact. For example, #151, which added Assign's return path to `CodeA`, rewrote `CodeA.lean`
  (14k lines changed), every lemma slice `CodeA/L*.lean` and every check group `CodeACheck/G*.lean`.
  Everything that imports any of them then rebuilds.
- The open PR #186 shows the same thing again. It adds one 106-octet range, renumbers every `CodeA`
  slice, and needs a re-sync of every open PR that imports `CodeA`.

## 2. Proposed changes, ranked by expected saving per typical PR

The savings are in serial minutes, from the history replay; divide by about 3 for wall time. "Per
affected PR" is the saving on a PR of the kind the proposal targets. "Average" spreads that over the
last 87 PRs.

### P1. Append-only code-fact tiers (a policy plus a generator flag)

**What.** Never regenerate an existing code-fact module in order to add facts. New facts go in a new
tier module, for example `CodeA2` with `HasCodeA2`, and its own `CodeA2Check`.
- The repository already works this way across tiers (`Code`, `CodeA`, `CodeF`, `CodeR`, `CodeX`).
  P1 makes it the rule within a tier too.
- The generator gains an option to emit only the facts that no earlier tier already contains.
- Modules that need the new facts import the new tier. Nothing else rebuilds.

**Saving.**
- Per affected PR: a `CodeA` or `CodeX` addition drops from 270–320 serial min to roughly the new
  tier's own modules plus its consumers (≈20–60). `ProgAll` rebuilds only if the symbolic executor
  needs the new facts.
- Average: about 25–30 serial min per PR. Code-fact PRs made up 10 of the 87 commits and about 3000
  serial min between them.

**Effort.** Small: a generator option in `Tests/GenWitnessSteps.lean`, plus a note in `CLAUDE.md`.

**Risk.** Low.
- Each new tier is discharged by the kernel check, exactly as `hasCodeA` is today, so no headline
  theorem gains an assumption.
- Tiers accumulate. Fold them back into one module during a planned cold rebuild, for example
  together with P2.

**Touches.** The generator and new `Services/Bootstrap/Code*<n>` files. Whichever session adds facts
(Acc, Refine and Fmt work all do) uses the new tier.

### P2. Stable, address-sharded code-fact layout

**What.** Make the generator's output stable under insertion.
- Chunk the facts by fixed program-address buckets, or by function from `fnRanges`, rather than by
  position.
- Each bucket gets its own facts list, its own `HasCode·_k` class (with an instance
  `HasCode· → HasCode·_k`), its own lemma slice and its own check group.
- When facts are added or a step count changes, only the buckets whose facts changed are rewritten
  byte for byte. Lake then rebuilds only those buckets and their importers.
- Consumers import the buckets they use instead of `CodeAAll` or `CodeFAll`.

**Saving.**
- P1's saving, plus regenerations that *change* existing facts. For example, a change to the base
  `Code` step count (7463) would cost up to 545 serial min today.
- Unlike P1, it does this without tiers accumulating.
- `ProgAll` can be sharded the same way: a 38-minute single-threaded module becomes several smaller
  ones that can build in parallel.

**Effort.** Medium–large.
- Rewrite the generator for `code`, `codea`, `codef`, `coder`, `codex`, the `*check` variants, and
  `gen_prog.py`.
- Make one mechanical import-rewriting PR across about 500 importers. Most consumers use the facts
  through the `pvm_code` simp set, not by name, so their bucket imports must be derived from the
  address range each proof covers.

**Risk.** Medium.
- Internal lemmas that take `[HasCodeA p P]` would take bucket classes instead, or keep `HasCodeA`
  and rely on instance resolution. Headline theorems keep `HasCode`, so their statements do not
  change.
- `simp` sets that are split across buckets need care.
- It requires one cold rebuild.

**Touches.** Every `Services/Bootstrap/Code*` file, `Tests/GenWitnessSteps.lean`,
`PVM/SymExec/gen_prog.py`, `Services/Bootstrap/SymExec/Prog*.lean`, and the import lines of most of
`Services/Bootstrap/**`, including the active areas Acc, Refine and Fmt.

### P3. Spike: Lean's module system for proof-only rebuild avoidance

**What.** Lean core now has a module system (`module`, `public import`, `@[expose]`). Its stated aim
includes not rebuilding downstream modules when only private material, such as proof bodies, changes.
- **This is unverified on v4.36.0-rc1 and on this project.** There is no toolchain in this session.
- The spike would convert a single hub, for example `Services/Bootstrap/Alloc/Rep.lean` and one
  consumer, edit a proof body, and check whether Lake skips the consumer.

**Saving, if it works.**
- Most proof PRs edit proofs, not statements, inside hub modules.
- Recent examples: Encode hubs 92–145 serial min; Decode and Alloc hubs 240–390 serial min; edits to
  `PVM.SymExec.Sound` 103 serial min.
- These would shrink to the edited module and its direct users. This is potentially the largest
  saving for non-code-fact PRs.

**Effort.** A spike of one session. Converting hubs afterwards is incremental, one module at a time.

**Risk.** Medium–high.
- Definitions are not exposed by default, and the project relies on `decide`, `simp` unfolding and
  reflective checking (code facts, SymExec), which need definition bodies. Those modules would need
  `@[expose]` or would have to stay outside the module system.
- It is new tooling on a release-candidate toolchain.

**Touches.** Only the hub modules converted, one PR each.

### P4. De-serialise the Alloc chain and the bottom of the Bootstrap stack

**What.**
- `Services/Bootstrap/Alloc` is a linear import chain of about 25 modules: `Rep` → `Arith` → `Writable`
  → `Register` → `FreeNext` → … → `AllocWrap` → `ReallocEntry`. Each link has 221–257 dependents.
  The bottom modules `Reader`, `Memcpy`, `MemcpyBig`, `DecodeU16` and `DecodeU32` look the same.
- A name heuristic finds **201** direct imports in `Services/**` where the importer uses no name the
  imported module declares. Most of them are links in these chains:
  - `AllocFind` ← `AllocPro`;
  - `AllocSplit` ← `AllocSearch`;
  - `MemcpyBig` ← `DecodeU16`;
  - `Alloc.Rep` ← `Picoalloc.Init`;
  - `PVM.Logic.Go` ← `Alloc.Register`.
- Replace each such import with the narrower imports the module actually needs, so that each chain
  becomes a tree. Downstream modules would then import the 2–3 contract modules they use (for
  example `HeapContract`) rather than the whole chain.

**Saving.**
- An edit to the middle of the Alloc chain costs about 335 serial min today. As a tree it would cost
  only that branch: an estimated 50–150 serial min.
- Decode and Alloc drove 33% of the historical cost, but under 3% of the last 42 PRs, so the average
  saving *now* is small (≈5 serial min per PR). It matters again whenever T1 work returns to the
  allocator or the decoders.

**Effort.** Medium.
- The heuristic gives false positives: a simp set or an instance can be used without naming it. Each
  edge must therefore be checked by removing the import and building that one module, which is cheap
  with a warm cache.
- For chains that are real (where a module uses lemmas from its predecessor), there is a further,
  larger option: state the contract as a structure that downstream modules take as a hypothesis, and
  discharge it at the top. That would change internal lemma statements, so it needs a decision from
  Adam, and I don't recommend it before P3 has been tried.

**Risk.** Low for removing imports, since the build checks it.

**Touches.** `Services/Bootstrap/Alloc/*`, `Reader*.lean`, `Memcpy*.lean`, `DecodeU16/32.lean`,
`Decode/Tag.lean`, and the import lines of their direct importers. None of these is in an active
area.

### P5. Split the slowest single modules

**What.** Split modules over about 8 minutes so that they can build in parallel and so that an edit
recompiles less:
- `ProgAll` (38 min);
- `Decode.Lookup` (17 min);
- `Acc.Inputs.CompactU64` and `Acc.Inputs.ItemOperand` (12 min each);
- `Alloc.ReallocShrink`, `NoInstrArgs`, `Alloc.AllocAlignImpl`, `Refine.ArgsRun`.

**Saving.**
- On the wall time of PRs that rebuild them. `ProgAll` is downstream of every `CodeA`, `CodeX` and
  `PVM.SymExec` change, and as a 38-minute single-threaded tail it probably bounds those CI runs.
- The saving per touching PR is the module's own time minus its largest shard, for example about
  25 min of wall time for `ProgAll`.
- Small on average. Cold builds are limited by throughput, not by the critical path (see below), so
  P5 does little for them.

**Effort.** Small for hand-written modules (move lemmas into siblings). `ProgAll` is generated, so
splitting it is part of P2, or a small change to `gen_prog.py` on its own.

**Risk.** Low.

**Touches.** `Services/Bootstrap/SymExec/ProgAll.lean` and `gen_prog.py` (SymExec area);
`Acc/Inputs/*` (Acc area, which is active); `Refine/ArgsRun.lean` (Refine area, which is active);
`Decode/Lookup.lean`; `Alloc/*`.

### P6. A larger CI runner (not a code change; spends money, so Adam decides)

**What.** Use more cores on CI.
- A cold build is limited by throughput: 15.4 serial hours on about 3 effective cores.
- The critical path, estimated from the imputed times, is only about 1.5–2 h.
- 8 cores would roughly halve cold and near-full rebuilds, and 16 cores would cut them further, down
  towards the critical path. Memory has to scale with the cores (`pvm_go` is memory-hungry).

**Saving.** Applies to every PR and to every cold build, and is complementary to #193 and #202.

**Effort.** A change to the CI configuration. **Risk.** Cost only.

### P7. SymExec: separate definitions from lemmas (not recommended now)

**What.**
- `PVM.SymExec` is a chain: `Core` → `Sound` → `Check` → `Cut`. Consumers import `Cut`, and the
  generated `Prog` tables need `Check`, so they need `Sound`. Splitting definitions from lemmas
  therefore does not take `Sound` out of consumers' dependencies.
- The SymExec changes in history (spike, Phase 1, Phase 2, host effects) changed the executor's
  definitions, so a full downstream rebuild was genuine.

**What would help, cheaply.** A convention: put *additive* lemmas in new leaf modules
(`PVM/SymExec/Lemmas/*`) imported only by their users, rather than appending them to `Sound.lean` or
`Cut.lean`. That saves up to about 100 serial min per additive-lemma PR, and nothing for definitional
changes. P3 would make this convention unnecessary.

**Touches.** `PVM/SymExec/` (active area).

## 3. Overlap with active work, and the suggested order

Active areas are `Services/Bootstrap/Acc/`, `Refine/`, `PVM/SymExec/` and `Fmt/`. In-flight
infrastructure work is #193 (CI auto-resume and a lake-cache release) and #202 (CI split).

| proposal | touches an active area? | conflict risk |
|---|---|---|
| P1 append-only tiers | the generator only; the Acc, Refine and Fmt sessions *use* the new tiers | low: the sessions need to adopt it |
| P2 sharded code facts | the import lines of nearly all of `Services/Bootstrap/**`, including Acc, Refine, Fmt and `Bootstrap/SymExec` | **high**: touches every open PR's imports |
| P3 module-system spike | none (one Alloc hub in a throwaway branch) | none |
| P4 Alloc and bottom-stack chains | none (`Alloc`, `Reader`, `Memcpy`, `DecodeU16/32`, `Decode/Tag`) | low |
| P5 slow-module splits | `Acc/Inputs`, `Refine/ArgsRun`, `Bootstrap/SymExec/ProgAll` | medium: coordinate with the owners |
| P6 CI runner | CI config, which #193 and #202 also edit | sequence after #193 and #202 |
| P7 SymExec leaf-lemma convention | `PVM/SymExec` (convention only) | low |

**Suggested order.**

1. **P1 now.** It is the cheapest, it removes the largest recurring cost, and it fits the re-sync rule
   in `CLAUDE.md`: an append-only tier triggers no re-sync of unrelated open PRs.
2. **P3 spike in parallel.** It is independent of everything else, and its result decides P4's scope
   and whether P7's convention is needed.
3. **P6 decision** once #193 and #202 have merged, because all three edit the CI workflow.
4. **P4**, edge by edge, in small PRs. It overlaps no active area.
5. **P5** for the modules outside active areas first (`Decode.Lookup`, `Alloc.*`, `NoInstrArgs`). For
   `Acc/Inputs`, `Refine/ArgsRun` and `ProgAll`, the owning session does the split when it next
   touches the file.
6. **P2 last**, as a single mechanical PR at a quiet point, once open Bootstrap PRs have landed. Fold
   the P1 tiers in during the same cold rebuild. It is optional if P1 alone proves enough.

## Caveats

- The times are wall times on shared cores, and 24% of the modules are imputed. Rank the proposals by
  these numbers; don't plan schedules on them.
- The history replay uses today's import graph for past commits. A module's past dependents could
  have differed, but the hubs have been stable.
- The "unused import" count in P4 is a lexical heuristic, and each edge needs a build to confirm it.
- The module-system claim in P3 is unverified until the spike runs.
