# Accumulate's instruction handlers

These are summaries of what bootstrap's accumulate does for each `Instruction`, from the dispatch
point to the shared tail. The pattern (entry state `AtDispatch`, exit at 14278, the result at
`RES` = sp + 1000, `KeepsExcept` for every other memory change) is documented in
`Dispatch.lean`. Copy it for new handlers.

| File | Handlers |
| --- | --- |
| `Dispatch.lean` | `AtDispatch`, `KeepsExcept`, the jump table, slot and word helpers |
| `NoCall.lean` | `lookedUp_none`, `lookedUp_some`, `assignForGasCost_empty`, `panic` |

## The dispatch table

Read off runs of Ψ_A in this model (`accHostFn`, `Params.full`), one operand holding one
instruction each. "→ 14278" means the handler joins the shared tail. Host calls are inline unless
an out-of-line function is named. `alloc` is 40494, `dealloc` 40613, `format!` (`core::fmt`) 59375,
and `log` is host call 100.

| Tag | Instruction | Handler | What it does on the way to 14278 |
| --- | --- | --- | --- |
| 1 | `Upgrade` | 11740 | `upgrade` (20) at 11792, 49541, alloc 9, `log`, dealloc |
| 4 | `Eject` | 9444 | `format!`, `log`, dealloc, then `eject` (22) at 9584 |
| 6 | `Solicit` | 11669 | `solicit` (24) at 11712, then `format!`, `log` |
| 8 | `Lookup` | 10927 | `lookup` (3) at 11008, 48295, then `format!`, `log` |
| 9, 21 | `Import`, `RandomStorageRefine` | 12487 | memcpy, `format!`, `log`: `Err(Invalid)` |
| 11 | `Bless` | 9614 | 26006 (allocates), then `bless` (15) at 35011; panics unless bootstrap is the manager |
| 12 | `Assign` | 12096 | 40215 (alloc + copy of the queue, `assign` (16) at 40397), dealloc |
| 13 | `Designate` | 10017 | 49597 (`designate` (17) at 49874), alloc 19, `log`, dealloc |
| 14 | `Yield` | 9301 | `yield` (26) at 9345, 47845, `format!`, `log` |
| 15 | `Checkpoint` | 9944 | `checkpoint` (18) at 9944, alloc 13, `log`, dealloc. The results write (36170) comes before the dispatch, at 8650 → 8710 |
| 16 | `Panic` | 15361 | trap (☇) |
| 18 | `LookedUp` | 9193 | nothing: `None` → 13199 (`Err(Lookup)`), `Some` → 9202 (`Ok(Data)`) |
| 19 | `Imported` | 9047 | `format!`, `log` |
| 20 | `Exported` | 12377 | `format!`, `log` |
| 24 | `AssignForGasCost` | 11173 | empty queue: nothing (→ 13541, `Ok(Unit)`, then dealloc of the queue's buffer if its capacity is not 0); otherwise alloc and `assign` |

`gas` (0) at 11330 and 13011 (in the `Transfer` and `CreateService` paths): ω₇, the gas left, is
stored to sp + 1384 and sp + 1472 and used later. `checkpoint` at 8490 and 9944 is followed by an
instruction that overwrites ω₇ without reading it. 11889 (`Benchmark`) is not checked yet.

## The route to Ψ_M: the answer-queue contract

T2 uses `accContractQ env` (`Acc/ContractQ.lean`), whose context `AccCtxQ = AccCtx × List Nat`
carries a queue of answers for the two host calls that return the gas left: `gas` (0) and
`checkpoint` (18). At those ids the call takes the queue's head as ω₇; at every other id the step is
the model's (`accHostFn env`) outcome at some gas, not ∞, with the queue kept.
* Given its queue, a run is determined (`accContractQ_pins`, then `FreeRunH.det`).
* `psiM_of_freeRunH_accQ`: Ψ_M is ∞, or its output and context are those of a run under
  `accContractQ` for some queue (the gas values actually left at those calls).
* So the summaries are stated for every queue, and post-states never mention the answers (they
  reach only logging, or an ω₇ that is overwritten). The T2 statement does not mention the queue.

How the summaries get there:
* Summaries that make no `gas` or `checkpoint` call are stated under `accContractK cap env`
  (Upgrade, Designate, Assign, `Checkpoint.midK`). `FreeStepsH.toQ` carries them to
  `accContractQ` for every queue (kept), and `weaken` with `accContractK_le_CK` to `accContractCK`.
* Summaries through a `checkpoint` or `gas` call have a Q version that pops the queue
  (`Checkpoint.toAllocQ`, through `FreeStepsH.checkpointQ` / `gasQ`).
* The `accContractC` / `CkLift` route (#130, #140: ω₇ := 0 at `checkpoint`, dead afterwards) stays
  valid; the CK versions (`Checkpoint.toAlloc`, `Checkpoint.mid`) are kept.

## The gas cap

Host calls are stepped through at gas `cap` (`accHostK`, `logK`): each call's outcome is the model's
(`accHostFn env`) at gas `cap`, which must cover the call's charge. So every summary that makes a
host call takes the cap as a parameter, with only the bounds its calls need. The top-level
statement picks one cap that covers all of them, and the allocator's summaries (`alloc_callG`:
heap growth) need 2²⁷ ≤ cap anyway.

| Summary | Calls | Cap needed |
| --- | --- | --- |
| `Checkpoint.toAlloc` | `checkpoint` (18) | 𝖬_C = 103 ≤ cap |
| `Checkpoint.mid`, `Upgrade.mid` | `log` (100) | 𝖬_∅ = 1000 ≤ cap < 2⁶⁴ |
| `Upgrade.toCheck` | `upgrade` (20) | 𝖬_U = 1028 ≤ cap < 2⁶⁴ |
| Designate (in progress) | `designate` (17) | 1100 + 302 · z ≤ cap < 2⁶⁴, z keys |
| Bless (to do) | `bless` (15) | 422 + 20 · z ≤ cap < 2⁶⁴ |

## Session 2 progress (2026-11-15, row 8)

Toolchain: no lake-cache release yet, so a local build (`lake build <module>`; a cold build of the
Handlers dependencies takes ~2 h on 4 cores). Use `ulimit -v 12000000` when compiling single files.

**Done (compile; axioms only propext / Classical.choice / Quot.sound; not yet imported from
`Services.lean`, so not in CI):**
- `RecentCounter.lean`: the counter write's segments `cw_pre` (8326 → 33843), `cw_mid` (8348 → 48104),
  `cw_ret` (set's returns → 8376), `cw_dl` (8376 → 40613), `cw_ok` (8402 → 8416), `cw_err` (→ 15361).
- `RecentCounterImpl.lean`: `trap_34070`, `keep_yin`, `cw_free` (set's return → `dealloc` → 8402,
  any host relation) and **`counter_write`**: from 8326 the run implements
  `store .counter (fixed 4 w)` in `Impl` form under `accContractS`, with any `Ab` covering the trap at
  34070 (alloc failure = heap). Post `CwPost` at 8416: ω₁ = sp, `HeapCtxC` for some st′ keeping st's
  chunks and their data, memory kept above sp off `CwOut`, at `Glob` (196616 … 196791, so the
  `ParamStatics` words) and below 196608. Hypotheses: the tag-0 size word kc at 68680 (1 ≤ kc,
  kc + 31 < 2³⁶), `set`'s error-table entries (69056, 69072), 68680 … 69076 readable, the frame
  S0 + 240 ≤ sp, sp + 1856 ≤ S1, the old value under `[0]` < 2⁶³ (`ValuesFit`).
- `RecentSlot.lean` (34377, the slot's typed get): `re_short` (58434 with len < n returns ω₇ = 1),
  `sg_pre` (34377 → 33843), `sg_get` (34400 → 47857), `sg_dl` (34417 → 40613, cap ≠ 0), `sg_none`
  (34434 → return when get gave `None`).

**Pitfalls found:**
- Never `dsimp only` / `generalize` / `rw` a goal whose `match` scrutinee is `ASem.step … s.c` with
  `s` a structure literal: Lean whnf's `ASem.step` and runs out of memory. First
  `rw [show ({ i := …, c := c, q := f } : St Stream).c = c from rfl, hstep]` (exact syntactic form),
  then `dsimp only` once the scrutinee is `some …`.
- `pvm_go` needs `↓rdN_fold` for loads; for a return through a saved ω₀ add `rdN_writeN_same8`
  (`Fmt.`), `Num.decodeLE_encodeLE` and the `Nat.mod_eq_of_lt` facts.
- `refine ⟨?ω', ?run⟩; case run => pvm_go …` for a one-witness existential.


## Session 9 progress (2026-11-16)

- `ResultsDropRun.lean`: **`drop_results`** (28864 → caller t, any n, generic in R): every buffer in
  `resPtrs μ₀ rp n` freed (state `(resPtrs μ₀ rp n).foldl free s₀`), `Kept` (other allocated chunks of s₀ kept
  with data), `Frm` (memory from the caller's sp S up, globals, non-writable octets, same access), ω₁ = S,
  ω₅/ω₆ restored. Needs `HeapCtxC`, `ResultsOwn`, `SpOK S0 S1 S` (S − 56 ≥ 2³¹ + 60, S0 + 96 ≤ S ≤ S1).
  Pieces: `Core` (invariant), `Core.sk/dk/rd/item/inr`, `dv_cell`, `dv_inner`, `dv_out`, `dr_data`, `dr_vec`,
  `dr_item`, `dr_loop`, `init3`. Axioms clean. Pitfall: never close `free s w = (FR ++ [w]).foldl free s₀` by
  `rfl` (the kernel unfolds `free`, OOM); rewrite with `List.foldl_append/cons/nil`.
- `ResultsDropRun.lean` (end): `ChunksKept μ st μ' st'` (= `StorePost`'s chunk clause) and **`ResultsOwn.keep`**
  (with `resPtrs_keep`, `itemPtrs_keep`, `item_keep`, `innerPtrs_congr`). Axioms clean. Avoid `congr 1` on
  goals with `rdN` (whnf timeout).

## Session 8 handoff (2026-11-16, for the 9th session)

**PRs.** #224 (row 8) merged. **#228** (row 9 `results_init`, R4 `ResultsAt`, `ResStoreLoopSeg`,
`docs/t2-remaining.md`; branch `claude/bootstrap-t2-handlers-a-row9`, rebased on main, local full build green)
is open and subscribed: `model` green, attempts running. **Merge it on green** (squash), tell @parent.

**Branch `claude/bootstrap-t2-handlers-a-r5`** (pushed; = old row-9 branch + #222's head + this work; no PR).
Rebase onto main once #222 and #228 merge, before opening its PR (#228's commits are the pre-rebase row-9
commits: `git rebase --onto origin/main <old row-9 tip 6450fb4>`; #222's own commits drop out once it merges).
New this session (all compile, axioms clean, imported from `Services.lean`):
- `ResStoreLoop.lean`: **`rl_loop`** (36346 → 36405, induction on n − k with `rl_item`).
- `ResStoreImpl.lean`: `RetOK ret t` (294 → 8477 row 9, 300 → 8716 Checkpoint instr, 562 → 15121 row 11),
  `rs_endG`, **`res_freeG`** (any value chunk dv with cap vc, any `RetOK` return); `res_free` now a corollary
  (statement unchanged).
- `ResStoreGen.lean`: `res_enter` (36170 → 36346, `LoopInv 0`), `res_exit` (36405 → 48104), `SetPre` (the
  state at `set`'s call, with |val| ≤ vc ≤ 32·(dv.size − 1)), `SetPre.mono`, **`res_store`** (36170 → 48104,
  any n; aborts 36528 / 34070 / `ExhaustsP`; value `encodeResults rs`).
- `ResStoreCall.lean`: `ExhaustsP.aborts` (an `ExhaustsP` is an `Aborts` when `Ab` covers 40611/40821),
  `StorePost`, **`store_core`**: 36170 → caller t (`RetOK`) is `Impl` of
  `orPanic (write (keyEnc μ (sp+1568) 2) (encodeResults rs))` against `ExtendH`/`OkEncH`; FULL continues at t
  with ω₇ = 3 where the caller's `herr` ends ☇. Usable for row 11 and for the Checkpoint instruction (R5).
- `RowElevenSeg.lean`: `r11_flag0/1` (15038: [sp+160] & 1), `r11_pre` (15060 → 36170, ret 562), `r11_ok`
  (15121 → 15133), `r11_err` (→ 15361).
- `ResultsDropSeg.lean`: every straight-line segment of the results drop 28864 (see its module doc), incl.
  `back8` (the [ω₅ − 8] load: keep ω₅ = q opaque, never `r + 8`, or the kernel recurses on the folded 2⁶⁴ literal).
- `ResultsDrop.lean`: `innerPtrs`, `itemPtrs`, `resPtrs`, **`ResultsOwn`** (decided by @parent: option (A),
  additive next to `ResultsAt`; R5 must produce it), `innerPtrs_succ/split`, `resPtrs_succ/split`, `nodup_next`.

**Decision this session (@parent, option A for R7's drops):** `ResultsOwn` additive; prove 28864 and the
deallocs (15166 results buffer, 15185 [sp+104]/[sp+128], 15201 [sp+272]/[sp+264]); 33214 (drop of the
`IntoIter<Instr>` at sp+472, per-kind drops via the table at 68312) is a named frame-only hypothesis
**`DropInstrsH`** over an InstrRep footprint. `InstrRep` doesn't exist yet: define the bundle (parameter shared
by R3/R6, with a footprint field and `DropInstrsH`) on r5 yourself; list `DropInstrsH` in
`docs/whats-proven.md` and `docs/t2-remaining.md`. @parent tells T2 inputs (R2 passes it through).

**Row 11 map** (jte: 558 → 15038, 560 → 15060, 562 → 15121, 564 → 15143, 566 → 15172, 568 → 15191, 228 → 6766):
15028: ω₇ = sp+472, call 33214 (ret 558) [15050: same, ret 560 → 15060, skipping the flag]; 15038 flag;
15060 … 15115 key + call 36170 (ret 562); 15121 Ok check (else ☇ 15361); 15133: ω₇ = sp+448, call 28864
(ret 564); 15143: if [sp+448] ≠ 0, dealloc([sp+456], 144·cap, 8) ret 566; 15172: if [sp+128] ≠ 0,
dealloc([sp+104], …, 1) ret 568; 15191: if [sp+264] = 0 → 6766, else dealloc([sp+272], …, 1) with ω₀ = 228
(→ 6766). The last two buffers' chunk facts are premises of R7 (from R2's state).

**Next, in order:**
1. Merge #228 on green.
2. `drop_results` (in `ResultsDrop.lean`), generic in R (all segments and `dealloc_callG` are): plan —
   - `Kept s0 μ0 FR μ s` := ∀ d ∈ chunks s0 used, d.addr + 32 ∉ FR → d ∈ chunks s ∧ data kept vs μ0;
     `Frm`: memory from S up, `Glob`, non-writable octets kept vs μ0; readable/writable equal.
   - helper `sk` (a stack write in [F, F+56) keeps HeapCtxC/Kept/Frm; F = S − 56 ≥ 2³¹) and `dk` (a dealloc
     call of q ∉ FR whose chunk is in s0: `dealloc_callG` → HeapCtxC (free s q), Kept (FR ++ [q])).
   - outer invariant at 28929 for item k with FR = `resPtrs μ0 rp k` (ω₁ = F, ω₅ = n, ω₆ = k, F = n,
     F+8 = rp, F+48/40/32 = ret/v5/v6); item step to 28922 with FR = resPtrs (k+1), by tag (255, < 5, 5,
     6 … 254); then `dr_next0/1`; end `dr_end`. Item reads: octets in a chunk ∉ resPtrs (ResultsOwn.3) → kept.
   - inner invariant at 29014 for j with FR = resPtrs k ++ innerPtrs q j, ω₅ = q + 8 + 24j, F+24 = end; reads
     in the outer chunk (∉ FR by `nodup_next` on resPtrs n = resPtrs k ++ innerPtrs q j ++ w :: …).
   - result: HeapCtxC μ' s', Kept (resPtrs μ0 rp n), Frm, ω₁ = S, ω₅/ω₆ restored, at t.
3. `ResultsOwn.keep` (store_core keeps st's chunks with data, so resPtrs and ResultsOwn survive).
4. R7 (`RowEleven.lean`): DropInstrsH + flag + `store_core` (or skip) + `drop_results` + the three deallocs →
   6766, as `Impl` of `unless (is.any zombify) (store key (encodeResults rs))`.
5. R5 (the instruction loop) as before; it must produce `ResultsVec`, `ResultsOwn`, [sp+160] ↔ Zombify.

## Session 7 handoff (2026-11-16, for the 8th session)

**Branches.**
- `claude/bootstrap-t2-handlers-a-row9` (based on #224's branch): row 9 (`ResStoreImpl`, `ResultsInit`), R4
  (`ResultsAt`), 36170's loop segments (`ResStoreLoopSeg`), `docs/t2-remaining.md`. All compile locally; imported
  from `Services.lean`. **To do:** once #224 merges, rebase onto main, full `lake build` in the background, open
  the PR (body: row 9, R4, the map, plan B; the GetCall/GetKeyCall note below), merge on green.
- `claude/bootstrap-t2-handlers-a-r5` = row9 branch + #222's head (`claude/bootstrap-t2-inputs-wip`) merged in
  (parent's answer (c)). Adds `ResultsHyp.lean` (R8 `ExtendH`, R9 `OkEncH`, `WriterPre`, `WriterPost`) and
  `ResStoreLoop.lean` (`ExhaustsP.pre`, `encK`, `LoopInv`, `LoopHyp`, `writer_chain`, `ext_step`, **`rl_item`**:
  one pass of the loop, Ok and Err, axioms clean). It also carries a one-line fix in #222's
  `Acc/Transfer/GetKeyCall.lean:197` (`fr5⟩` → `fr5, -, -, -⟩`), needed because #224's `get_some` has more
  conclusions; the parent is sequencing #224/#222 (whichever merges second needs that line). Rebase this
  branch onto main once #222 (and the row-9 PR) merge, before opening its PR.

**Decisions this session (parent):** park row 11 as such; plan B (Adam, decision 23): T2 as a skeleton with named
hypotheses (R6 per handler, R3 decode success, R9 encoder per item, R8 writer step, G4 log lines as Fmt
hypotheses). `InstrRep` is a parameter shared by R3/R6 with a copy/frame field (obligation: T1's per-kind Reps
discharge it). Handlers A states the G4 Debug log-line hypotheses itself (minimal, frame-only, like `LogFmt`;
list in whats-proven.md). R5's result is the contract T2 inputs' R2 consumes (see `docs/t2-remaining.md`).

**Next, in order (Handlers A):**
1. `rl_loop`: induction on k with `rl_item` (n − k passes; `rl_enter` first; ends at 36405 with `LoopInv n`).
2. `res_store` (general n ≥ 0): from 36170 like `res_head` (rs_pre, alloc 144n+4, rs_vec, prefix_any) to
   `LoopInv 0` (μ₀ := memory after prefix_any; ℰ(n) = encK n rs 0; buffer chunk fresh vs st), then `rl_loop`,
   `rl_tail`, `kb_call`, `rs_set`, `set_call`, and a `res_free` generalised to any value chunk (the buffer may have
   grown: chunk `d` with d.addr + 32 = r). Convert the HeapHost runs with `FreeStepsH.growS`. For n = 0 reuse
   `res_head`. Aborts: 36528, 34070, and `ExhaustsP` (T2 inputs' `AccAbort` must cover its state).
3. R7: row 11 (15032 … 15198): unless [sp+160] = 1, `res_store` with the final results; drops 33214 (ret 558/560),
   28864 (ret 564), deallocs at 15166 / 15185, back to 6766.
4. R5: the instruction loop (map in this README's parent message; 8493 setup, head 8540, end 15028/15050; per item:
   copy to sp+744 (memcpy 68729, `memcpy_val`), Zombify flag [sp+160] for tag 3, Checkpoint (tag 15) pre-write via
   36170 at 8655 → 8716 (use `res_store`), Debug log line at 8772 (G4 hypothesis), copy to sp+1144, dispatch 8822,
   handler hypothesis `HandlerImpl` (R6) to 14278, the tail (result log line, G4; push with growth, R8-style
   hypothesis or `ExtendH`-like for the 144-octet push), back to 8540), as `Impl.forIn` with `ResultsVec`.

## Session 7 progress (2026-11-16, row 9 composed)

- `ResStoreImpl.lean`: `rs_j1` (40611 → 36217), **`res_head`** (36170 → `set` at 48104, n = 0, any `HeapHost`;
  traps 36528 / 34070; key `keyEnc μ kp 2` in a chunk of (kc+31)/32+1 units, value [0] in a 2-unit chunk;
  memory from sp up kept) and **`res_free`** (`set`'s return → 8477; ω₇ = −1 for `Ok`, else the error octet).
- `ResultsInit.lean`: **`results_init`**, the `Impl` of `store (.results (μ[sp+312..+32]) item) (encodeResults [])`
  then `op .checkpoint` from 8416 to `R9Post` at 8492 (ω₁ = sp, HeapCtxC for some st′ keeping st's chunks with
  data, memory above sp kept off `R9Out` = [sp+1568, sp+1604), Glob, below 196608 with readability).
  Hypotheses: [sp+464] = 0, kc at 68696 (35 ≤ kc), set's error table, 68680 … 69076 readable, frame
  [sp − 352, sp + 1632), ℰ₂(item) = μ[sp+176..+2], `StoreFit`; `[HasCodeX p P]`. Ab covers 36528, 34070.
  Axioms clean. Both imported from `Services.lean`.
- Row 11 parked; **plan B** (Adam, decision 23): T2 as a skeleton with named hypotheses. Handlers A does R4,
  R5, R7 of `docs/t2-remaining.md` (map written this session).
- **R4 done:** `ResultsAt.lean`: `InHeap`, `VecAt`, `OkAt`, `ResultAt`, `ResultsAt`, `ResultsVec` (cap/ptr/len at
  sp+448/456/464), `KeepsHeap`, `ResultsAt.keep` (frames keeping st's chunks with data keep it), `ResultsAt.nil`.
  Layout read off the encoder arms (36346 … 36394, 30374 … 30640).
- `ResStoreLoopSeg.lean` (compiles): 36170's loop for n ≥ 1: `rl_enter`, `rl_ok`, `rl_okenc`, `rl_err`,
  `rl_errcode`, `rl_next`, `rl_tail`. Return addresses: 1696 → 36290, 1698 → 36335, 1700 → 36373, 1702 → 36394.
- **Waiting on @parent** (sent 2026-11-16): InstrRep as a hypothesis parameter vs T1 export; who states the Debug
  log-line Fmt hypotheses; using `memcpy_val`/`ExhaustsP` from #222 (R8/R9 hypotheses use `ExhaustsP`).
- **Next:** R8 hypothesis (`extend` at 58508 under HeapHost, shaped like refine's `extend_any`) and R9 (36299 per
  Ok item appends `(Result.encode (.ok r)).drop 1`), both with `ExhaustsP` failure; then the general-n 36170
  (`res_store`), R7 (15032 … 15198), R5 (loop 8493 … 15028, see the map in the parent message).
- Row 9: rebase onto main once #224 merges, full build, PR, merge on green.

## Session 6 progress (2026-11-16, row 8 composed)

- `RecentAddGen.lean`: `Prog.bind_assoc`, **`addRecent_eq`** (spec `addRecent` as four binds: counter get,
  slot read + removal, slot write, counter write), `ASem.step_read_ctx` (`read` keeps the context),
  `Prog.All`, **`Impl.inv`** (a context invariant through `Impl` along a program whose operations keep it),
  `StoreFit` (all storage values < 2⁶³), `SmallOp` and `storeFit_step`.
- `RecentAdd.lean`: **`add_recent`** (8013 → `AddPost` at 8416, `Impl` of `addRecent Cs (μ[sp+512..+32]) item`
  with ℰ₂(item) = μ[sp+176..+2]). Hypotheses: kc₀ at 68680, kc₁ at 68688, the `set` error table, 68680 … 69076
  readable, frame [sp − 352, sp + 1856), `ParamStatics`, `RingFits`, `Cs.maxRecent = 2·C·I`, `StoreFit`.
  Ab covers 34070, 47977, 32584. `AddPost`: ω₁ = sp, HeapCtxC for some st′ keeping st's chunks and data,
  memory kept above sp off `AddOut` (= RmOut ∨ SwOut ∨ CwOut), at Glob and below 196608. Axioms clean.
  Not in `AddPost`: readability below 196608 (`counter_write`/`CwPost` don't state it); add it there if
  row 9 needs it.
- Tip: foreground `sleep` loops return at once in this environment; wait with a background until-loop.
  To compile a new module before `lake build` reaches it: `lake env lean F.lean -o <olean> -i <ilean>`.
- Row 8 is **PR #224** (opened 2026-11-16; `model` green, attempts running). Merge on green.
- **Row 9 started (local commits on this branch, pushed only after #224 merges, since a push restarts its CI):**
  - `ResStoreSeg.lean` (all compile): 36170's n = 0 path in the callee frame S = sp − 96: `rs_null` +
    `trap_36528` (alloc null → ☇, a heap-exhaustion reason), `rs_vec` (36217 → 30977, Vec {144n+4, ptr, 0}
    at S+32, n u32 at S+56, ret 1694 → 36263), `rs_zero` (36263 → 33843 for n = 0: value cap → S+24, len →
    S+8, ptr in ω₆; key encoder with out S+32, kp from S+16, ret 1704 → 36432), `rs_set` (36432 → 48104:
    out S+56, key ptr/len S+40/S+48, value ω₆ / [S+8], vp saved at S; ret 1706), `rs_ret` (set's returns →
    36456), `rs_d1` (36456 → 40613: r saved at S+16, b = u8 [S+64] in ω₆, dealloc key buffer ω₅, ret 1708 →
    36482), `rs_d2` (36482 → 40613: dealloc [S], ret 1710 → 36499), `rs_end` (36499 → 8477, ret 294
    hard-wired: ω₇ = −1 if r ≠ −1 else b; ω₀/ω₅/ω₆ restored).
  - `ResultsInitSeg.lean` (all compile): `ASem.step_checkpoint` (y := x), `r9_pre` (8416 → 36170: tag-2 key
    value at sp+1568 from the package copy at **sp + 312** (not sp + 512) and the item u16 at sp+176;
    ω₇ = [sp+456] results ptr, ω₈ = [sp+464] n; ret 294), `r9_ok` (ω₇ = −1 → 8490), `r9_err` (ω₇ = 3 →
    15361), `r9_ck` (8490 → 8492 as a `YIn (accContractS env) c.2 c.1` step).
  - **Next for row 9:**
    1. `res_store0` (36170 → 8477, n = 0), composing exactly like `sw_head` + `sw_free`
       (RecentSlotWriteImpl.lean): `rs_pre`, `alloc_callG` (4 octets; null → `rs_null`), `rs_vec`,
       `Encode.VecCore.prefix_any` (needs `[HasCodeX p P]`, available at top level as in Acc/Start.lean;
       ℰ(0) = [0]), `rs_zero`, `kb_call` (tag 2, key size word at 68696, `keyEnc μ (sp+1568) 2` =
       `(Key.results pkg item).encode`), `rs_set`, `set_call` (value [0], length 1), `rs_ret`, `rs_d1`,
       `dealloc_callG`, `rs_d2`, `dealloc_callG`, `rs_end`. Ab gets 36528 and 34070.
    2. Row 9 as `Impl` of `Prog.bind (store (.results pkg item) (encodeResults [])) (fun _ => op .checkpoint)`
       from 8416 (check `encodeResults [] = [0]`), with hypotheses: [sp+464] = 0, μ[sp+312..+32] = package.
       Post at 8492 (after the checkpoint, ω₇ = stream head). The checkpoint's ASem step is
       `step_checkpoint`; the run is `r9_ck` (no Reaches before it beyond `r9_ok`).
    3. Then compose rows 8 + 9 if useful, and row 11 (15032 … 15198, see the plan below).

## Session 5 progress (2026-11-16, row 8)

Adam decided both row-8 questions (2026-11-16): ring size (a), counter wrap (a).
- **Q19** in `Spec.addRecent`: the counter is stored as `fixed 4 (((c + 1) % 2^32) % C.maxRecent)`;
  `SpecLemmas/Ring.lean` adapted (`addRecent_counter'` exact, `addRecent_counter` for c < maxRecent).
  Rows in docs/bootstrap-target.md (Q19) and docs/upstream-candidates.md.
- `RecentSlotWrite.lean`: `ParamStatics μ C I`, `RingFits C I` (0 < 2·C·I < 2³²), `rw_writable`, and the
  segments `sw_pre1`, `sw_pre2`, `sw_j1`, `sw_null`, `trap_32584`, `sw_v1` … `sw_v4`, `sw_ret`, `sw_d1`,
  `sw_d2`, `sw_end`, `sw_ok1` (8266 → 8312), `sw_ok2` (8312 → 8326), `sw_err`. docs/whats-proven.md lists
  `RingFits` (assumption of T2, possible discharge from fetched parameters) and `ParamStatics` (obligation).
- `RecentSlotWriteImpl.lean`: `sw_head` (8172 → `set` at 48104), `sw_free` (`set`'s return → 8266),
  **`slot_write`** (8172 → `SwPost` at 8326 as `Impl` of `store (.recent c) (μ[sp+512..+32] ++ μ[sp+176..+2])`;
  Ab at 32584 and 34070; ω₇'s low 32 bits = ((c + 1) mod 2³²) mod 2·C·I). The counter register c may be
  any 64-bit value (the binary's counter is a sign-extended `i32`).
- `RecentCounterGet.lean`: segments `cg_pre`, `cg_g`, `cg_gret`, `cg_dk`, `cg_none`, `cg_some`, `cg_fin0`,
  `cg_finD`, `cg_finR` (the counter's typed get, 8013 … 8056; 34637 is the get's continuation).
- `RecentCounterGetCall.lean`: **`counter_get`** (8013 → 8056 under `KeepCtx (accContractS env)`): ω₅'s low 32 bits
  = `ctrVal (storage [0])` (= `((·).bind (decode (fixedN 4))).getD 0`), or the traps 34070 / 47977; keeps
  memory and its access below 196608.
- **Read-only access** (parent approved (a), 2026-11-16): `get_call` / `get_some` (GetCall.lean) gained
  `∀ a < 196608, μ'.readable a = μ.readable a`. Row 8 needs 68680 … 69076 readable at every stage.
- **Next (in order):**
  1. Done: `sg_fret`, `sg_tailW`, `sg_tailE`, `slot_get`, `rm_head`, `recent_match` (`RmPost`), `counter_get` all
     state that memory access below 196608 is kept. Every Handlers module is imported from `Services.lean`.
  2. Compose row 8 from 8013: `addRecent` elaborates with a join point, so first prove
     `addRecent C pk it = Prog.bind (load .counter (fixedN 4)) (fun o => Prog.bind (Prog.bind (load (.recent
     (o.getD 0)) slotDec) (match …)) (fun _ => Prog.bind (store (.recent (o.getD 0)) (encodeRecent pk it)) (fun _ =>
     store .counter …)))` with a local `Prog.bind_assoc` (the match branches are `bind (op remove) jp` / `jp ()`).
     Then `Impl.bind` four times: `counter_get` (call form with s₁ = s, `ASem.step_read`, `keep_yin`), `recent_match`
     with c := ω₅.toNat (`Key.recent` only uses c mod 2³²; spec c = `ctrVal`), `slot_write`, `counter_write` with
     w := ω₇.toNat (`fixed 4 w = fixed 4 (w mod 2³²)`). Needs `C.maxRecent = 2·𝖢·𝖨`, package = μ[sp+512..+32],
     ℰ₂(item) = μ[sp+176..+2] (both kept by counter_get / recent_match frames), `hvals` for the storage after each
     write (`writeSelf` keeps other keys; written values are short).
  3. Import every new module from `Services.lean`; full `lake build` in the background; PR (body: Q19, RingFits,
     the GetCall addition, ParamStatics obligation).

## Session 4 progress (2026-11-15, row 8)

**Done (compile; RecentMatch not yet imported from `Services.lean`):**
- Step 1 of "Next (row 8)" below: `get_call` and `get_some` (Acc/Wrappers/GetCall.lean) gained two
  conclusions, `∀ a, Glob a → μ'.read a = μ.read a` and `∀ a, a < 196608 → μ'.read a = μ.read a`
  (from alloc's `HKeepGD` and `HeapHost.keepRO`); every old conclusion unchanged. `get_none` /
  `get_empty` already had a frame covering both. `slot_get` gained the same two, plus
  `∀ w, storage(keyEnc μ kp 1) = some w → w.length < 2³¹` (from the value's chunk, < 2³⁰) for
  `ASem.step_read`.
- `RecentMatch.lean`: `ASem.step_remove` (`.remove` evaluates to `none` on FULL, else the account
  := `writeSelf self key []`; stated with `writeR7`/`writeSelf` to match `remove_call`).

- `RecentMatch.lean` also has (all compile): `rm_pre` (8056 → 34377), `rm_none` (8079 → 8172),
  `rm_some` (8079 → 51243), `rm_j` (8165 → 48481), `rm_back` (48514/48531 → 8172), `trap_47977`,
  `trap_48533`, `readN_32`, **`rm_to_remove`** (8079 → 48481 for `SlotOut … (some (q, k))`, the
  35 octets `(Key.results q k).encode` at sp + 744, ω₇/ω₈ set, frame off sp + 744 … 780 and
  sp + 1568 … 1604) and **`rm_head`** (8056 → 8079 via `slot_get`, or the traps 34070 / 47977).
- **`recent_match` done** (step 2): `RmOut`, `RmPost` and `recent_match`, the `Impl` of
  `Prog.bind (load (.recent c) slotDec) (match · with | some (q, k) => op (remove (results q k)) |
  none => pure ())` from 8056 to `RmPost` at 8172. Hypotheses: H, ω₁ = sp, ω₅ = c, the stack frame
  (S0 + 352 ≤ sp, sp + 1632 ≤ S1), the tag-1 key-size word at 68688, `hvals` (all this service's
  values < 2⁶³). Ab at 34070 and 47977.
- The FULL case needed `Impl`'s none branch weakened (parent approved option A): **PR #215**
  (`claude/t2-impl-none-y`, Impl.lean + Prefix.lean only), now `∃ c', c'.2 = s.c.2 ∧ Ends p (YIn R
  s.c.2 s.c.2) s₁ .panic c'`. This branch carries the identical patch; merge main after #215 lands.
- Tip: `rw [ASem.step_… ]` on a goal mentioning `{ i := …, c := c0, … }.c` ran out of memory; first
  `rw [show ({ … } : St Stream).c = c0 from rfl]` (as counter_write does).

**Open questions for Adam (sent 2026-11-16; parent recommends 1(a), 2(a)); they block the slot write.**
Code: 8293 C = u16 [196616]; 8301 I = u64 [196696]; 8306 mul64; 8309 shloLImm32 by 1 (2·C·I mod 2³²,
sign-extended); 8312 panic (15361) if 0; 8320 ω₅ := c + 1 (64-bit); 8323 remU32 (low 32 bits). Spec:
`fixed 4 ((c + 1) % C.maxRecent)`, maxRecent = 2·C·I unbounded.
1. Ring size: the binary agrees only if 0 < 2·C·I < 2³² (C = 341, I = 16 gives 10912). (a) Premise
   `ParamStatics μ C I ∧ 0 < 2·C·I < 2³²` (named hypothesis on the chain parameters); (b) model the
   wrap and the panic in Spec.
2. Counter wrap: for a stored counter c = 2³² − 1 the binary stores 0, the spec 2³² mod 10912 = 5440.
   (a) New quirk: Spec `fixed 4 (((c + 1) % 2^32) % C.maxRecent)`, recorded in bootstrap-target.md and
   upstream-candidates.md; (b) hypothesis c ≠ 2³² − 1; (c) hypothesis c < maxRecent.

**Next (row 8, steps 3 and 4 of the old list):** the slot write 8172 … 8326 (key {1, c} again,
(package, k) copied to sp + 1144, the inlined alloc of 34 octets and the encoder 32414, then `set`,
the 255 check, `ParamStatics` for 2·C·I and c′ := (c + 1) mod 2·C·I), the counter's typed get at
34637 (8031 … 8049; a separate function, u32 decode), then compose row 8 from the counter get,
`recent_match`, the slot write and `counter_write` (8326 → 8416) with `Impl.bind`. Then the row-8 PR
(imports in `Services.lean`, `ParamStatics` in docs/whats-proven.md as an obligation).

## Session 3 progress (2026-11-15, row 8)

Toolchain: `scripts/fetch-lake.sh` works (main's built `.lake`); then `lake build <module>` for the
dependencies and `lake env lean <file>` for one file. Use `ulimit -v 40000000` or more: with 12 GB
Lean fails with "failed to create thread".

**Done (compile; not yet imported from `Services.lean`):**
- `RecentSlotSeg.lean`: 34377's segments after `get`: `sg_some` (34434 → 58434), `sg_r2` (34485 →
  58434), `sg_short0` / `sg_shortD` (a short read: `None`, then return or `dealloc`), `okMem`,
  `sg_ok0` / `sg_okD` (the `Some` record), `sg_ret` (34623).
- `ReadExactText.lean`: `read_exact_text`, `Fmt.read_exact` plus the copied octets (via `memcpy_text`).
- `RecentSlotTail.lean`: `slotDec` (addRecent's decoder, `rfl`-equal to the one in `Spec.addRecent`),
  `slotDec_long` / `slotDec_short`, `SlotOut`, `sg_fret` (`dealloc` + return), `okMem_slot`,
  `sg_tailW` (34434 → return for a value w ≠ [] in a fresh chunk: three read-length cases),
  `sg_tailE` (the empty value).
- `RecentSlotGet.lean`: `sg_gret` (`get`'s exits → 34417) and **`slot_get`**: 34377 under
  `KeepCtx (accContractS env)` either returns with `SlotOut μ' out ((storage (keyEnc μ kp 1)).bind
  (decode slotDec))`, `HeapCtxC` for some st′ keeping st's chunks and their data, memory kept from SP
  on off out … out + 36; or reaches 34070 / 47977 (heap). Hypotheses: the tag-1 size word kc at 68688
  (5 ≤ kc, kc + 31 < 2³⁶), the frame [SP − 352, SP) in the stack, the value < 2⁶³ (`ValuesFit`).

**Decided (parent, 2026-11-15): (a).** `get_call` (Acc/Wrappers/GetCall.lean, T2-inputs' wrapper
area; the parent told them not to edit it meanwhile) gets two extra conclusions in place: `Glob` kept
and memory below 196608 kept (and `get_some` / `get_empty` / `get_none` as needed). Every existing
conclusion stays. Mention it in the PR body. Code facts: if new ones are needed, add a tier per
`docs/code-fact-tiers.md` (#205), don't regenerate CodeA, and tell @parent before pushing anything
touching `Code*`.

**Next (row 8):**
1. Extend `get_call` (and `get_some` / `get_empty` / `get_none`), then add the
   `Glob` and `< 196608` conclusions to `slot_get` (`sg_tailW` / `sg_fret` already have them).
2. 8056 … 8172 as `Impl` of `addRecent`'s `match ← load (.recent c) slotDec with …`:
   - 8056 … 8073: u16 1 at sp + 1568, u32 c (ω₅) at sp + 1572, then 34377 with out sp + 1144 and
     ret 280 → 8079. `Key.recent c` = [1] ++ fixed 4 c = `keyEnc μ (sp + 1568) 1` (c < 2³²).
   - 8079: u16 at sp + 1144 = 0 → 8172 (None).
   - 8086 … 8158: the 32 octets sp + 1146 → sp + 1572, the i16 at sp + 1178 → sp + 1570, tag u16 2
     at sp + 1568, sp + 744 … 780 zeroed; `kf_call` (51243, ω₇ = sp + 1568, ω₈ = sp + 744; ret 282 →
     8165), then 8165 jumps straight to `remove` 48481 (`remove_call`, ret 284 → 8172).
     `Key.results p i` = [2] ++ p ++ fixed 2 i = `keyEnc μ (sp + 1568) 2`.
   - The read is `Impl`'s call form with s₁ = s (KeepCtx run, `keep_yin` for the YIn part);
     `ASem.step_read` needs the value < 2³¹: get it from the chunk bound (data below base + 2³⁰).
3. 8172 … 8326 (slot write, inlined alloc + encoder 32414) and 8266 … 8326 (`ParamStatics`, c′).
4. 8031 … 8049: the counter's typed get at 34637 (u32 decode).
5. Add the modules to `Services.lean`; record `ParamStatics`' discharge obligation in
   `docs/whats-proven.md`.

## Handoff (T2 handlers-a, paused 2026-11-14)

**Branch:** `claude/bootstrap-t2-handlers-a-wip`. Resumed 2026-11-15: main merged in (with #186, so CodeA
has the 51243 facts); full build green; every Handlers module is now imported from `Services.lean`,
so CI and `scripts/CheckAxioms.lean` cover them. Everything below is pushed.

### Done (builds, nothing forbidden, axioms only propext / Classical.choice / Quot.sound)
- `Handlers/KeyEnc.lean`, the storage-key encoder (33843):
  - `kb_call`: one call under any `HeapHost` at cap ≥ 2²⁷. Either `alloc` gives a block ptr and the
    run returns with `Vec {c, ptr, keyEnc.len}` at out, the octets `keyEnc μ kp t` at ptr, and
    `HeapCtxC` kept for the new state; or `alloc` fails and the run reaches the trap at 34070.
  - Pieces: `kb_pre`, `kb_vec`, `kb_t1`, `kb_t2a`, `kb_t2b`, `kb_epi`, `KVec` / `kb_ext` /
    `KVec.store44` / `KVec.init`, `kb_body`.
- `Handlers/KeyBuf.lean`, the fixed-buffer encoder (51243):
  - `kf_call` writes the same `keyEnc` octets into a 35-octet buffer and returns ω₇ = buf and
    ω₈ = len. The trap at 51348 is dead.
- `Handlers/RemoveCall.lean`, the SDK's `remove` (48481) as an `accContractS` run: `rm_full` (FULL →
  the trap at 48533, quirk Q18) and `remove_call` (FULL traps; otherwise ω₇ = 1/0 for a removed/absent
  value, account := `writeSelf self key []`). Assumes old values < 2⁶³ octets (`ValuesFit`).
- `Handlers/ResStore.lean`, `rs_pre` (36170's prologue, to the `alloc` call).
- `Handlers/HeapKeep.lean`: local copies of `keep_hi`, `keep_data` and `heapC_writable_data`, so KeyEnc
  doesn't import the Inputs modules. T2-inputs offered to move them to a shared `Acc/HeapKeep.lean`.
- Earlier: the Checkpoint, Upgrade, Designate* and Assign* pieces, `HeapLock`. `PVM/Logic/HostBound.lean`
  (unused) was dropped.

### In flight
- **Q18 PR** (`claude/bootstrap-t2-q18`): `ASem.step .remove` panics on FULL (Adam, 2026-11-15), the
  Q18 rows in `docs/bootstrap-target.md` and `docs/upstream-candidates.md`, `StepSnd` adjusted.
  Not built yet. The `ValuesFit` < 2⁶³ doc edits belong to T2-inputs, not here.
- After #200 merges, prefer the `storageGet`/`storageWrite` accessors (JAM/Account.lean) in new
  statements (storage-key re-keying, `docs/storage-key-design.md`).

### Next steps (the approved order: rows 8, 9, 11)
1. **36170, the results store** (rows 9 and 11 call it the same way):
   - The arguments: ω₇ = [sp+456] points to the results (144-octet items), ω₈ = [sp+464] is n, and
     ω₉ = sp+1568 is a tag-2 key.
   - The segments, with return addresses and their jump-table entries:
     - `rs_pre`, then `alloc` (ret 1692 → 36217, null → 36528);
     - 36217 → `prefix_any` (30977, ret 1694 → 36263);
     - n = 0 → 36405;
     - otherwise the loop 36346, per item:
       - byte 255 → extends [1] and [item+1] (ret 1700 / 1702 → 36373 / 36394);
       - otherwise extend [0] (ret 1696 → 36290), then 36299 (ret 1698 → 36335);
     - 36405 → key via `kb_call` (ret 1704 → 36432);
     - `set` 48104 (ret 1706 → 36456);
     - dealloc ×2 (1708, 1710), then the return. ω₇ is the `set` outcome's tag octet (S + 64).
2. **36299, `WorkExecResult`'s encoder.** It dispatches on the tag through the i32 table at 68264
   (target = 68264 + entry). The arms are at 30374 / 30512 / 30433 / 30438 / 30392 / 30567 / 30640
   (tags 0–6), per the Vec session's parse; CodeA has them.
   - Use the Vec session's HeapHost Encode names (`extendHG`, `prefixHG`, `encode_okMH_bigG`, …),
     coming on `claude/decode-heaphost`.
   - Take the RO words 68264…68291 as T1's vendored-blob facts (VendoredFacts / FmtRO). Ask T1
     (session_017ptjPBNFBKAwfdirTGg1oY) for the definition, and T2-inputs for accumulate's carriage.
3. **Row 8 (8040 … 8471):** 33843 (`kb_call`) → 34377, the typed get (`get_call` on a heap key) →
   51243 (`kf_call`) → `remove` 48481 (`remove_call`, done) → alloc → `set` 48104 (`set_call`) → dealloc.
   Map from CodeA (2026-11-15; return address → jump-table target):
   - 8031 … 8046: save ω₅, ω₆ (sp+64, +56); ω₈ := key ptr, ω₇ := sp+32; `kb_call` with ret 1610 → 34637
     (a separate function, range (34637, 35072), not 8049). 8049 is entered from elsewhere: ω₅ := ω₈
     unless ω₇&1 = 0 (then 0): the counter c, 0 if absent.
   - 8056 … 8073: tag-1 key {1, c} at sp+1568; 34377 (typed get of the ring slot) out sp+1144,
     ret 280 → 8079. Slot empty ([sp+1144] u16 = 0) → 8172.
   - 8086 … 8158: slot holds (p′, k′): a tag-2 results key at sp+1568 (32 octets from sp+1146, i16 from
     sp+1178), a zeroed 32-octet buffer at sp+744; `kf_call` (ret 282 → 8165), then `remove` 48481
     (ret 284 → 8172).
   - 8172 … 8263: key {1, c} again; (package, k) copied to sp+1144 (32 octets from sp+512, u16 from
     sp+176); an inlined callee prologue (ω₀ := 286, sp −= 96) that allocs 34 octets (40494, ret 1490
     → 32414, the encoder's body, range (32414, 32727)), returning to 8266 via 286.
   - 8266 … 8316: ω₇&255 must be 255 else panic (15361); then 2·C·I from read-only data
     (u16 at 196616, u64 at 196696), panic if 0; c′ := (c + 1) mod 2·C·I (8320, 8323).
   - 8326 … 8369: counter key {0} with c′ (u32 at sp+1000); `kb_call` (ret 288 → 8348); `set` 48104
     (out sp+744, value sp+1000, 4 octets; ret 290 → 8376).
   - 8376 … 8412: dealloc the key buffer if its cap ≠ 0 (40613, ret 292 → 8402); `set`'s result must
     not be Err (−1) else panic (15361).
   - 8416 … 8471: row 9 begins: the tag-2 key K at sp+1568, results ptr/len from sp+456/464, 36170.
   **196616 / 196696 are NOT blob data**: they are statics written at runtime by the entry prologue's
   `apply()` of the fetched protocol parameters (fetch kind 0): `storeU16 3 196616` at 56279,
   `storeU64 11 196696` at 56205 (Code.lean; outside every fnRangesA range). The rw statics
   196616 … 196791 are written only there (other absolute stores: 196608, the allocator word, and
   206848). So no `accRwOk`/initial-memory fact applies. Reported to @parent 2026-11-15 with options
   (a) a premise `ParamStatics μ C I` on row 8's summary, established by the T2 composition (prologue +
   frames), or (b) prove apply()'s stores now (needs a CodeA range). **Decided (parent, 2026-11-15): (a).**
   Row 8's summary takes `ParamStatics μ C I` ([196616]₂ = C, [196696]₈ = I) as a premise in the style
   of its other memory premises; every later summary's frame must keep 196616 … 196791. The discharge
   (apply()'s stores at 56205/56279, then preserved) is an **obligation**, not an assumption of the
   final T2 theorem: record it in `docs/whats-proven.md` (in the PR that introduces `ParamStatics`) and
   here. (b), apply()'s stores and the CodeA range for 56205 … 56279, went to the T2-inputs session.
4. **Row 9:** 8471 → 36170; on Err → 15361 (☇); 8490 is checkpoint, under accContractS's 0/18 case.
5. **Row 11 (15032 … 15198):** the drops 33214 (ret 558/560) and 28864 (ret 564); 15115 → 36170;
   dealloc at 15166 and 15185; back to 6766.
6. When #150 lands: the allocation side of Designate and Assign (lock → `toL` →
   `alloc_impl0_callG` → unlock). When #163 lands: the fmt-group handlers.

### Dependencies and open decisions
- The Vec session: HeapHost versions of the Encode primitives (the parent chose option (a)).
- T1: the RO-data facts pattern for the table at 68264.
- Bless's scope is still to be agreed with the parent.
