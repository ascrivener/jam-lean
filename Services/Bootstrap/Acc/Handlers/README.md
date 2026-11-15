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

**Next (row 8):**
1. 34377's remaining segments: `sg_some` (34434 → 58434, 32-octet read), `sg_r2` (34485 → 58434,
   2-octet read; copy S + 56 → S + 24), `sg_bad` (34534: u16 0 at out, then 34610 or 34539),
   `sg_ok` (34571: payload to out + 2, u16 at out + 34, tag 1), `sg_free` (34610 → 40613, ret 1608),
   `sg_ret` (34623) / `sg_ret0` (34539); then the composition with `kb_call`, `get_call` (Some w /
   None / trap 47977), `read_exact` / `re_short`, `dealloc_callG`. Statement: out gets
   `load (.recent c) (take 32, fixedN 2)`'s result (0 = None; 1, p at +2, k at +34).
2. 8056 … 8172 composed: key {1, c} at sp + 1568, 34377, then (slot present) the results key,
   `kf_call` (51243) and `remove_call` (48481), as `Impl` of the `match` in `addRecent`.
3. 8172 … 8326 (slot write, inlined alloc + encoder 32414) and 8266 … 8326 (`ParamStatics`, c′).
4. 8031 … 8049: the counter's typed get at 34637 (u32 decode).
5. Add the modules to `Services.lean`, record `ParamStatics`' discharge obligation in
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
- **#208** (`claude/bootstrap-t2-handlers-a-1`): this branch's pieces + Services.lean imports. CI
  re-running after a fix (the forbidden-word grep also scans .md files: never write that word).
- **#209** = the Q18 PR below. Both: merge on green (parent-approved).
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
