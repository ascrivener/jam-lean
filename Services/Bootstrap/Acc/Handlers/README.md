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

## Handoff (T2 handlers-a, paused 2026-11-14)

**Branch:** `claude/bootstrap-t2-handlers-a-wip`. Main and #186's branch are merged in, so CodeA has the
51243 facts. Everything below is pushed.

### Done on the branch (builds, no sorry, axioms only propext / Classical.choice / Quot.sound)
- `Handlers/KeyEnc.lean`, the storage-key encoder (33843):
  - `kb_call`: one call under any `HeapHost` at cap ≥ 2²⁷. Either `alloc` gives a block ptr and the
    run returns with `Vec {c, ptr, keyEnc.len}` at out, the octets `keyEnc μ kp t` at ptr, and
    `HeapCtxC` kept for the new state; or `alloc` fails and the run reaches the trap at 34070.
  - Pieces: `kb_pre`, `kb_vec`, `kb_t1`, `kb_t2a`, `kb_t2b`, `kb_epi`, `KVec` / `kb_ext` /
    `KVec.store44` / `KVec.init`, `kb_body`.
- `Handlers/KeyBuf.lean`, the fixed-buffer encoder (51243):
  - `kf_call` writes the same `keyEnc` octets into a 35-octet buffer and returns ω₇ = buf and
    ω₈ = len. The trap at 51348 is dead.
- `Handlers/HeapKeep.lean`: local copies of `keep_hi`, `keep_data` and `heapC_writable_data`, so KeyEnc
  doesn't import the Inputs modules. Switch to T2-inputs' versions after #152 if the import cost is
  fine; T2-inputs offered to move them to a shared `Acc/HeapKeep.lean`.
- Earlier work on this branch: the Checkpoint, Upgrade, Designate* and Assign* pieces, `HeapLock`,
  `DesignateFree`, `AssignFree` and `PVM/Logic/HostBound.lean` (possibly to drop).

### In flight
- **#186** (`claude/bootstrap-t2-codea-51243`, 81464e1): `fnRangesA += (51243, 51349)`. CI is green.
  The parent said: hold it until #166 has merged, then re-sync and merge. Don't merge before.
- **`Handlers/ResStore.lean`, `rs_pre`** (36170's prologue): the draft is **unchecked**. Its import,
  `Encode.VecCore`, wasn't built locally. Build that, then check `rs_pre`.

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
   51243 (`kf_call`) → `remove` 48481 → alloc → `set` 48104 → dealloc. Needs #166.
4. **Row 9:** 8471 → 36170; on Err → 15361 (☇); 8490 is checkpoint, under accContractS's 0/18 case.
5. **Row 11 (15032 … 15198):** the drops 33214 (ret 558/560) and 28864 (ret 564); 15115 → 36170;
   dealloc at 15166 and 15185; back to 6766.
6. When #150 lands: the allocation side of Designate and Assign (lock → `toL` →
   `alloc_impl0_callG` → unlock). When #163 lands: the fmt-group handlers.

### Dependencies and open decisions
- #150 → #152 → #166 (get, set, remove) → then #186.
- The Vec session: HeapHost versions of the Encode primitives (the parent chose option (a)).
- T1: the RO-data facts pattern for the table at 68264.
- Bless's scope is still to be agreed with the parent.
