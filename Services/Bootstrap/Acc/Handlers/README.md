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
