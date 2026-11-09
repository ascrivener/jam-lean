# Bootstrap's accumulate: entry, control flow and checkpoints

This page maps the accumulate entry of `services/bootstrap/jam-bootstrap-service.jam`, as
groundwork for T2. Every address is a PVM instruction index in the blob. It was read off the
blob as follows:
- its disassembly;
- runs of Ψ_A in this model (`psiM` at instruction 5 with `accHostFn`, `Params.full`) on 31
  inputs: one operand for each `Instruction` variant, one operand holding all of them, an
  undecodable work output, and an incoming transfer.

Every run ends as the source predicts. Three of them end in ☇: `Panic`, `Bless` when bootstrap is
not the manager, and the undecodable output. The others halt with (ω₇, ω₈) = (0, 0). No proof
here depends on this page; it says where the proofs have to go.

## Entry

Instruction 5 is `jump 6378`. The accumulate entry is one function at 6378 … 15368, with a frame
of 1856 octets (sp = 4278057152 after its prologue). `on_work_item`, `on_transfer` and
`on_instruction` are inlined into it. Every Rust panic and failed `unwrap` jumps to 15361
(`unimp`, ☇).

| Where | What |
| --- | --- |
| 6398 → 44241 | SDK setup: `fetch` (2) of the protocol parameters (kind 0), then their check. The same code as refine's, and already in `Code.facts`. |
| 6429, 6451, 6473 → 31894 | t, s and \|**i**\| decoded from the arguments by the compact `u32` decoder (`DecodeU32`). |
| 6501 → 49454 | `info` (6) of the service itself, for the first log line, then `format!` (59375) and `log` (100) at 6608. |
| 6634 … 6670, 44495 … | The inputs: `fetch` (2) of kind 14 (ℰ(↕**i**)) in two phases (47541: length, then data). Then the `Vec<AccumulateItem>` decoders (39710, 44916 and their callees 45075, 45126, 45643, 46856, 39634) decode them into 184-octet slots. |
| 6674 … 6782 | The items loop. The word at slot + 0 selects: −1 → 7159, the transfer path (`on_transfer`); −2 → 15215, the end; anything else is an operand. |
| 7009 | Operand with a work error (the word at +288 is −1): skipped (15191). |
| 7073 → 31894 → 22145 → 482 | `BootstrapWorkOutput::decode`: the compact length, then the **same `Vec<Instruction>` loop as refine's** (680, 723, 562; elements by `Instruction::decode` at 20626, as in `Decode/Loop.lean`), then k as a `u16` (22206 → 58434). The results `Vec` is allocated with capacity n (7138, `alloc(144·n)`). |
| 8073 → 34377 | `add_recent_work_item`: `read` (4, wrapper 47857) of the counter and of the ring slot, removal of the old results, `write` (5, wrapper 48104) of the slot and of the counter. |
| 8471 → 36170, 8490 | Empty results written under `InstructionResults(p, k)`, then **`checkpoint` (18) at 8490**. |
| 8490 … 15032 | The instruction loop and the inlined `on_instruction` dispatch. Each instruction is formatted and logged, then run, and its result appended. Instruction `Checkpoint`: the results so far are written (36170), then **`checkpoint` at 9944**. `Benchmark`: **`checkpoint` at 11889** in its loop. |
| 15032 … 15185 | Unless the list holds a `Zombify`, all results are written (36170); then drops. |
| 15215 … 15359 | End of the items: the halt at 15359 with (ω₇, ω₈) = (0, 0), so Ψ_A takes no yield from the output. |

**Host calls made inline in 6378 … 15368:** `checkpoint` 8490, 9944, 11889; `new` 9029;
`provide` 9262, 12676, 12879; `yield` 9345; `eject` 9584; `forget` 10910, 14236; `lookup` 11008;
`gas` 11330, 13011; `transfer` 11551, 13111; `query` 11620; `solicit` 11712; `upgrade` 11792; and
`log` (100) at many sites.

**Host calls made out of line:**
- `fetch` at 47490, 47690, 47742 and 44793;
- `read` at 47886 and 48077;
- `write` at 48132, and 48493 (remove);
- `info` at 48547;
- `lookup` at 48454, 49263 and 49427;
- `bless` at 35011, `assign` at 32684 and 40397, `upgrade` at 46210, `designate` at 49874;
- `grow_heap` (1) in the allocator.

## Reuse of the refine proofs

- The prefix (44241) and `decodeU32` (31894) are the same code, entered with the same kind of
  arguments.
- The `Vec<Instruction>` loop and `Instruction::decode` are the same code, but **at a different
  stack pointer**:
  - at 680, sp is 4278056528 in accumulate and 4278057688 in refine, a difference of −1160;
  - `DecodeLoop`, `Decode/Loop.lean` (`ElemOk`, `pass`, `loop`) and the per-variant `ElemOk`
    proofs state refine's absolute stack addresses;
  - for accumulate they are needed with every stack address moved by −1160. The tag table (67476)
    and the heap addresses are absolute or already parameters.

## Checkpoints and rollback

What the model does (`Checkpoint.lean`; GP v0.8.0 eq. `accinvocation`, Ω_C):

- **y changes only at `checkpoint`** (`dispatch_ctx_snd`). Every host call keeps the exceptional
  dimension y, except `checkpoint` (18) when it does not run out of gas: that sets y to the
  current x (`dispatch_checkpoint`).
- **Ψ_A reports x after a halt and y after ☇ or ∞** (`psiARun_eq`).
- So if a run ends in ☇ or ∞, Ψ_A's state, transfers, yield and provisions are those of x at the
  last `checkpoint` that succeeded, or of I(**e**, s) if there was none. `write` and the other
  accumulate host functions change x at once, so a checkpoint commits every effect made before it.

What the binary does there:
- it checkpoints once per operand, after recording the item in the ring and writing its empty
  results (8490);
- it checkpoints at each `Checkpoint` instruction, after writing the results so far (9944);
- it checkpoints after each of `Benchmark`'s 1000 writes (11889).

So after ☇ or ∞, the stored results of the operand that was running are those of its last
`Checkpoint` instruction, or the empty list.

## Code facts

From 6378, 18,050 instructions are reachable statically. 5,537 of them already have
`Code.facts` or `CodeX.facts`. The rest, in three tiers:

- **A**, about 6,300 instructions: the entry, the inputs fetch and decode, the output decode, the
  ring and results helpers, the storage wrappers and the allocator's remaining paths.
- **B**, about 300 instructions: the out-of-line parts of `Bless`, `Assign`, `Upgrade` and
  `Designate`.
- **C**, about 5,900 instructions: logging and `core::fmt` (step 5 of the plan).

## Proved so far, and what comes next

**Proved** (gas-free runs under `accContract`, `Contract.lean`):
- `Start.start_from_Y`: from Y's state (`standardInit`, the deployed layout) at instruction 5 to 6429, in
  3420 steps. This is `AccPrefixC` and `AccBParams`, generated by `genwitnesssteps` with `WITNESS_ACC=1`.
- `Start.start_to_6501`: on to the call at 6501, through the decodes of t, s and |**i**| (`Args.args_run`).
- `Args.fmt_setup`: 6508 → 6580, the arguments of the first log line's `format!`.

**Owned by another session:**
- the `info` call (6501 → 6508, a frame-only summary);
- the `format!` call (6580 → 6587) and other logging.

**Next: the inputs**, from 6630 to the items loop at 6674. The traced call sequence is:
1. 47541: `fetch` of kind 14, ℰ(↕**i**), in two phases (length, then data into a fresh buffer from 41177);
2. 39710: the list length;
3. 44916: the `Vec<AccumulateItem>` decode. It calls 40852 / 41016 to allocate 184 octets per item, then
   decodes each item:
   - a transfer: reads 58434, a memzero 70133, a `u64` 46040, memcpys 68729;
   - an operand: four hashes (58434 with 68729), the gas (39634 / 39710), and two `Vec<u8>` (45643: the
     work output and the authorizer trace);
4. 42327: frees the fetched buffer.

These are decoders over symbolic data, like T1's, at accumulate's stack. They should reuse T1's
frame-base `ElemOkF` pattern (#120) where the code is shared.
## The inputs decode, 6630 → 6674, as the code facts show it

- **6630 … 6670** inline the prologue of the inputs function (frame 144, return address 226 → 6674,
  the output at the caller's sp + 1568). It stores the kind 14 at sp + 32 and tail-calls the SDK's
  `fetch_vec` at 47417 (out = sp + 56, its arguments at sp + 32), returning through entry 2022 to
  44495.
- **47417, `fetch_vec(kind)`**: kind 14 is in the no-argument mask 20359 (bits 0–2, 7–11, 14).
  - First `fetch` (47490) with a null buffer, for the length L. NONE stores `None` (−1 at out);
    any other error code traps (47844).
  - L = 0 gives the dangling pointer 1. Otherwise L ≤ 2³⁷ − 32 (else trap), then the allocator's
    lock (47578 … 47606), `alloc_impl` (41177) with ω₈ = 1, ω₉ = ⌈L/32⌉ and **ω₁₀ = 1 (zeroed)**,
    and the unlock (47631 … 47635). A null block traps at 47554 (`handle_alloc_error`), so
    allocation failure here is ☇.
  - Second `fetch` (47690) into the block, then `Some(Vec { cap: L, ptr, len: L })`. The returned
    length is not compared with L. After an error on the second call, the block is freed (lock,
    42327, unlock) and the result is `None`.
- **44495**: `None` traps (the `unwrap`). The reader over the bytes at sp + 104 gives the item count
  by **39710**, a trap on error. 39710 … 39981 is refine's `u32` decoder 31894 … 32165 moved by 7816
  (`DecodeU32A.lean`). Then **44916** decodes `Vec<AccumulateItem>` into sp + 80 (a trap on
  error), frees the fetched bytes (lock, 42327, unlock) if L ≠ 0, stores the `Vec` at the caller's
  sp + 1568 and returns to 6674. The reader is not checked to be empty, so trailing octets after
  ℰ(↕**i**) are ignored.
- **44916**: capacity min(n, 89) of 184-octet items, grown by 40852 / 41016. `AccumulateItem::decode`
  is inlined at 45115 … 45254, using the reader 58434 and memcpy 68729. The `Vec<u8>` decoders are
  45643, and 39634 (length by 39710, then 45643); 46040 decodes a `u64`, and 46856 is also called.
  None of these is a copy of refine code that is already proved.
- `alloc_impl` with ω₁₀ = 1 runs the zeroing paths (from 42098), which the refine proofs (all with
  ω₁₀ = 0) do not cover.

## Inputs decode: proved so far (branch `claude/bootstrap-t2-inputs`) and the plan

Proved, complete (`Acc/DecodeU32A.lean`, `Acc/Inputs/*.lean`):
- `decodeU32A`: 39710, refine's `u32` decoder moved by 7816.
- `fetch14_step`: one `fetch` of kind 14 under `accContractK`. `rangeWritable_of`.
- `fetch_vec` (47417), in segments: `fv_pre` (47417 → 47490), `fv_fetch1` (→ 47541), `fv_lock`
  (→ 41177), and `fv_unlock` / `fv_store` / `fv_post` (47631 → 47722).
  **Open:** `alloc_impl` with the zero flag between 41177 and 47631. Agreed: new `AllocZeroed*.lean`
  files after the HeapHost PR lands. Generalized step lemmas keep their ω₁₀ = 0 forms as corollaries.
- `finish_grow` (40852), no current block:
  - the steps `fg_entry_new`, `fg_alloc_lock`, `fg_alloc_ok` / `fg_alloc_err` and `fg_ret_jump`;
  - the paths `fg_new_hdr`, `fg_new_grow` and `fg_new_fail`;
  - `fg_new_call` on `HeapCtxC`.

Also proved since:
- `finish_grow`'s alloc path, generic in the host: `fg_new_hdr`, `fg_new_grow`, `fg_new_fail` and
  `fg_new_call`.
- The `Vec<u8>` reader (45643), one chunk: `rv_entry`, `rv_mid`, `rv_exit`, `rv_fail`, `rv_empty`,
  `read_any`, and `rv_call` on `HeapCtxC`.
- 39634's segments: `vv_pre`, `vv_mid` and `vv_post`.

**Decision (Adam via @parent):** prove 6630 → 6674 first for inputs whose `Vec`s never grow: at
most 89 items, and each work output and auth trace at most 16384 octets. These bounds are explicit
hypotheses, marked temporary. They are lifted by generalizing the realloc impl lemmas over the
return address (they fix ω₀ = 1988 / 40805) after the HeapHost PR, keeping the ω₀ = 1988 forms as
corollaries.

Plan:
1. (After the bounds are lifted.) `finish_grow`'s realloc path (a current block, 40898 … 40995 → 42980 → 41109). It needs:
   - the lock and unlock glue at these addresses, taking an `impl` run as `ReallocWrap.realloc_wrap`
     and `ReallocKeepAll.realloc_wrap_keep` do;
   - the per-case compositions with the impl-level lemmas (`realloc_inplace_refines_keep`, grow,
     grow-heap, `fallback_refines_heap_keepG`);
   - a case split as in `realloc_wrap_cases_keepG`.
2. The `Vec<u8>` reader 45643 (16 KiB chunks; the reader 58434 and `finish_grow`), and 39634
   (length, then 45643).
3. `AccumulateItem::decode`, inlined at 45115 … 45254, with 46040 (`u64`) and 46856.
4. The item loop 44916 (capacity min(n, 89), 184-octet slots), a LoopA-style proof at accumulate's
   frame.
5. 44495's glue (unwrap, count, free of the fetched bytes), then the summary 6630 → 6674.
