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

**Log sites** (`AccLog/`, frame-only: termination and the frame, not the message):
- `AccLog.ItemLog.item_fmt_site`: T2's item log line, 6955 → 7009 (`format!` of the template at 66266
  "Accumulating work item from {}", `log` (100) at 6987, the `String`'s dealloc at 7002). Hypothesis `hA`
  (`ArgsAt … itemTmpl`), the argument at sp + 1144: **discharged by ArgOk(56340)** (fmt-4).

The `format!` (59375) sites of the handlers, the formatters their arguments need, and whether they
already have `ArgOk`: hex32 60525, dec32 68146 and dec64 68449 do. The formatter addresses are read from
the jump table at 11888 + 6 + 3i and loaded within 40 instructions before the call; "?" means none was
found that close.

| Site | `format!` pc | Template | Text | Formatters |
|---|---|---|---|---|
| Imported | 9116 | 66312 | "Imported data {}" | 37897 (no ArgOk) |
| Yield | 9380 | 66083 | "Yielded hash {}" | 37996 (no ArgOk) |
| Eject | 9527 | 66618 | "Ejecting service #{} with code_hash {}" | 56340 (fmt-4), ? |
| Lookup | 11043 | 66297 | "Lookup, got {}" | ? |
| Exported | 12414 | 66747 | "Exported {} items" | ? |
| Import / RandomStorageRefine | 12535 | 66055 | "Instruction not handled: {}" | ? |
| Designate | 13242 | 66555 | "Designated keys {}" | 38706 (no ArgOk) |
| Solicit | 14062 | 66688 | "Solicited {} of length {}" | 56340 (fmt-4), ? |

Each handler log-site lemma takes an `ArgsAt` hypothesis like `hA`, discharged by the formatters' `ArgOk`.
They are `AccLog.<Site>.lean`, theorem `<site>_fmt_site` (from the `format!` call to the end of the
`String`'s dealloc: 9116 → 9165, 9380 → 9429, 9527 → 9576, 11043 → 11092, 12414 → 12463, 12535 → 12584,
13242 → 13291, and 14062 → 14553 for Solicit). `scripts/gen_acc_log_site.py` writes them from
`Imported.lean`; `Solicit.lean` is then edited by hand, since its dealloc returns to a jump to 14553.
Their hypothesis `hA` is **discharged by ArgOk** of the formatters in the table above.

**Handoff (2026-11-14): what is left for the log sites.**
- **ArgOk(56340), and 57346, queued after fmt-4 (#170).** fmt-4 adds a stack depth Z to
  `ArgOk`/`ArgsAt`/`format_inner` and a premise W + 24 ≤ spA. Then:
  - prove `ArgOk … 56340 v M C` for v pointing at 32 readable stack octets (the `[u8; 32]` Debug, jump-table entry
    2502), with constant M and C;
  - add `argsAt_item`, which builds `item_fmt_site`'s `hA` from T2's facts at 6955.
  - T2's facts come from `op_mid` (6866 → 6955, `Acc/Items/Operand.lean`, branch `claude/bootstrap-t2-inputs-wip`):
    `rdN μ (S + 1144) 8 = S + 312`, `rdN μ (S + 1152) 8 = 2502`, readability of [S + 1144, S + 1160) (HeapCtx `st`),
    and the 32 octets at S + 312 = the operand's first hash.
  - Eject and Solicit (and Created service, 12789) need the same 56340.
- **fmt-4's signature change.** Whichever of fmt-4 and the handler log sites lands second updates them:
  - in `Imported.lean`: `ArgsAt … S0 S1 600 μ …` and `format_inner … S0 S1 600 (Nat.le_refl _) HA HR …`;
  - then rerun `scripts/gen_acc_log_site.py` (the arguments are in each file's docstring and the table above);
  - then re-edit `Solicit.lean` by hand.
- **Formatters with no owner yet:**
  - 37897 (Imported), 37996 (Yield) and 38706 (Designate);
  - the formatters of Lookup (11043), Exported (12414) and Import (12535) are still to identify. Their argument
    pair is set up more than 40 instructions before the call.
- **on_transfer's log line (T2, `LogFmt p env pb S0 S1`, `Acc/Transfer/Hyp.lean` on `claude/bootstrap-t2-inputs-wip`).**
  - The call: `format!` at 7692 (return 262 → 7699), template 66221 "Received transfer from {} of {} with memo {}",
    ω₇ = sp + 744, ω₉ = sp + 1568.
  - Three argument pairs, each with a constant formatter word read off the code:
    - (sp + 472, 2800): u32 Display, entry 2800 → 68146 (dec32), which already has ArgOk;
    - (sp + 1000, 2804): u64 Display, entry 2804 → 68449 (dec64), which already has ArgOk;
    - (sp + 512, 678): `String` Display, entry 678 → **17596**, which has no ArgOk yet. This is not 57346.
  - Premises: `HeapCtxC env.code pb S0 S1`, S0 + 4096 ≤ sp, sp + 1856 ≤ S1, 2^31 ≤ sp.
  - T2 needs the out String's fresh chunk (for the dealloc at 7756), HeapCtxC kept, ω₁/ω₅/ω₆ kept, and only
    [sp + 744, sp + 768) changed from sp up; or Exhausts.
  - `format_inner` gives this given `ArgsAt`. After fmt-4, restate the premises in fmt-4's form and tell T2, who will
    adapt the call site.

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

- `AccumulateItem::decode` (45126, frame 424), its entry and the transfer arm (`Acc/Inputs/Item.lean`):
  segments `it_pre` … `it_tr_fill`, stages `tr_s1` … `tr_s4`, and **`tr_call`** (45126 → 47072): a
  deferred transfer's 153 octets at ip into the slot (−1 at + 0, memo at + 8, amount + 136, gas + 144,
  source + 152, destination + 156).
- The `u64` compact decoder 46856 (body 39982 … 40212; `Acc/Inputs/CompactU64*.lean`): segments
  `cu_head`, `cu_mid` (the leading-ones cascade, l < 8), `cu_post`, `cu_zero`, `cu_ff`, `cu_ff_post`;
  `cu_pre`, `cu_tail_mid`, `cu_tail_ff`; and **`cu_call`**: from ℰ(g) at the reader, ω₈ = g
  (return address 2106 → 46889).
- The operand arm's segments (tag 0; `Acc/Inputs/ItemOperand*.lean`, not yet imported by `Services.lean`):
  - `op_h0` … `op_h4` (46300 → 46856): the four hashes, each read by `read_ok` (32 octets into b + 272,
    returns 2084 / 2086 / 2088 / 2090) and copied to b + 32, + 64, + 96, + 136; `op_h4` calls 46856 (2106);
  - `cu_call` (the gas g), then `op_res` (46889 → 58434): g to ω₅, the result's tag octet read (2108);
  - tag 0: `op_t0` (46920 → 39634, `vv_call` for the output, 2114), `op_ret1` (39708 → 47086), `op_ok`
    (47086 → 39634: output length, capacity, pointer to b, b + 8, b + 16, using `repack` / `rd8_split`;
    `vv_call` for the trace, 2116);
  - tags 1 … 6: `op_te1` (46920 → 58434; `read_ok` of t from the one-octet reader {b + 135, 1}, 2110),
    `op_te2` (46974 → 39634: −1 at b + 8, t at b + 16; `vv_call` for the trace, 2116);
  - `op_ret2` (39708 → 47158), then `op_fill1` … `op_fill3` (47158 → 47332): the slot. Operand slot:
    + 0 trace capacity, + 8 trace pointer, + 16 trace length, + 24 the result's capacity (−1 for an
    error), + 32 its pointer (the tag for an error), + 40 its length, + 48 p, + 80 e, + 112 a, + 144 y,
    + 176 g.
- The operand arm composed (`Acc/Inputs/Operand{Head,Call,Arm}.lean`, not yet imported by `Services.lean`):
  - `op_head` (46300 → 46889, host-generic): the four hashes (as `Words4`) and the gas;
  - `vv_any`: the `Vec<u8>` decoder for 0 … 16384 octets (`VAlloc`: nothing for 0, else a fresh block);
  - `op_mid_ok` (heap contract), `op_mid_err` (stack only; `read_ok_adj` for the one-octet reader at
    b + 272 with its buffer at b + 271), `op_end` (the trace and the slot, 39634 → 47332);
  - **`op_call_ok`** and **`op_call_err`** (46300 → 47332): the slot from the reader's ℰ(p, e, a, y, g,
    O(l), ↕t), or an allocation failure reaching 45975 (Exhausts). `HeapCtxC.keep_hi` carries the context
    over stack-only steps.
  - Checked against the loop: 44916 decodes each item into its own stack buffer (sp + 88), then copies the
    184 octets into the `Vec` (memcpy at 45097), so `out` on the stack is right.
- **Next:** the item decode from 45126 (it_pre, the tag read, then `tr_call` / `op_call_ok` / `op_call_err`,
  with ω₀, ω₅, ω₆ restored to the caller's), then the loop 44916 (≤ 89 items), then 44495 and 6630 → 6674.

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
