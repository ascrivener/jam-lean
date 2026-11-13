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
- The item decode for operands from 45126 (`Acc/Inputs/ItemCall.lean`): `item_pre0`, **`item_op_ok`**,
  **`item_op_err`** (ω₀, ω₁, ω₅, ω₆ as at the call). With `tr_call` (transfers, stack only, host-generic)
  both arms are covered. PR #141.
- **Next: the loop 44916** (frame 480; `Vec<AccumulateItem>::decode` with the count n from 39710), as the
  code facts show it:
  - 44916 … 44964: prologue (ω₀, ω₅, ω₆ at sp + 472, + 464, + 456; out at sp + 0, reader at sp + 48;
    `Vec { cap 0, ptr 8, len 0 }` at sp + 64 … + 88); n = 0 → 45556 (the empty `Vec`);
  - 44965 … 45036: capacity min(n, 89) (ω₁₂ = 89), `finish_grow` 40852 (2040 → 45042) for cap·184 octets,
    align 8 (`fg_new_call`); an error → 45642 (trap);
  - 45042 … 45126: cap and ptr stored at sp + 64 / + 72, then per item: ω₇ = sp + 88 (the stack slot),
    ω₈ = the reader (sp + 48), the item decode 45126 (2044 → 45168);
  - 45168: slot word −2 (an error) → 45257 (drop the decoded items, free, error out); else memcpy
    184 octets sp + 88 → sp + 272 (2046 → 45192); len = cap → 45201: grow (`finish_grow` with a current
    block, 1990; only when n > 89, excluded by the temporary bound); 45075: memcpy sp + 272 → ptr + 184·len
    (2042 → 45103), len += 1, count −= 1, loop to 44996 / 45115;
  - 45593 … 45613: the `Vec` (cap, ptr, len) written to out, epilogue, return.
  Segments done (`Acc/Inputs/Loop.lean`): `lp_pre` (44916 → 40852, n > 0), `lp_fg_ret` (41175 → 45042),
  `lp_buf` (45042 → 45126), `lp_ret_tr` / `lp_ret_op` (47072 / 47332 → 45168), `lp_chk` (45168 → 68729,
  then `memcpy_big_aligned` 184 octets, 2046 → 45192), `lp_step` (45192 → 68729, then memcpy into
  q + 184·L, 2042 → 45103), `lp_next` (45103 → 45126, count > 1), `lp_last` (45103 → 45613, count 1:
  `Vec { n, q, L + 1 }` at out). **Next:** n = 0 (44952 → 45556 → 45613); then the induction over the
  items: an invariant "after L items, len L at s + 80, the buffer's first L slots hold the decoded
  items, the reader past them, `HeapCtxC` for the current state", one step = item decode (`tr_call` lifted
  by `keep_hi`, or `item_op_ok` / `item_op_err`) + `lp_ret_*` + `lp_chk` + memcpy + `lp_step` + memcpy.
  Statement plan for the induction, in T1's `ElemOkAF` style (`Decode/LoopA.lean`): a per-item contract
  `ItemOk env cap pb enc Rep` = from 45126 with the reader holding `enc` (inside an allocated chunk), the
  stack slot `out` and `HeapCtxC`, either the run reaches the item's `jumpInd` (47072 / 47332, so a
  `Fin 2`/address parameter or an existential end point) with ω₀, ω₁, ω₅, ω₆ restored, the slot's first word
  ≠ −2, `Rep (slot octets) μ''` for every μ'' agreeing on the item's fresh chunks, the context for a new
  state keeping the old chunks and their data, the reader advanced by |enc|; or Exhausts (an `alloc`
  failure reaching 45975). Instances: `tr_call` (no chunks), `item_op_ok`, `item_op_err`. The loop
  theorem then takes a list of (enc, Rep) with `ItemOk` each, n = the list's length ≤ 89.
  Done (`Acc/Inputs/LoopItem.lean`, `LoopItemOp.lean`): `ItemOk`, and its instances `itemOk_tr`
  (`encTr`, `RepTr`), `itemOk_opok` (`encOpOk`, `RepOpOk`), `itemOk_operr` (`encOpErr`, `RepOpErr`);
  helpers `readN_app`, `Words4.readN`, `blk`, `VAlloc.blk_mem`, `blk_read`, `wd`.
  Done (`Acc/Inputs/LoopInd.lean`): `HeapCtxC.keep_data`, `lp_body` (one item and its two copies),
  `lp_items` (the induction), `lp_buf_err`, and **`lp_call`** (44916 → 45613, 0 < n ≤ 89): `Vec { n, q, n }`
  at out with slot j satisfying item j's `Rep`, the buffer a fresh chunk, the context kept with every old
  chunk and its data; or exhausted (45975, or the trap 45642 when `finish_grow` fails). n = 0: `lp_empty`.
  **Next:** 44495's glue (the fetched bytes unwrapped, the count by `decodeU32A`, `lp_call`, the fetched
  buffer freed at 42327 with the allocator's lock inline, the result stored, return 2022/226 → 6674),
  `fetch_vec`'s zeroed allocation (a′), then the 6630 → 6674 summary.
  **44495's glue, as the code facts show it** (in 6630's 144-octet frame, sp): ω₆ = the fetched `Vec`'s
  cap (sp + 56; −1 = the fetch's error niche → trap 44676); ptr at sp + 64, len at sp + 72; the reader
  {ptr, len} at sp + 104 / + 112; `decodeU32A` (2024 → 44527; its error bit → trap); ω₉ = n,
  ω₇ = sp + 80 (out), ω₈ = sp + 104, `lp_call` (2026 → 44552); the result's cap −1 (an error) → trap;
  ptr, len to sp + 16 / + 24; if the fetched cap ≠ 0: the lock (196792 + 10056, spin), `dealloc` 42327
  (2028 → 44632) of the fetched buffer, unlock (196792 + 8192 + 1864); then `Vec { cap, ptr, len }` at
  *(sp + 8) and the return through sp + 136 (226 → 6674). The free needs a `HeapCtxC`-level dealloc:
  handlers-a is writing `dealloc_callG` (`Decode/DeallocCall.lean`); use it.
  Segments done (`Acc/Inputs/Glue.lean`): `g_pre` (44495 → 39710), `g_mid` (44527 → 44916), `g_ret`
  (45613 → 44552), `g_post` (44552 → 44591, the lock about to be taken), `g_end` (44641 → 44674). Waiting
  on the dealloc for 44591 … 44640.
  **(a′) `fetch_vec`'s zeroed allocation:** `alloc_impl` stores ω₁₀ (the zero flag) at its frame + 112;
  the tail (42074 … 42128) computes ω₁₀ := flag ∧ ω₁₀ and, when nonzero, tail-calls `memzero` 70133 on
  the block (returning to the caller), else returns at 41404. The existing proofs fix the flag 0
  (`h112 : rdN μ (sp + 112) 8 = 0`, `bitwise_and_zero` in `Alloc/AllocTail.lean`). Since `fetch` then
  writes all L octets of the block, the zeroing does not affect the result: it suffices to show both
  tail branches keep `HeapCtxC` (memzero writes only the block's data and its stack frame, so
  `HeapCtxC.keep_data`). This means a flag-generic copy of the `alloc_impl` chain (`AllocTail`, then the
  `alloc_callG` composition) in new `AllocZeroed*.lean` files, keeping the flag-0 lemmas as they are.
  **Link to the spec (planned).** The top-level T2 assembly instantiates the list from the model's
  accumulate inputs: for each of the paper's items (GP v0.8.0 §12: an operand 𝕌 or a deferred
  transfer 𝕏), `enc` is its ℰ encoding (Appendix C: tag 0 then ℰ(p, e, a, y, g, O(l), ↕t), or tag 1
  then ℰ(ℰ₄(s), ℰ₄(d), ℰ₈(a), m, ℰ₈(g))), so ℰ(↕**i**) = ℰ(n) ⌢ enc₁ ⌢ … ⌢ encₙ is what `fetch` kind 14
  returns, and `Rep` is the slot layout of that item (the transfer layout of `tr_call`, the operand layout
  of `item_op_ok` / `item_op_err`). The per-item `ItemOk` facts come from those three theorems; the
  model-side function from items to (enc, Rep) is written there, next to the model's types.
  Then 44495's glue and the 6630 → 6674 summary.

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
