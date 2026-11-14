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
  (45613 → 44552), `g_post` (44552 → 44591, the lock about to be taken), `g_end` (44641 → 44674).
  The free (`GlueLock.lean`, `GlueFree.lean`): `g_lock` (44591 → 42327), `g_unlock` (44632 → 44641) and
  `g_free` (44591 → 44641) over fmt's `free_callG` (the free path with the lock held, `HeapCtxL`),
  giving `HeapCtxC` for `free s ptr` again (`heapL_release`).
  **Composed** (`GlueCall.lean`): `g_call` (44495 → 44674, 0 < n ≤ 89, under `env.rel cap`) and
  `g_call0` (n = 0, host-generic). `lp_items` / `lp_call` state each slot's `Rep` for any memory
  agreeing on the final state's allocated data off the reader's chunk (it is freed next), and the
  stack frame above sp. With `accHeapHost env` the runs lift to `accContractK` (`FreeStepsH.ofAccGrow`).
  **The model link** (`InputsSpec.lean`): `itemOf` maps each of the model's accumulation inputs (GP v0.8.0
  §12: an operand tuple 𝕌 or a deferred transfer 𝕏) to its loop item; `itemOf_enc` (its encoding is the
  model's `AccumulateInput.encode`), `itemOf_ok` (an `InputSized` input is an `ItemOk` item),
  `inputsEnc_items` (ℰ(↕**i**) is the one-octet count and the items' encodings, for < 128 inputs) and
  `g_inputs` (44495 → 44674 stated for `aenv.inputs`).
  **`fetch_vec`** (`InputsPre.lean`, `FetchVecCall.lean`): `in_pre` (6630 → 47417), `fv_call` (47417 → 47722
  over the zeroed `alloc_implZ_callG`, the lock held as `HeapCtxL`; `heapL_release_data` gives `HeapCtxC`
  back after the second `fetch`), `fv_null` (no block: the trap 47554), `fv_ret` and `in_ret`.
  **The summary** (`Inputs.lean`): `inputs_decode`, 6630 → 6674 under `accContractK`.
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

## T2: the whole path, step by step (plan)

The target is `accumulate_spec` (`docs/bootstrap-target.md`, T2). Ψ_A's state, transfers, yield and
provisions are those of `Spec.accumulate C t` run for some n host operations under `ASem`, from
I(**e**′, s), where **e**′ is **e** with the incoming transfers credited. The binary side is a
chain of gas-free runs under the accumulate contract, lifted to Ψ_M at the end. Each step's run ends
in one of three ways:
- it reaches the next step's start;
- it reaches the halt at 15359;
- it traps (☇, the panic or exhaustion outcomes). The lift turns a trap into "the spec stopped at its
  last checkpoint".

| # | Binary | Statement (proved, or to prove) | Spec side | Owner | Status |
| --- | --- | --- | --- | --- | --- |
| 1 | 5 → 6501 | `Start.start_to_6501`: the SDK setup and the decodes of t, s and \|**i**\| (`Args.args_run`) | none (no effect) | T2 start | merged (#122, #124) |
| 2 | 6501 → 6630 | `acc_log_line`: `info` (6) of this service and the first log line; frame-only, with `info_self` | `myInfo` needs no `AOp`: the spec does not log | fmt | #145 open |
| 3 | 6630 → 6674 | `inputs_decode`: `fetch_vec(14)`, the n items into 184-octet slots holding `itemOf` of each input, or Exhausts | `op AOp.fetchItems` and `decode (Dec.vec Dec.item)` | T2 inputs | #152 open (bounds: ≤ 89 inputs, blobs ≤ 16384 octets) |
| 4 | 6674 … 6782 | **items loop**: the induction over the slots; the word at slot + 0 selects the transfer path (−1 → 7159), the end (−2 → 15215) or an operand. The invariant is the `Prog` continuation `for it in rest` | `for it in items` | unowned | gap |
| 5 | 7159 … | **`on_transfer`**: the counter under "transfer-count" read and bumped, then ℰ(s, a, memo) written | `onTransfer` | unowned | gap |
| 6 | 7009 | operand with a work error: skipped (15191) | `.work _ none => pure ()` | unowned (with 4) | gap, small |
| 7 | 7073 → 31894 → 22145 → 482 | **the output decode** `BootstrapWorkOutput::decode`: refine's `Vec<Instruction>` loop at sp − 1160 (the frame-base `ElemOkF` pattern), then k as `u16` | `Dec.output`; undecodable → panic | T1 decoders (frame-moved) | gap: needs the frame-base `Loop`/`ElemOk` |
| 8 | 8073 → 34377 | `add_recent_work_item`: `read` / `write` of the ring and counter | `addRecent` | unowned | gap |
| 9 | 8471 → 36170, 8490 | empty results stored, then `checkpoint` | `store …; op AOp.checkpoint` | unowned (with 4) | gap; `checkpoint` is in `accContractC` (#140) |
| 10 | 8490 … 15032 | **the instruction loop**: per instruction, the log line (`format!` 59375, `log`), the dispatch and its handler to the shared tail 14278, the result appended | `onWorkItem`'s loop, `onInstr` per `Instr` | Handlers A (handlers); fmt (log lines); loop itself unowned | handlers partly (#129, #131, #151); loop gap |
| 11 | 15032 … 15185 | the results written (unless a `Zombify`), drops (dealloc) | the tail of `onWorkItem` | unowned (with 10) | gap |
| 12 | 15215 … 15359 | the end: halt with (ω₇, ω₈) = (0, 0) | `pure ()` | unowned (with 4) | gap, small |
| 13 | lift | Ψ_M = the free run's output (`psiM_of_freeRunH_accC`, `checkpoint`'s ω₇ dead: #140), Ψ_A's outcome from x or y (`psiARun_eq`) | `ASem.outcome (ASem.run n …)` | #140 (the lift); the rest unowned | partly |
| 14 | spec | **`ASem`**, the semantics of `Prog AOp` against Ψ_A's host functions, plus `accEnv`, `credit` and `ASem.run` / `ASem.outcome` as `accumulate_spec` uses them | (all of it) | unowned | gap: not defined yet |

**Cross-cutting gaps.**
- **G1, `gas` (0) at 11330 and 13011.** See the proposal below.
- **G2, the spec side, which does not exist yet.**
  - `ASem`, `accEnv`, `credit`, `ASem.run` and `ASem.outcome` need defining (row 14).
  - So does a spec-only lemma: `decode (Dec.vec Dec.item) (inputsEnc env)` is the inputs mapped to `Spec.Item`, matching `itemOf`'s slots (`itemOf_enc` gives the encoding side).
  - `AOp.fetchItems`' docstring says kind 15, but the model's `fetch` (`JAM/Host/General.lean`) and the binary (47417 … 47722) use kind 14 for ℰ(↕**i**); kind 15 is one item. `ASem` must interpret `fetchItems` as kind 14.
- **G3, the temporary bounds.** At most 89 inputs and blobs of at most 16384 octets (one chunk) come from the `Vec` decoders' no-growth assumption. Lifting them needs the realloc generalization.
- **G4, the per-instruction log lines.** Each instruction is formatted and logged before it runs. They are frame-only (fmt), but a summary for each format is needed.
- **G5, `Benchmark`'s `checkpoint` (11889).** Its ω₇ deadness is in #140; its handler is not proved yet.
- **G6, the gas cap.** `fetch` costs 287 + 𝔊(400, L), and `hcost` is a hypothesis of `inputs_decode`. It becomes "or ∞" with the parametrized cap (#73), as for T1.

### Proposal for G1: the `gas` host call

What the code does with the result (code facts):
- 11330 `ecalli 0`, then 11331 `store ω₇ → sp + 1384`, 11335 `ω₇ := sp + 1384`, 11339 `store → sp + 1416`;
- 13011 / 13012 / 13016 / 13020: the same pattern, through sp + 1472.

So the gas left is stored, and its *address* is put in a `format!` argument slot (sp + 1416). It is
printed, nothing more. Neither transfer's gas limit comes from it:
- `Transfer`'s `transfer` (11551) takes ω₉ from sp + 1472, which was stored at 11307 from the instruction;
- `CreateService`'s `transfer` (13111) takes it from sp + 248.

So the value affects only a log line, and `log` (100) changes nothing in Ψ_A's outcome. The spec has
no gas operation, consistent with this. It cannot be pinned like `checkpoint`: the value is read
afterwards (by `format!`), so ω₇ is not dead.

Proposal:
1. **Contract.** Extend `accContractC` with id 0 answering *any* ω₇ (`accContractG`: Ω_G's outcome
   with ω₇ replaced by an arbitrary v, everything else pinned). As with `accContractCK_pins7`, it
   pins the handler except in ω₇ at ids 0 and 18.
2. **Handlers.** State the `Transfer` and `CreateService` handlers for every v. The logging
   summaries are frame-only, so they already hold for any argument value. v flows only into the log
   line, so the handlers' post-states don't mention it.
3. **Lift.** `psiM_of_freeRunH_anyG`: the real Ψ_M run is a free run under `accContractG` (at each
   `gas` call, v is the gas actually left). The free run is unique given the answers, since
   everything else is pinned. So a statement proved for every choice of answers holds for Ψ_M. This
   replaces the `DeadAfter` side condition for id 0 with "proved for all v", and no data-flow
   analysis is needed.

Cost: small for 1 and 3, which are variants of #140's `ContractC` / `CkLift`. 2 is free once the handlers carry v as a parameter.
Alternative: a data-flow `DeadAfter`-style check that ω₇'s value reaches only `format!` arguments. That is harder to state and to check.

## Proposal: `Impl`, how a binary run implements a `Prog AOp`

The items loop's body (`onWorkItem`, `onTransfer`) and everything after it interleave plain code
with host calls. So these steps need a statement form that composes along `Prog.bind`, and the
lift from it to `accumulate_spec` needs proving once.

**`Impl R p Q (i, ω, μ, c)`.** From the PVM state (i, ω, μ) with context c, the gas-free run under R
implements `p : Prog AOp α` and, when p returns a, reaches a state satisfying `Q a`. Defined by
recursion on p:
- **`pure a`:** a run to some state satisfying `Q a`, with c unchanged except by context-keeping
  host calls (`log`, `gas`, `fetch`, `info`, `read`, `lookup`). Their effect on (x, y) is the
  identity.
- **`panic`:** a run to a trap, with c unchanged as above.
- **`call op k`:** a run to the host call(s) implementing `op` (the SDK wrapper), with c unchanged up
  to that point. Then one of:
  - `ASem.step env op c = some (b, c')`, and the run continues to a state from which
    `Impl R (k b) Q` holds with context c';
  - `ASem.step env op c = none`, and the run traps.

**Composition.**
- `Impl_bind`: `Impl R p (fun a s => Impl R (f a) Q s) s → Impl R (p >>= f) Q s`.
- `Impl_for`: the induction over `for it in rest`, with `Q` the loop invariant at 6782.
- The per-wrapper lemmas (step 2 of the plan: one per `AOp`) are the `call` case.

**The lift, proved once (`Impl_spec`).** Suppose `Impl (accContractG env) (Spec.accumulate C t)
(fun _ s => s at the halt 15359)` holds from instruction 5. Then
`∃ n, ASem.outcome (ASem.run n …) = (Ψ_A's state, transfers, yield, provisions)`:
- A halt gives n = all operations, and the outcome is x.
- A trap gives `panicked`, and the outcome is y.
- Ψ_M running out of gas inside the k-th operation's host calls gives n = k − 1 (`stopped`), and
  the outcome is y. This works because y changes only at `checkpoint`, which is itself an
  operation, and the context-keeping calls between operations keep y (`dispatch_ctx_snd`).

This uses `psiM_of_freeRunH_anyG` (the `gas` proposal) and `psiARun_eq`.

**What is needed before the items loop.**
- The `Impl` definition and `Impl_bind`, small.
- `Impl_spec`, medium: an induction over p, alongside the run's host calls.
- The wrapper lemmas for the `AOp`s the loop uses: `read`, `write`, `remove`, `checkpoint`. The loop
  body then composes these with frame-only code.

## `Impl` and the lift: proved (`Acc/Impl/`)

`Impl` is adopted as above, with one change: it is **existential, over an infinite answer stream**
(`accContractS`, Handlers A's `accContractQ` with `Nat → Nat` for the list). A stream never runs out,
so runs exist and compose. The real run's answers, followed by 0s, form one such stream.

| File | What |
| --- | --- |
| `Split.lean` | `FreeRunH.of_steps`: under a self-pinning contract, a run through a known segment continues from its end. |
| `StepSnd.lean` | `ASem.step_snd`: an operation keeps y, or leaves (x, x). Only `checkpoint` writes y. |
| `Impl.lean` | `Impl` (pure / panic / call op k; wrappers pass only through y ∈ {c.y, c₁.y}, `YIn`), `Halts` (halt with ω₈ = 0), `Impl.pre`, `Impl.bind`, and `Impl.run`: a run exists and reports what some `ASem.run n` reports. |
| `Prefix.lean` | `Pre` (contexts at host calls), `Pre.split` / `split_run`, and `Impl.prefix`: the out-of-gas case. |
| `ContractS.lean` | `accContractS`, `accContractS_pins`, and `FreeRunH.toS`: every non-∞ handler run is an `accContractS` run. |
| `OogPrefix.lean` | `psiM_oog_pre`: Ψ_M out of gas returns the y of a prefix of an `accContractS` run. |
| `Lift.lean` | `impl_psiM` and `psiA_of_impl`. If `Impl … Ab prog Halts` holds from instruction 5 with (x₀, x₀) for every stream, then Ψ_A's state, transfers, yield and provisions are `ASem.outcome (ASem.run n prog …)` for some n, and either that run finished, or Ψ_M ran out of gas, or a run reached a state where a reason in `Ab` holds. That is T2's shape (the strengthened statement in `docs/bootstrap-target.md`). |
| `QtoS.lean` | Handlers A's answer lists as streams: `qs ++ₛ g`, `accContractQ_S`, `FreeStepsH.qToS`. |

**Early ☇, for a listed reason.** `Impl` takes a reason predicate `Ab`: an early ☇ needs a state on
the run where `Ab` holds. For accumulate, `Ab := AccAbort`, defined from the code facts, with these
cases:
- `heap` (decision 4, Adam): an allocation returned null (for `get`: 48047 with ω₇ = 0), or the
  size check before an allocation failed (`get`'s 47974 with the length above 2³⁷ − 32; Adam folded
  "too long" into heap exhaustion). Both reach the allocation-failure trap.
- one case per named quirk where the binary traps and the model goes on (none yet; `remove` on
  FULL is pending with Adam).

**Hypotheses on the state.** `ValuesFit (credit e s inputs) s` (`hvals`, Adam): storage values,
preimages and the encoded inputs of s are shorter than 2⁶⁴ octets. Ω_R / Ω_Y return lengths in a
64-bit register, so a longer one would wrap.

**What remains for T2:** `∀ f, Impl (accContractS env) env (Spec.accumulate C t) Halts` from instruction 5. This is built:
- from the segment lemmas: 1 → 6630 (start, `acc_log_line`), `inputs_decode`, and the items loop;
- per `AOp`, from wrapper lemmas in the call-case form: keep (x, y) to the wrapper, then the wrapper
  under `YIn`.
Lemmas stated under `accContractK` (no `gas`/`checkpoint` call) carry over with the stream kept.
Lemmas under `accContractQ` (from (x, v :: qs) to (x', qs)) carry over to any stream `cons v (qs ++ₛ g)`.

**The SDK storage wrappers** (`Acc/Wrappers/`), as runs keeping the answer stream:
- `get` (47857, `GetCall.lean`): `get_none`, `get_empty`, `get_some` (|w| + 31 < 2³⁶; or `alloc_impl`
  returned null at 48047, then the trap 47977).
- `set` (48104, `SetCall.lean`): `set_call`, one Ω_W (`write_stepS`), then `Ok(Some(len))`, `Ok(None)`
  or `Err` at out. x's account becomes `writeSelf`; y is kept.
- `remove` (48481, `Remove.lean`): segments for the old-length and NONE replies. The FULL reply
  traps (48533) and is pending with Adam (model change plus quirk Q18, or an abort reason).
- Helpers: `FreeStepsH.growS` (allocator runs under `accGrowK` keep the context), `HeapCtxL.of_lo` /
  `keep_hi` (the locked heap context survives stack writes).

**Named TODOs for the wrappers:**
- `get` for 2³⁶ ≤ |w| + 31 ≤ 2³⁷ − 32: the 32-bit unit count sign-extends and `alloc_impl` gets a
  request ≥ 2³¹ units. This needs the allocator lemma "a request ≥ 2³¹ units returns null, keeping
  the context" (asked of the Vec session); then it is `heap`.
- Read-only data: `set`'s error table (69056, 69072) and keys in rodata are hypotheses until
  `ROKeep` (gas-free runs keep non-writable octets, contract-generic) and an accumulate `roBytes`
  check land.
- Keys must survive `get`'s allocation: `get_some` takes them on the stack above the frame or in an
  allocated chunk's data.

## Brief: `add_recent_work_item` and the results tail (rows 8, 9, 11)

These go to a separate session. Both run inside an operand's iteration of the items loop, in
accumulate's 1856-octet frame (sp as at 6674). Both are stated in `Impl`'s call form: reach each
wrapper's call keeping (x, y) (`KeepCtx`), run the wrapper under `YIn`, and continue.

- **Row 8, `add_recent_work_item`** (spec `addRecent`):
  - Entry: 8073, `loadImmJump` to 34377 with ω₀ = 280, so the return is jump-table entry 139, 8079.
    The arguments: ω₇ = sp + 1144 (out), ω₈ = sp + 1568; 8061 stores the u32 at sp + 1572.
  - The function reads and writes the ring and the counter with the SDK wrappers in
    `Acc/Wrappers/`: `get_none` / `get_empty` / `get_some` (`GetCall.lean`), `set_call`
    (`SetCall.lean`) and `remove` (`Remove.lean`, FULL pending).
  - Exit: 8079 (the u16 result at sp + 1144), the allocator's context (`HeapCtxC`) for the new
    state, x's account as the spec's writes leave it, y kept.
  - Keys built with `format!` live in heap Strings: the `get` lemmas need a variant with the key in
    an allocated chunk (alloc keeps used chunks' data). `set`'s error-table hypotheses come from
    `Acc/RoData.lean` (`accRoBytes`) and `KeepsRO` (#165, `ROKeepS.lean`).
- **Row 9, the empty results and the checkpoint** (spec `store …; op AOp.checkpoint`):
  - 8471: `loadImmJump` to 36170 with ω₀ = 294 (the results store, a `set`). Then 8477 … 8481:
    an `Err` byte (≠ 255) → 15361 (☇ via `orPanic`).
  - 8490: `checkpoint` (18), under `accContractS`'s 0/18 case (the stream's head into ω₇, y := x).
- **Row 11, the results write and the drops** (the tail of `onWorkItem`, unless a `Zombify`):
  15032 → 33214 (ω₀ = 558), …, 15185 → 40613 (`dealloc`, ω₀ = 568), on to 15191 (the operand's
  remaining drops) and back to the loop head 6766.
- **Hypotheses to carry:** `ValuesFit` (values < 2⁶⁴ octets), the [2³⁶, 2³⁷ − 32] `get` band (TODO),
  and the `heap` abort reason for every allocation.

**Log sites** (the per-item line at 6955, the handlers' `format!`) are stated against a hypothesis of
`acc_log_line`'s shape: the allocator's context in and out, the format!/String region kept, or
Exhausts. They are marked "discharged by the fmt summaries". The migration session owns them.
