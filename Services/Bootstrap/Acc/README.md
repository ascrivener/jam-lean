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
