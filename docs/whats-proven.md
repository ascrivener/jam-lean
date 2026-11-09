# What's proven

This page is for people evaluating this repository, such as Polkadot Fellowship reviewers,
retro-funding committees and JAM implementers. It says what is proved, about what, under which
assumptions, and how to check it. It describes `main` as of PR #67 (2026-11-07). Work still in
progress is listed at the end. Every theorem named below exists on `main`, and the trust base
below covers all of them. Where a result is only partial, the text says so.

## Overview

jam-lean is an executable Lean 4 model of the JAM protocol, written from the Gray Paper v0.8.0.
It covers all of Appendix A (the PVM, its host-call machinery and its gas model) and the parts of
Appendix B and the protocol that the PVM needs (codec, hashes, host functions, Ψ_R, Ψ_A, Ψ_I and
the accumulation state transition). The model passes the test vectors, and theorems about it are
checked by Lean's kernel. The model is then used to verify **real compiled service binaries**:

- the witness service, `services/witness/witness-service.jam`;
- Parity's bootstrap service, `services/bootstrap/jam-bootstrap-service.jam`, built unmodified from
  the published crate `jam-bootstrap-service` 0.1.29.

For bootstrap, this includes the heap allocator that the JAM service SDK links into every service
(picoalloc). Its compiled `alloc`, `dealloc` and `realloc` are proved to refine a functional
model, and that model is proved to keep a full heap invariant.

The proofs are about the octets that run on chain, not about source code, a compiler or a
hand-translation. The semantics they use is the Gray Paper's, as modelled here and validated
against the vectors.

## The PVM model

**What is modelled.** The `PVM` library is exactly Gray Paper Appendix A:
- deblob, decoding and instruction semantics;
- memory, Ψ₁ and Ψ (§A.1–A.5);
- Ψ_H, Y and Ψ_M (§A.6–A.8);
- the gas model (§A.9–A.10).

The `JAM` library builds on it with:
- the codec;
- Blake2b-256 and Keccak-256;
- the general, accumulate and refine host functions;
- Ψ_A, Ψ_R and Ψ_I;
- the §12 accumulation state transition.

The model is total, and memory is an extensional finite map. The opcode tables and the gas-cost
table are generated from the paper's LaTeX, and CI checks them for drift
(`scripts/gen_tables.py`, `scripts/check-tables.sh`). See the README's
[Scope](../README.md#scope) and [Layout](../README.md#layout) sections.

**How it is validated** (from the README's [results table](../README.md#results)):

| Check | Result |
| --- | --- |
| PVM `programs/` vectors: status, registers, pc, gas, fault address, host call, memory | **364 / 364** |
| Block costs in `programs/` | **5,123 / 5,123** |
| Block costs in `gas-tests/` (doom, pinky, prime-sieve) | **39,737 / 39,737** |
| Basic blocks (ϖ) against the blocks the vectors list | identical in all 367 programs |
| Codec, work-package family (GP v0.8.0 vectors) | 6 / 6 |
| Blake2b-256; Keccak-256 / SHA3-256 | 13 / 13; 15 / 15 |
| General host functions; refine host functions, Ψ_R and Ψ_I (hand-written, no vectors exist) | 30 / 30; 59 / 59 |
| Accumulation STF (§12), tiny vectors | **61 / 63**; the 2 others are `bless_from_non_manager`, which the vectors' changelog lists as departing from GP 0.8.0 |

The PVM vectors are [koute/jamtestvectors](https://github.com/koute/jamtestvectors), commit
`6bf3768`. The JAM vectors are [davxy/jam-test-vectors](https://github.com/davxy/jam-test-vectors)
v0.8.0.

`Tests/Invocation.lean` adds **kernel-checked examples**: hand-assembled programs run through Y,
Ψ_H and Ψ_M and evaluated by `decide +kernel`, so Lean's kernel itself evaluates the model. They
cover out-of-gas, traps, invalid blobs, unreadable output and Y's memory layout. The vectors at the
pinned commit do not cover these layers.

**Theorems about the model itself** (details in the README's [Theorems](../README.md#theorems)
section):
- `psi_eq` (`PVM/Theorems/Termination.lean`): the executable `psi` satisfies the paper's
  recursive definition of Ψ, and its fuel never runs out.
- `psiHStar_eq` (`PVM/Theorems/Invocation.lean`): `psiHStar` is the paper's Ψ_H* for any handler
  that never adds gas.
- `accHostFn_gasNonIncreasing`, `refineHostFn_gasNonIncreasing` and
  `isAuthHostFn_gasNonIncreasing` (`JAM/Theorems/HostGas.lean`): the protocol's dispatchers never
  add gas.
- `psi_eq_psiFast` (`PVM/Fast.lean`, registered with `@[csimp]`): the fast interpreter that the
  tests run is equal to the paper-literal `psi`.
- `psiA_confined` and `psiR_noExports` (`JAM/Theorems/Confinement.lean`): code that never names
  certain host calls cannot touch other accounts or export segments.
- `psi_freeRun`, `psiM_of_freeRunH` and `psiM_of_stepsH` (`PVM/Logic/`): the gas-free reasoning
  layer used below. It is sound against Ψ and Ψ_M.
- `FreeStepsH.keepRO` (`JAM/Theorems/KeepRO.lean`): a gas-free refine run (under
  `refineContractK`, any cap) keeps the access of every page outside the heap's 48 … pb and the value
  of every octet on such a page that is not writable, so read-only data is never touched. From
  `Program.exec_mem` (an instruction changes nothing off its writes), `Program.freeStep_keep` (a
  continuing step writes only writable octets, GP §A.4) and `refineContractK_keep` (`grow_heap` sets
  only heap pages; `fetch` writes only a writable range).

**Provenance.** The model was written from the Gray Paper and the test vectors only. No other PVM
or JAM implementation was consulted.

## Theorems about real binaries

Most theorems below are stated for any blob that passes a given list of **code facts**:
`checkCode p facts = true`, meaning the decoded instruction at each index, block starts and
jump-table entries. For both vendored binaries, the kernel proves this of the actual octets:
- witness: `Services.Witness.CodeCheck.checkCode_ok`;
- bootstrap: `Services.Bootstrap.CodeCheck.checkCode_ok`, in `Services/Bootstrap/CodeOk.lean`.

Each blob is represented to the kernel as one natural number (`PVM.NatBlob`).

### Witness service (`Services/Witness/`)

- **`Rejects.refine_rejects`** (`Services/Witness/Rejects.lean`).
  - *Statement:* take a work item whose code is the vendored witness binary, refined with the
    full-chain parameters and a gas limit of at least `gasBound` (about 4.1 × 10⁷, under 1% of
    the 5 × 10⁹ refine limit). Then for every core index c < 2¹⁶, item index i < 2¹⁶, service
    id < 2³², and payload that is either empty or 1–15 octets whose first octet is at least 12,
    Ψ_R's result is exactly ℰ(`Rejected(BadPayload)`) = [12, 0].
  - *Assumed:* nothing about the code. Its sections, code facts, block costs, layout and heap
    bounds are all checked by the kernel.
  - *Built from:*
    - `PsiREmpty.psiR_rejects_exact`, which says the same for any blob with witness's code facts
      and layout;
    - `PsiREmpty.psiR_rejects` (milestone A′), the "[12, 0] or ∞" form;
    - `PsiR.psiR_badTag` and `PsiREmpty.psiR_empty`;
    - the gas-free runs `BadPayload.run_badTag` and `EmptyPayload.run_empty`.
- **`Confined.accumulate_confined`** and **`Confined.refine_noExports`**
  (`Services/Witness/Confined.lean`).
  - *Statement:* for every state, input and gas, accumulating witness changes nothing outside its
    own account, and its refine exports no segments.
  - *Assumed:* nothing about the code. The kernel scans every opcode position of the binary for
    `ecalli` (`CodeCheck.hostIds_ok`).
- **Function summaries used along the way:**
  - `memcpy_small` (`Memcpy.lean`): the compiler's `memcpy` for fewer than 16 octets;
  - `decodeU32` (`DecodeU32.lean`): the SDK's `u32` decoder, for every n < 2³²;
  - `decodeC` (`DecodeC.lean`): the inlined decode of the core index, for every c < 2¹⁶;
  - `prefix_from_Y` (`Prefix.lean`): the first 702 steps of refine, from Y's starting state.

An independent kernel, nanoda as vendored by
[witness-lean](https://github.com/ascrivener/witness-lean), also accepted all 18,571 nodes of
`psiR_rejects`. See the README's [witness-lean section](../README.md#checking-on-chain-witness-lean).

### Bootstrap service: refine (`Services/Bootstrap/`)

- **Malformed payload: the empty payload panics.** `psiR_empty`
  (`Services/Bootstrap/PsiREmpty.lean`).
  - *Statement:* for every c < 2¹⁶, i < 2¹⁶ and service id < 2³², with an empty payload, Ψ_R's
    result is ☇ (panic) or ∞. The decode of `Instructions` fails and the service's `unwrap`
    traps at pc 6377.
  - *Scope:* the empty payload is the only malformed payload covered so far.
- **Empty instruction list.** `psiR_noinstr` (`Services/Bootstrap/NoInstr.lean`).
  - *Statement:* for every c < 2¹⁶, i < 2¹⁶, service id < 2³² and 32-octet salt, with payload
    ℰ(`Instructions { instructions: [], salt }`) = [0] ⌢ salt, Ψ_R's result is
    ℰ(`BootstrapWorkOutput { instructions: [], work_item_index: i }`) = [0] ⌢ ℰ₂(i), or ∞.
  - *Built from:* `NoInstrArgs`, `NoInstrHead`, `NoInstrTail1`–`8` (one per hex-digit count of
    the service id, which the service logs) and `NoInstrFinish`.
- *Assumed by both:*
  - the looked-up code has the deployed layout and passes `checkCode` for bootstrap's code facts;
  - the heap bounds are `(48, 1044430)`;
  - the full-chain parameters.

  The kernel proves the code facts of the vendored blob (`CodeOk.checkCode_ok`). The layout is
  checked by the compiled `lake build bootstrapcheck`. Unlike witness's `refine_rejects`, no
  bootstrap theorem yet discharges these hypotheses for the vendored blob in a single statement,
  and there is no gas bound, so the "or ∞" remains.
- **The `Instructions` decode loop, for lists of `Checkpoint`.** `DecodeLoop.loop` and
  `DecodeLoop.pass` (`Services/Bootstrap/DecodeLoop.lean`).
  - *Statement:* from the loop's state after k of n elements, the loop at pc 680 decodes the
    remaining elements, each one a `Checkpoint` (tag 15). Each 232-octet value goes into its
    buffer slot. The loop then leaves for pc 562 with all n `Checkpoint`s in the buffer, and
    changes only its stack frame, the reader and the buffer.
  - *Assumed:* n < 128, and the buffer is 8-aligned, lies after the payload in the heap and stays
    below 2³¹ (`Ok`). The loop invariant `Inv` fixes the frame's concrete addresses.
  - *Scope:* this is a loop lemma. It is **not yet composed** into a Ψ_R theorem for a payload of
    `Checkpoint`s, and other instruction kinds are not covered.
- **The decode loop, for any instruction.** `Decode.Loop.loop` and `Decode.Elems`
  (`Services/Bootstrap/Decode/Loop.lean`, `Elems.lean`).
  - *Statement:* `ElemOk enc Rep` says that `Instruction::decode`, entered after the first octet of
    the encoding `enc`, reads the rest, returns to the loop and leaves a value satisfying `Rep` (and not
    the error word) in its slot. If every element of a payload `es` has an `ElemOk`, the loop at 680
    decodes them all: it leaves for 562 with value j, satisfying `reps j`, in buffer slot j, and changes
    only the stack, the reader and the buffer. This generalizes `DecodeLoop.loop` from `Checkpoint`s to
    any list. `Elems` gives the `ElemOk` of `Checkpoint`, `Panic` and `Benchmark` (`unit`), and of
    `Zombify`, `Exported`, `Yield`, `Solicit`, `Forget`, `Eject`, `Upgrade`, `Lookup`, `Transfer` and
    `RandomStorageRefine`, each saying the
    slot holds the discriminant and then the encoding's fields at their offsets.
  - *Assumed:* fewer than 128 elements (a one-octet length), each encoding non-empty, the buffer
    8-aligned after the payload and below 2^31 (`Ok`); the stack writable from its bottom
    (4278050816, the blob's 8192-octet stack) to the loop's frame.
  - *Scope:* `ElemOk`s for the remaining variants (Assign and the Vec/Option ones)
    are not stated yet; the loop is not yet composed into a Ψ_R theorem.
- **`Instruction::decode`'s tag dispatch, for every tag.** `Decode.Tag.dispatch`, `reject` and
  `unit_variant` (`Services/Bootstrap/Decode/Tag.lean`).
  - *Statement:* from 20626, where the reader has just read the tag octet into the function's
    frame at A:
    - for each tag t < 25, the 32-bit offset table at 67476 sends the run to t's decoder
      `handler t`, changing nothing but ω₇ and ω₈ (`dispatch`);
    - if the reader failed or t ≥ 25, the function returns the error word 2^64 − 2 in its result
      slot (`reject`);
    - for the variants without fields (`Checkpoint`, `Panic`, `Benchmark`), the function returns
      their discriminant word 2^63 + t − 1 (`unit_variant`).

    In each case the function restores ω₀, ω₅, ω₆ and sp from the frame and returns.
  - *Assumed:* the offset table's 100 octets (read-only data) and the frame's saved words. Unlike
    `DecodeLoop`, the frame address A and the slot O are arbitrary, so the theorems also serve the
    decode of work outputs in accumulate.
  - *Scope:* the decoders of the 22 variants with fields are not covered yet. The code facts now
    cover all of `Instruction::decode`, from two traced payloads that between them hold every
    instruction kind, plus the whole range 20626 … 22145.
- **The compiler's `memset`, zeroing an aligned buffer.** `Memzero.memzero`
  (`Services/Bootstrap/Memzero.lean`).
  - *Statement:* called at 70133 with an 8-aligned D, the octet 0 and n a multiple of 8 and at
    least 16, `memset` zeroes D … D + n, changes no other memory and returns.
  - *Scope:* only that case (the word loop). Other fill octets, unaligned destinations and short or
    ragged lengths take paths not covered yet. `Transfer`'s decoder uses this case for its memo.
- **`Instruction::decode` for variants with fixed-width fields.** `Decode.Fixed.zombify`,
  `exported` and `read_u64` (`Services/Bootstrap/Decode/Fixed.lean`).
  - *Statement:* from 20626 with tag 3 (`Zombify { ejector: u32 }`) or 20 (`Exported { count: u64 }`),
    and the reader holding enough octets, the function returns the variant in its slot O: the
    discriminant word 2^63 + t − 1 at O and the field's octets, copied from the payload, at O + 8.
    The reader is advanced by the field's width. Memory changes only in the stack below the frame,
    the reader and the slot. `read_u64` summarizes the shared `u64` reader at 3791, which every `u64`
    field goes through.
  - *Scope:* the other variants are not covered yet.
- **`Instruction::decode` for variants with a hash field.** `Decode.Hash.yield`
  (`Services/Bootstrap/Decode/Hash.lean`).
  - *Statement:* from 20626 with tag 14 (`Yield { hash }`) and the reader holding at least 32
    octets, the function reads the hash into its frame (`read_big_sp`), copies it to O + 8 and puts
    the discriminant word 2^63 + 13 at O. The reader is advanced by 32. Memory changes only in
    A − 88 … A + 32, the reader and O … O + 40.
  - *Scope:* `CreateService` is not covered yet (`Provide`: see `provide_hash` and `provide_inline_*`).
- **`Instruction::decode` for a hash and a `u64`.** `Decode.HashU64.solicit` and `forget`
  (`Services/Bootstrap/Decode/HashU64.lean`).
  - *Statement:* from 20626 with tag 6 (`Solicit { hash, len }`) and the reader holding at least 40
    octets, the function returns the variant in its slot O: the discriminant word 2^63 + 5 at O, the
    hash at O + 8 and `len`'s 8 octets at O + 40, all copied from the payload. The reader is advanced
    by 40. Memory changes only in the 176 octets below the frame, the reader and O … O + 48.
    `forget` is the same for tag 7 (`Forget { hash, len }`, word 2^63 + 6).
    `U32Hash.eject` (`Services/Bootstrap/Decode/U32Hash.lean`) does the same for tag 4
    (`Eject { target: u32, code_hash }`, word 2^63 + 3): the hash at O + 8 and `target` at O + 40,
    the reader advanced by 36.
    `Upgrade.upgrade` (`Services/Bootstrap/Decode/Upgrade.lean`) does the same for tag 1
    (`Upgrade { code_hash, min_item_gas, min_memo_gas }`, word 2^63): the hash at O + 8 and the two
    `u64`s at O + 40 and O + 48, the reader advanced by 48, through three reads.
    `Lookup.lookup` (`Services/Bootstrap/Decode/Lookup.lean`) does the same for tag 8
    (`Lookup { service: u32, hash, eager: bool }`, word 2^63 + 7): `service` at O + 8, the hash at
    O + 12 and the bool at O + 44, given that the payload's bool octet is 0 or 1; the reader advanced
    by 37.
  - *How:* a helper with its own 88-octet frame reads the hash (`read_big_sp`), moves it, reads the
    `u64` (`read_ok`) and stores the variant (`s1`, `s2`, `s3`).
- **`Instruction::decode` for `RandomStorageRefine`.** `Decode.RandomStorageRefine.random_storage_refine`
  (`Services/Bootstrap/Decode/RandomStorageRefine.lean`).
  - *Statement:* from 20626 with tag 21 (`RandomStorageRefine { seed: u64, n: u8 }`) and the reader
    holding at least 9 octets, the function returns the variant in its slot O: the discriminant word
    2^63 + 20 at O, `seed` at O + 8 and `n` at O + 16, copied from the payload (any octet for `n`). The
    reader is advanced by 9. Memory changes only in A − 144 … A + 24, the reader and O … O + 17.
  - *How:* the decoder's 56-octet frame and a shared helper for a `(u64, u8)` pair (35406, jump-table
    entry 825), which reads both (`read_ok`) and writes `Ok` with them at A (`r1` … `r4`).
- **`Instruction::decode` for `Transfer`.** `Decode.Transfer.transfer`
  (`Services/Bootstrap/Decode/Transfer.lean`).
  - *Statement:* from 20626 with tag 2 (`Transfer { destination: u32, amount: u64, gas_limit: u64,
    memo }`) and the reader holding at least 148 octets, the function returns the variant in its slot
    O: the discriminant word 2^63 + 1 at O, the 128-octet memo at O + 8, `amount` at O + 136,
    `gas_limit` at O + 144 and `destination` at O + 152, all copied from the payload. The reader is
    advanced by 148. Memory changes only in the 264 octets below the frame, the reader and O … O + 156.
  - *Assumed:* A and O 8-aligned; the stack, reader, payload and slot apart.
  - *How:* a 176-octet frame; three `read_ok`s park the integers, `memzero` clears the memo's buffer,
    `read_big_sp` reads the memo into it and `memcpy_big_aligned` copies it to O + 8 (`t1` … `t7`).

- **`Instruction::decode` of `LookedUp { data: Option<Vec<u8>> }`, without allocation.**
  `Decode.LookedUp.looked_up_none` and `looked_up_empty` (`Services/Bootstrap/Decode/LookedUp.lean`).
  - *Statement:* from 20626 with tag 18, if the reader's next octet is 0 (`None`), the function
    returns the discriminant word 2^63 + 17 at O and the niche word 2^64 − 1 at O + 8, and advances
    the reader by 1 (`looked_up_none`). If the next octets are 1 (`Some`) and ℰ(0) (length 0), it
    returns 2^63 + 17 at O and the empty `Vec` `{cap 0, ptr 1, len 0}` at O + 8, and advances the
    reader by 2 (`looked_up_empty`). Memory changes only in the callees' frames below A, the reader
    and O … O + 32.
  - *How:* `Option<Vec<u8>>::decode` (35937) reads the tag (`read_ok`). For `Some`, it decodes the
    length (`decodeU32`) and calls `read_vec` (3473), which for n = 0 neither reads nor allocates
    (`VecU8.vec_u8_empty`).
  - *Also proved, not yet composed:* the steps of `read_vec` for 1 ≤ n ≤ 16384 (one chunk) and of
    `finish_grow`'s path through `alloc` (`VecU8.v1` … `v3`, `g1`, `g2`). `AllocOk.alloc_ok`
    (`Services/Bootstrap/Decode/AllocOk.lean`) is `alloc` (40494) for any successful model `alloc`, growing the heap or not, as one statement.
  - *Scope:* non-empty `Some` payloads are not covered yet. The code facts lack `read_vec`'s and
    `finish_grow`'s realloc paths and the error exits. The allocator's wrapper theorems also don't
    state that page access outside the heap is kept, so the payload's readability after an `alloc`
    can't be shown yet.

- **`Instruction::decode` of the single-`Vec` variants with no elements.**
  `Decode.VecEmpty.vec_empty` (`Services/Bootstrap/Decode/VecEmpty.lean`).
  - *Statement:* from 20626 with tag 5 (`DeleteItems`), 10 (`Export`), 19 (`Imported`) or 9
    (`Import`), and the reader's next octet ℰ(0), the function returns the discriminant word
    (2^63 + 4, 2^63 + 9, 2^63 + 18 or 2^63 + 8) at O and the empty `Vec` `{cap 0, ptr 8, len 0}` at
    O + 8. The reader is advanced by
    1. Nothing is allocated. Memory changes only in A − 176 … A, the reader and O … O + 32.
  - *How:* the four decoders share one shape: a helper frame, `decodeU32` for the length, and the
    element reader at 8 or 3100 (`vec_elems_empty`, `vec_pairs_empty` for n = 0).
  - *Scope:* non-empty vectors allocate, and are not covered yet (see the previous item's scope).

- **`Instruction::decode` of the other `Vec`/`Option` variants, in their cases without allocation.**
  `Decode.Provide.provide_hash`, `Decode.RandomStorage.random_storage_err`, `Decode.Bless.bless_empty`
  and `Decode.Designate.designate_empty` (`Services/Bootstrap/Decode/`).
  - *Statement:* from 20626, each returns the variant in its slot O with the reader advanced past
    its encoding:
    - `Provide { service, preimage: Hash(hash) }` (tag 17): the discriminant word 2^63 + 16 at O,
      the preimage's tag 0 at O + 8, `hash` at O + 9 and `service` at O + 48 (37 octets read);
    - `RandomStorageAccumulate(Err(()))` (tag 22): 2^63 + 21 at O and the niche word 2^64 − 1 at
      O + 8 (1 octet read);
    - `Bless` with no always-accumulate entries (tag 11): 2^63 + 10 at O, the empty `Vec`
      `{cap 0, ptr 8, len 0}` at O + 8 and the four `u32`s at O + 32 … O + 44 (17 octets read);
    - `Designate` with no keys (tag 13): 2^63 + 12 at O and `{cap 0, ptr 1, len 0}` at O + 8 (1 octet
      read). The bound check against 3·𝖢 (𝖢 read from 196616) passes for n = 0 whatever 𝖢 is.

    Memory changes only in the callees' frames below A (and the result slot at A for `Designate`),
    the reader and the slot.
  - *Scope:* `RandomStorageAccumulate(Ok(keys))` and non-empty `Bless` and `Designate` allocate, and
    are not covered yet. `Provide` with `Inline(bytes)`: see the next item.

- **`Instruction::decode` of `Provide { service, preimage: Inline(bytes) }`.**
  `Decode.Provide.provide_inline_small` and `provide_inline_big`
  (`Services/Bootstrap/Decode/ProvideInline.lean`).
  - *Statement:* from 20626 with tag 17, and the reader holding the service (4 octets), the preimage
    tag 1, ℰ(n) and n octets, `Provide`'s helper keeps the tag word 1 and decodes n (`decodeU32`). It
    then reads the bytes with `read_vec` into a `Vec` at H + 80 and moves the `Vec` with unaligned
    stores. `Instruction::decode` returns the discriminant word 2^63 + 16 at O, the tag 1 at O + 8,
    the `Vec` `{cap n, ptr q, len n}` at O + 16 and the service at O + 48, with the n octets at q. The
    reader is advanced by 5 + |ℰ(n)| + n.
    - 1 ≤ n ≤ 16384: q is the model's `alloc` of ⌈n/32⌉ units, and the heap holds the state after it
      (`vec_u8_small`).
    - 16384 < n < 2³⁰ − 64: through `vec_u8_big`, with the same two outcomes. Either the variant is
      returned, q an allocated chunk of ⌈n/32⌉ + 1 units of the state after the `realloc`s, or the
      run stops at a `realloc` the model fails (33055, ω₇ = 0).
  - *How:* `pi_pre` runs from 20626 to `read_vec`'s call and `pi_post` from its return to t. The new
    steps are `q3`, `q4`, `q5` and `p5i`. `q5`'s overlapping stores are checked octet by octet.
  - *Assumed:* as `vec_u8_small` / `vec_u8_big`, with `Instruction::decode`'s frame at A, the helper's
    frame at A − 152, and the reader, the slot and the payload above A.
  - *Setting:* the payload above A is not the decode loop's setting (see `vec_u8_small`). The loop
    uses `provide_inline_heap` (below) for n ≤ 16384.

- **`Vec<u8>`, `LookedUp { Some(bytes) }` and `Provide { Inline(bytes) }` with the payload in the heap
  (1 ≤ n ≤ 16384).** `Decode.VecU8.vec_u8_heap` (`Services/Bootstrap/Decode/VecU8Heap.lean`),
  `Decode.LookedUp.looked_up_heap` (`LookedUpHeap.lean`) and `Decode.Provide.provide_inline_heap`
  (`ProvideInlineHeap.lean`).
  - *Statement:* as `vec_u8_small`, `looked_up_small` and `provide_inline_small`, in the decode loop's
    setting. The payload (the whole encoding) lies inside the data of an allocated chunk, the
    allocator's context is `HeapCtx`, and the run is under `refineContractK cap` (cap ≥ 2²⁷). The
    `alloc` is `HeapCtx.alloc_call`, with two outcomes:
    - the model's `alloc` of ⌈n/32⌉ units gives `(q, s')`: the variant is returned with the `Vec`
      `{cap n, ptr q, len n}` and the n payload octets at q. The context is kept for `s'`, every
      allocated chunk of `s` is kept with its data, the block is a new allocated chunk, and page
      entries outside the heap are kept;
    - the model's `alloc` fails: the run reaches the `alloc` wrapper's return (40611) with null.
  - *How:* the payload survives the `alloc` because `alloc` keeps every allocated chunk and writes
    only off their data (`HKeep`, `off_hdr_data`); the reader's writes stay in the new block
    (`data_disj`). `read_low` is the reader for a source below its frames.

- **`realloc` keeps the other allocated chunks' data.** `Decode.ReallocKeepAll.realloc_wrap_cases_keep`
  (`Services/Bootstrap/Decode/ReallocKeepAll.lean`).
  - *Statement:* `realloc_wrap_cases_hdata`, and whenever the model's `realloc` returns a block, every
    octet of the data of an allocated chunk of `s` other than ptr's is as it was (`OthersData`).
  - *How:* `keep_of_hkeep`: a heap frame (`HKeep`) whose headers are those of `s`'s chunks, or lie in a
    free chunk or ptr's own chunk, or past the heap's top, keeps every such octet. Each case of
    `realloc` gives one:
    - same size: `same_refines_low`, only the stack;
    - shrink: `shrink_refines_hdr`;
    - to 0: `free_refines_hdr`;
    - grow in place, with or without `grow_heap`: `grow_refines_hdr` / `grow_heap_refinesK_hdr`, the
      new header in the free next chunk (`grow_hdr`);
    - fallback: `alloc`'s frame, then `memcpy` into the new block (free in `s`), then `free`.

    The wrappers (`realloc_wrap_keep`, `realloc_wrap_keep0`) carry it through the lock and unlock.
  - *Assumed:* as `realloc_wrap_cases_hdata`.

- **The decode loop for elements that allocate.** `Decode.LoopA.loopA`, `ElemOkA`,
  `Decode.HeapCtx.alloc_call` (`Services/Bootstrap/Decode/LoopA.lean`, `LoopAPass.lean`, `HeapCtx.lean`,
  `HeapWrap.lean`, `HeapFrame.lean`).
  - *Statement:* `ElemOkA` is `ElemOk` for a decoder that may call picoalloc's `alloc`. It runs under
    `refineContractK cap env`, with the allocator's context `HeapCtx` (picoalloc's state in memory,
    the heap pages and the stack). It either returns to the loop with a new state that keeps every
    allocated chunk and its data, and a value whose property depends only on chunks allocated during
    the element, or reaches a failed allocator call (`Exhausts`: a wrapper returned null and the
    model's call fails, `alloc` at 40611 or `realloc` in `read_vec` at 33055, `AllocFail`). Every `ElemOk` lifts to an `ElemOkA`
    (`ElemOkA.of_elemOk`). `ElemOkA` takes the globals' contents `gl` (196616 … 196792, `Glob`) at its
    start, and keeps them; `loopA` decodes the whole payload through `ElemOkA`s with the same `gl`,
    within the sum of the elements' own step bounds and 1700 an element (`bound`), or reaches a
    failed allocation. The heap context also says the read-only region (below 196608) is not
    writable (`HeapCtx.ro`).
    `alloc_call` is one call of the `alloc` wrapper: the model's block and state, with the context
    kept, the block a fresh allocated chunk and the heap's data and the globals below the allocator
    (196616 … 196792) kept (`HKeepG`), or null when the model fails.
  - *Assumed:* the cap on what one host call may charge is at least 2^27 (so any `grow_heap` fits);
    approved by Adam (2026-11-09).
  - *How:* main's `alloc_wrap_refines`, `alloc_wrap_refines_growK` and `alloc_wrap_refines_failK`,
    with the `HKeepG` frame of `alloc_refines_hdr` carried through the wrapper (`HeapWrap`);
    `HKeepG` is `HKeep` with the globals between the wrapper's lock word (196608) and the allocator
    (`A0` = 196792); the allocator's proofs give it unchanged, and `HKeepG.hkeep` recovers `HKeep`;
    `Rep.congr_data` (writes inside an allocated chunk's data keep `Rep`) and `alloc_keeps_used`.

- **`Instruction::decode` of a `Vec` of hashes, and of `Assign`.** `Decode.VecHash.vec_hash`,
  `Decode.Assign.assign_elem` (`Services/Bootstrap/Decode/VecHash.lean`, `Assign.lean`).
  - *Statement:* `vec_hash`: the hash-`Vec` decoder (1764) with 1 ≤ n ≤ 512 and the payload's n·32
    octets in an allocated chunk either allocates a fresh chunk q (the model's `alloc` of n units),
    copies the n hashes there, returns the `Vec` (n, q, n) and advances the reader, keeping the heap
    context, every allocated chunk and its data, the globals and the read-only data; or an
    allocation fails (`Exhausts`). `assign_elem`: `Assign` (tag 12) is an `ElemOkA`. With the
    globals holding at 196680 a word G whose low 32 bits n are 1 … 512, the encoding
    [12] ++ core (2) ++ n hashes ++ assigner (4) decodes to the slot `AssignRep`: the discriminant
    2^63 + 11, the queue's capacity and length n and pointer q, the assigner and the core, and the
    n hashes at q in the heap; within 1000 + 550·n steps.
  - *Assumed:* the global at 196680 is a parameter G (the start-up code copies it from the protocol
    parameters, presumably 𝖰 = 80 of GP v0.8.0); that start-up sets it is not yet proved (a
    follow-up). Approved by Adam (2026-11-09).
  - *How:* step lemmas `p1`, `g1`, `p5`, the element loop `elems`, and `alloc_call` for 1764; `as1`
    … `as4` for `Assign`'s handler (20971) and helper (24765), with `read_ok` for the core and the
    assigner; the decoder stores the length capped by the global (`min len (G mod 2^32)`), which is n.

- **Runs under the refine contract keep page access outside the heap.** `Alloc.FreeStepsH.pagesOut`
  (`Services/Bootstrap/Alloc/Pages.lean`).
  - *Statement:* any `FreeStepsH` run under `refineContractK cap env`, with `heapBounds env.code =
    (48, pb)`, keeps every page entry outside the pages 48 … pb − 1 (`PagesOut 48 pb`). So readability
    and writability are kept below 196608 and from 4096·pb up (`PagesOut.readable`, `.writable`). This
    is the page frame of the allocator's theorems: after `alloc` or `realloc`, the read-only payload
    is still readable.
  - *How:* every instruction's memory is μ or a `writeN` of μ (`exec_pages`). The contract allows only
    `grow_heap`, which sets pages 48 … t with t ≤ pb; `fetch`, which only writes octets; and unknown ids,
    which change nothing (`refineContractK_pagesOut`).

- **Reading 1 … 16384 octets into a fresh `Vec<u8>`, and `LookedUp { data: Some(bytes) }`.**
  `Decode.VecU8.vec_u8_small` (`Services/Bootstrap/Decode/VecU8Small.lean`) and
  `Decode.LookedUp.looked_up_small` (`Services/Bootstrap/Decode/LookedUpSmall.lean`).
  - *Statement:* `read_vec` (3473) for 1 ≤ n ≤ 16384 octets: when the model's `alloc` (the host's
    `growTo pb`) returns q for ⌈n/32⌉ units, it returns `{cap n, ptr q, len n}` with the n payload
    octets at q. The heap then holds the model's state after the `alloc` (`Rep`, `WF`, `FirstOk`, the
    lock clear), and ⟨q − 32, ⌈n/32⌉ + 1, used⟩ is one of its chunks. The reader is advanced by n. Page
    entries outside the heap are kept, and at sp and above memory changes only in the reader and the
    slot. `looked_up_small` lifts this to `Instruction::decode` of tag 18 with payload 1, ℰ(n), bytes.
  - *Assumed:* a well-formed, initialized heap within 14 pages of its bound (as
    `realloc_wrap_cases`), the stack above the heap's bound and 2³¹, and the reader, the slot and the
    payload at or above the frame. The run is under `refineContract`.
  - *Setting:* the payload at or above the stack frame is **not** the decode loop's setting: there the
    payload is inside an allocated heap chunk. These theorems remain true but do not apply to the
    loop; the loop uses the heap-payload versions below (`vec_u8_heap`, `looked_up_heap`).
  - *Scope:* the failure of `alloc` is not covered, nor is the data of other live heap blocks, which
    `alloc_ok` does not state (both are in `vec_u8_heap`). More than 16384 octets: see `vec_u8_big`
    below.
- *`Vec<u8>` of more than 16384 octets* (`Services/Bootstrap/Decode/VecU8Pass.lean`, `vec_u8_big`;
  steps in `VecU8Loop.lean`): `read_vec` (3473) for 16384 < n < 2³⁰ − 64. The first chunk of 16384
  octets goes into q, the model's `alloc` of 512 units. Then the loop at 3520 (`loop`, by induction
  over the octets left; one pass is `pass_ok`/`pass_fail`) reads chunks of min(left, L) octets,
  L the octets read so far, growing the buffer to exactly L + chunk with `realloc`
  (`realloc_wrap_cases_hdata`). The result is one of two:
  - `read_vec` returns with the `Vec` `{cap n, ptr q', len n}` at O and the n payload octets at q'.
    The heap then holds the model's state after the `realloc`s, q' is an allocated chunk of
    ⌈n/32⌉ + 1 units, and the reader is advanced by n.
  - A `realloc` the model fails (`none`, from the state memory then holds) is reached: the run stops
    at `finish_grow`'s return point from it (33055) with ω₇ = 0. What follows (`handle_alloc_error`)
    is not covered.
  - *Assumed:* as `vec_u8_small`, with the first `alloc` succeeding, the stack frame 96 octets
    lower, the payload disjoint from the reader's slot, and n < 2³⁰ − 64 (the model's `realloc`
    sizes are below 2²⁵ − 1 units).
  - *Steps:* the bound `loopSteps` adds 2000 for each doubling pass.
  - *Setting:* as `vec_u8_small`, the payload is at or above the stack frame, which is not the decode
    loop's setting. A heap-payload version needs `realloc` to keep other chunks' data, which is not
    yet proved.
  - `looked_up_big` (`Services/Bootstrap/Decode/LookedUpBig.lean`) lifts this to `Instruction::decode`
    of tag 18, `LookedUp { data: Some(bytes) }` with |bytes| > 16384, with the same two outcomes.
  - *`realloc` keeps the heap bound* (`Services/Bootstrap/Decode/ReallocOk.lean`,
    `realloc_wrap_cases_hdata`): `realloc_wrap_cases_data`, and for each block the model's `realloc`
    returns, the new state keeps the heap base and its allocated space ends within the heap's pages
    afterwards (`s'.base + 32 · s'.allocated ≤ 4096 · h'`), the bound the next `alloc` or `realloc`
    assumes. Model lemmas: `free`, `shrink` and `free`'s merges keep the allocated space, and
    `realloc_chunk`: the block `realloc` returns (alignment one unit, a nonzero request) is an
    allocated chunk of exactly the request plus one unit. Same assumptions as
    `realloc_wrap_cases_data`.

### picoalloc: the model (`Services/Picoalloc/`)

`Services/Picoalloc/Model.lean` is picoalloc 5.2, the SDK's heap allocator, written as Lean
functions over its state: the allocator's metadata and the chunk headers. Sizes are in 32-octet
units.

`WF` (`Invariant.lean`) is the heap invariant:
- the chunks walked from the base tile the space;
- no two free chunks are adjacent;
- each chunk records its predecessor's size;
- each free chunk is in exactly its bin's doubly linked list;
- the two-level bitmap marks exactly the non-empty bins;
- the allocated space covers every allocated chunk and header.

`FirstOk` (`First.lean`) says the first chunk's `prev` is 0.

| Theorem | File | Statement |
| --- | --- | --- |
| `init_wf`, `alloc_wf_fresh` | `Init.lean` | `init` of a zeroed allocator gives one free chunk spanning the space, and the first `alloc` keeps `WF` |
| `alloc_wf`, `alloc_chunks` | `Alloc.lean` | `alloc` at alignment one unit keeps `WF`. The returned block was free and overlaps no earlier allocation, and every other chunk is unchanged |
| `alloc_wf_align`, `alloc_wf_align_fresh`, `alloc_first_align`, `alloc_ptr_align`, `alloc_align_eq` | `AllocAlign.lean` | `alloc` at **any** power-of-two alignment keeps `WF` and `FirstOk`, and the returned pointer is aligned in the address space |
| `free_ok`, `free_wf` | `Free.lean` | `free` merges the freed chunk with its free neighbours into one free chunk, leaves every other chunk unchanged, and keeps `WF` |
| `realloc_wf` | `Realloc.lean` | `realloc` keeps `WF` on every path: shrink, grow in place, alloc + free, and size 0 (free, return null) |
| `alloc_first`, `free_first`, `realloc_first` | `First.lean` | each operation keeps `FirstOk` |

The model was also checked against the binary by execution. `genwitnesssteps --service bootstrap
allocck` compares the model with every allocator call in traced bootstrap runs. CI requires
"0 mismatches", and the model's history reports `WF` holding before and after each of the 173
traced calls. This is a test, not a proof; the proofs are the refinement theorems below.

### picoalloc: the compiled binary refines the model (`Services/Bootstrap/Alloc/`)

**What a refinement theorem says.** Each theorem below starts from memory that holds a model
state `s` (`Rep μ s`) satisfying `WF s` and `FirstOk s`, with the registers the calling
convention gives. It concludes that there is a gas-free run (`FreeStepsH`) of the binary's code
from the function's entry to its return, within a stated step bound, that ends with:
- memory holding the model's result `s'` (`Rep μ' s'`), with `WF s'` (and `FirstOk s'` where
  stated);
- the model's return value in ω₇;
- the caller's ω₀, ω₁, ω₅ and ω₆ restored;
- the stack from sp up untouched;
- page writability unchanged, or, with heap growth, the new heap pages stated (`HeapPages`).

The wrapper theorems also take the allocator's lock byte at 206848 and release it.

**`alloc`** (wrapper at 40494, `alloc_impl` at 41177):

| Case | Theorems | File |
| --- | --- | --- |
| Success, no heap growth | `alloc_refines`, `alloc_wrap_refines` | `AllocRefines.lean`, `AllocWrap.lean` |
| Success at any power-of-two alignment `2^k` units, no heap growth | `alloc_refines_align`, `alloc_wrap_refines_align`, `alloc_impl_align` | `AllocAlignRefines.lean`, `AllocAlignImpl.lean` |
| Success, the heap grown through `grow_heap` | `alloc_refines_grow`, `alloc_wrap_refines_grow` | `AllocGrowRefines.lean`, `AllocWrapGrow.lean` |
| First use: `initialize`, which grows the heap and sets up one free chunk at 206880 | `alloc_refines_first`, `alloc_wrap_refines_first`, `init_rep`, `first_grows` | `AllocFirst.lean`, `AllocInit.lean` |
| Failure: the binary returns null wherever the model's `alloc` fails, with memory still holding `s` | `alloc_refines_fail`, `alloc_wrap_refines_fail`, `alloc1_none` | `AllocFailRefines.lean`, `AllocFailModel.lean` |

`alloc1_none` shows that the model's `alloc` fails in exactly four ways:
- the request is too large;
- no bin is found;
- the bin's chunk is too small;
- the host refuses to grow the heap.

The binary is proved to return null on each path.

**Alignment.** Successful `alloc` without heap growth is proved at **any** power-of-two
alignment of `2^k` units (`AllocAlign*.lean`):
- The binary rounds the data unit up to a multiple of `2^k` in the address space, as the model's
  `dataOff` does.
- When this leaves a left remainder of `lhs ≠ 0` units, the binary registers it free at the
  chunk C (41736 … 41864), and the allocated chunk at `C + 32·lhs` gets `prev = lhs`.
- Memory ends up holding the model's `allocPostL`.
- The wrapper theorem takes an alignment of `al` octets with `(al + 31) / 32 = 2^k` and `k < 31`.

The other `alloc` theorems (heap growth, first use, failure) are for an alignment of **one
unit**, that is 1 to 32 octets. That covers every Rust allocation aligned to at most 32 octets.

**`dealloc`** (wrapper at 40613, free path at 42327):
- `dealloc_refines` (`Dealloc.lean`) and `free_refines` (`FreeRefines.lean`) state that memory
  ends holding the model's `free s ptr`.
- Every path is covered by `free_prev` and `free_next`, which handle the previous and next
  neighbours each being free or allocated, at the heap's start or end, and either the head of
  its bin or inside its list.
- No alignment restriction applies.

**`realloc`** (wrapper at 40701, `realloc_impl` at 42980):

| Path | Theorems | File |
| --- | --- | --- |
| Same size: address returned, allocator untouched | `same_refines` | `ReallocInplace.lean` |
| Shrink in place | `shrink_refines`, `realloc_inplace_refines` | `ReallocRefines.lean`, `ReallocInplace.lean` |
| Grow in place, no heap growth | `grow_refines`, `realloc_grow_refines` | `ReallocGrowRefines.lean` |
| Grow in place, heap grown | `realloc_impl_grow_heap`, `grow_heap_refines` | `ReallocGrowHeapImpl.lean`, `ReallocGrowHeapRefines.lean` |
| Size 0: free, return null | `realloc_zero_refines` | `ReallocZero.lean` |
| Fallback: alloc a new block, copy, free the old one | `fallback_pre`, `fallback_tail`, `fallback_refines`, `realloc_fallback` | `ReallocFallback*.lean` |
| Through the locked wrapper | `realloc_wrap` (generic), `realloc_wrap_inplace`, `realloc_wrap_grow`, `realloc_wrap_grow_heap`, `realloc_wrap_zero` | `ReallocWrap.lean`, `ReallocGrowHeapRefines.lean` |

When the fallback moves the block, the new block's first `usable`·32 octets equal the old
block's data as it was when `realloc` was called. The theorems are `realloc_wrap_fallback_data`,
and `realloc_wrap_cases_data` for every outcome that returns an address other than the old one
and null. They rest on frames for the allocator: `free_refines_hdr`, `alloc_refines_hdr` and
`alloc_refines_growK_hdr` show that in the heap only the allocator's fields and chunk headers
change (`HKeep`, `Rep.lean`), so other chunks' data is kept. On the paths that keep the address
(same size, shrink, grow in place, grow with the heap grown), the block's first
min(usable, new size)·32 octets are kept (`ReallocKeep.lean`). `realloc_wrap_cases_data` states
both for every outcome: any non-null result r holds those octets of the old block.

Through the wrapper, a null address returns null at once, and so does an alignment or size above
2³⁷ − 32 octets.

Not yet on `main` for `realloc`:
- a wrapper-level corollary for the fallback;
- the fallback when its inner `alloc` fails or grows the heap;
- the fallback reached after the host refuses heap growth;
- a fallback copy of 0 units;
- the combined case split `realloc_wrap_cases`.

These are in open PR #68.

## Trust base

- **Lean v4.36.0-rc1** (`lean-toolchain`). The model and proofs import only Lean core and `Std`.
  The test executables also use `Lean.Data.Json` from the core distribution.
- **Axioms:** every declaration in the `PVM`, `JAM` and `Services` namespaces depends only on
  `propext`, `Classical.choice` and `Quot.sound`. `scripts/CheckAxioms.lean` collects the axioms
  of every such declaration and fails on anything else. That includes `sorryAx`, and the
  `Lean.ofReduceBool` / `Lean.trustCompiler` axioms that `native_decide` and `bv_decide`
  introduce. CI runs this check.
- **No `sorry`, `native_decide`, `bv_decide`, `partial def` or `implemented_by`** anywhere in
  `PVM`, `JAM`, `Services` or `Tests`. CI greps for them.
- To check a single theorem: `#print axioms Services.Witness.Rejects.refine_rejects`, for example.

What you trust beyond the kernel:
- **The model's fidelity to the Gray Paper.** This is the main non-mechanical trust point. It is
  backed by the vector results above, and by generating the tables from the paper's source.
- **The statements.** Read them, especially the hypotheses listed here.
- **For bootstrap's Ψ_R theorems, the compiled layout check** (`bootstrapcheck`), as described
  above.

## Assumptions and limits

- **Writable memory.** The allocator theorems assume only that the heap and the stack are
  writable, never all of memory.
  - `WrAt μ HT S0 S1` (`Writable.lean`) says the heap region 196608 … `HT` and the stack
    `S0` … `S1` are writable, with `s.base + 32·s.allocated ≤ HT`.
  - `HeapPages μ 48 pb h` (`AllocGrow.lean`) is used where the heap grows. It says the writable
    pages in 48 … pb are exactly those below h, which is how `grow_heap` sees them.
- **At most 14 pages per heap growth.** Gas-free host calls are allowed at most `hostCostMax` =
  2000 gas (`JAM/Theorems/RefineContract.lean`). `grow_heap` costs 275 + 121 per page, so a
  growth theorem assumes the new top is at most 14 pages above the old one (the `hcost`
  hypothesis). Larger single growths are not covered yet.
- **Alignment.** In the binary, `alloc` with heap growth, on first use and on failure is proved
  at alignment one unit (≤ 32 octets). Success without growth is proved at any power-of-two
  alignment. The `realloc`
  fallback also needs a usable size of at least one unit, because a 0-unit copy takes `memcpy`'s
  small path, which is not composed yet.
- **Stack and range preconditions.** Each theorem fixes:
  - a stack pointer range (for example sp ≥ 2147483800 and below 2³²);
  - enough stack below sp (from 40 octets for `dealloc` to 304 for the `realloc` fallback);
  - a heap base of at least 206864, with the heap below 2³¹;
  - `s.allocated < 2³¹`.

  The `realloc` fallback also needs the base and sp 8-aligned. The wrapper theorems bound the
  size and alignment in octets: `size + 31 < 2³⁶`.
- **`alloc_impl`'s request size.** `alloc_refines_fail` assumes `req < 2³¹` units; see
  [Findings](#findings). The public wrapper always passes such a request.
- **Not stated: `realloc` copies the data.** In the fallback the copy runs inside the proof, but no
  theorem states that the new block holds the old block's contents, because the alloc and free
  lemmas do not yet give a frame for other chunks' data. The theorems state only the allocator's
  metadata and headers (`Rep`), the return value and the frame. Likewise, no theorem states that
  data in *other* live allocations is preserved by an allocator call.
- **Gas-free reasoning.** The allocator and decode-loop theorems are about gas-free runs
  (`FreeStepsH`) under a host contract:
  - `refineContract` for paths that call `grow_heap`;
  - any contract for paths that make no host call.

  `psiM_of_freeRunH` turns such a run into a statement about Ψ_M, of the form "this result, or ∞".
  Only witness's `refine_rejects` also carries a gas bound that removes the ∞. The allocator
  theorems say nothing about gas.
- **Refinement of a fragment, not of a whole program.** The allocator theorems are about the
  allocator's entry points called with the stated registers and memory. They are not yet composed
  into a Ψ_R or Ψ_A theorem about a bootstrap run that allocates.

## Findings

Disagreements between the model and the binary, found by the refinement proofs and resolved:

- **picoalloc's alignment rounding (#57).**
  - *Disagreement:* for alignments of 2 units or more, the model rounded the data unit from the
    heap base, while the binary rounds it in the address space. The heap base 206880 is 32 · 6465
    with 6465 odd, so the two differ for every such alignment.
  - *Resolution:* the binary is right, because Rust's allocator contract requires address-space
    alignment. The model was fixed. The existing theorems were all at alignment 1, where the two
    agree.
- **`realloc` to 0 units (#58, resolved in #62).**
  - *Disagreement:* the model returned `none`. The binary calls the free path on the chunk and
    returns null.
  - *Resolution:* the model now does the same, `(0, free s ptr, false)`, and
    `realloc_zero_refines` proves the binary matches.
- **`alloc_impl`'s 32-bit `req + 1` (#66).**
  - *Disagreement:* `alloc_impl` computes the minimum size `req + 1` with 32-bit adds. For
    `req ≥ 2³²` the sum wraps (`req = 2³²` gives 1), and the binary would allocate where the model
    fails.
  - *Why it is unreachable:* the public `alloc` wrapper only passes `req = ⌈size/32⌉ < 2³¹`.
  - *Resolution:* `alloc_refines_fail` assumes `req < 2³¹`.
- **Noted, not a disagreement (#65).** `realloc` with a null address returns null rather than
  allocating, unlike C's `realloc(NULL, n)`. The model's `realloc` is only defined for allocated
  chunks, so this is behaviour of the wrapper alone.

PRs #58–#67 report no other model/binary disagreements.

Findings about the Gray Paper and the test vectors themselves are triaged in
[`docs/upstream-candidates.md`](upstream-candidates.md), with the full notes in the README's
[Notes on the paper and the vectors](../README.md#notes-on-the-paper-and-the-vectors). Examples
are an inconsistency in 𝔓_S, Ψ_H's gas types, the non-termination of Ψ_H* for handlers that add
gas, and cases the vectors do not cover.

## How to reproduce

```bash
lake build                                  # the model and every theorem (CI builds a few large files first, one at a time)
lake env lean scripts/CheckAxioms.lean      # axiom audit of every PVM / JAM / Services declaration
scripts/fetch-vectors.sh                    # the pinned PVM vectors into vendor/
lake build pvmtest                          # every programs/ vector
lake build gascheck                         # every block cost in programs/ and gas-tests/
lake build Tests.Invocation                 # kernel-checked Ψ_H, Y and Ψ_M examples
lake build witnesscheck bootstrapcheck      # the vendored blobs' code facts and layout, compiled
lake exe genwitnesssteps --service bootstrap allocck 0 | tail -1   # picoalloc model vs traced binary
```

The full CI sequence, including the JAM vector suites and the drift checks for generated files,
is in [`.github/workflows/ci.yml`](../.github/workflows/ci.yml). A full build needs a large
machine: some proof files take several GB of memory to elaborate.

## In progress

At the time of writing, other work in progress includes:

- **The rest of `realloc`** (open PR #68):
  - the fallback's corner cases: inner `alloc` failing or growing the heap, the fallback after a
    refused heap growth, and a 0-unit copy;
  - `realloc_wrap_cases`, which matches every outcome of the model's `realloc` at alignment 1
    through the locked wrapper.
- **Lifting the 14-page limit,** by making the host-call gas cap a parameter of `refineContract`.
- **`alloc` in the binary at alignment above one unit with heap growth, on first use and on
  failure.** The no-growth success path is done (`AllocAlignRefines.lean`).

This page should be updated as these land.
