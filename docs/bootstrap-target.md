# Bootstrap: target theorems, spec and proof plan

**Status: proposal for review. No proofs.** This page proposes what "bootstrap is verified" should
mean in this repository, and how to get there. It has five parts:

1. [What bootstrap does](#1-what-bootstrap-does), read off its source.
2. [The spec](#2-the-spec), in prose and as Lean definitions (`Services/Bootstrap/Spec.lean`).
3. [The target theorems](#3-the-target-theorems), with Lean statements.
4. [The proof plan](#4-the-proof-plan): what exists, what is missing, the steps, and the risks.
   [Section 5](#5-the-allocator-assumptions-against-bootstrap) checks the allocator's assumptions
   against bootstrap.
5. [Open questions](#6-open-questions) for you to decide before proof work starts.

## Summary

- **Headline theorems.**
  - **T1 (refine):** for every payload, Ψ_R's result and exports are what `Spec.refine` gives (or ∞).
    With enough gas, the "or ∞" goes.
  - **T2 (accumulate):** for every input, Ψ_A's effect on the state, transfers, yield and provisions
    is that of running `Spec.accumulate` against the Gray Paper's host functions. If gas runs out,
    the effect is that of a prefix of that run, rolled back to its last checkpoint.
- **Safety corollaries:** refine never panics on well-formed input, refine's gas is bounded, the
  "local" instructions never touch another account, and accumulate's own bookkeeping stays
  consistent.
- **The spec** is a Lean transliteration of the Rust source. It covers all 25 instructions, the
  codec the binary actually runs, and every host call bootstrap makes, in order. It compiles, has
  no theorems and was checked by evaluation against the cases already proved.
- **Biggest risks:**
  - The logging code runs on every path and formats whole values with `core::fmt`.
  - The heap needs a model of the data in live blocks, not just the allocator's metadata.
  - The decoder accepts non-canonical lengths, which adds many paths.
- **What you need to decide:** see [the open questions](#6-open-questions). The main ones are which
  instructions to cover, how to treat logging, and which safety properties matter most.

---

## 1. What bootstrap does

### Sources

- **The binary** is `services/bootstrap/jam-bootstrap-service.jam`, built from crate
  `jam-bootstrap-service` 0.1.29.
- **The Rust source** is not vendored. Everything below comes from the published crates at the
  versions in the crate's `Cargo.lock`, downloaded from crates.io:
  - `jam-bootstrap-service` 0.1.29: `src/lib.rs`, the service itself, about 400 lines;
  - `jam-bootstrap-service-common` 0.1.29: the `Instruction` type and the storage keys;
  - `jam-pvm-common` 0.1.29: the SDK, with the entry points, host-call wrappers, logging and panic
    handler;
  - `jam-types` 0.1.29: the types (`GP_VERSION = "0.8.0"`, the same as the model);
  - `jam-codec` 0.1.1: the codec;
  - `bounded-collections` 0.3.2: `BoundedVec`.
- **The binary agrees with the source** wherever the existing proofs touch it:
  - `psiR_empty`: an empty payload fails `Instructions::decode` and traps at the `unwrap`;
  - `psiR_noinstr`: `[0] ⌢ salt` gives `[0] ⌢ ℰ₂(i)`;
  - `DecodeLoop`: `Checkpoint` is tag 15, and an `Instruction` is 232 octets in memory.

  Anything else said here about the binary is a claim about the source that the proofs would have
  to confirm.

**Assumptions**, marked **[A]** below:

- **[A1]** The binary was built from these sources. The README says so, with the build command.
- **[A2]** Integer overflow wraps. Rust release builds do not check overflow by default. This
  matters in one place only: the 32-bit transfer counter in `on_transfer`.

### Entry points (SDK `declare_service!`)

Both entry points start the same way:
1. They `fetch` (2) the protocol parameters (kind 0) and panic if `apply()` rejects them. With
   `Params.full` it accepts them.
2. They decode their arguments.

- **Refine** gets the GP arguments ℰ(c, i, s, ↕y, ℋ(p)). It returns ℰ(output) through a leaked
  `Vec`.
- **Accumulate** gets ℰ(t, s, |inputs|). It returns `(0, 0)` (no hash), so its yield comes only
  from the `yield` host call.

A Rust panic runs the SDK's panic handler, which logs and then executes `unimp`, a trap. Every
`unwrap`, `expect` and failed allocation therefore ends Ψ as ☇:
- in refine, the result is ☇;
- in accumulate, the state rolls back to the last checkpoint.

### The payload: `Instructions`

```
payload = ℰ(↕instructions) ⌢ salt(32 octets) ⌢ anything
```

The decoder is `Instructions::decode`, not `decode_all`, so trailing octets are ignored. The
codec is `jam-codec`'s derived SCALE-style encoding:
- fixed-width integers are little-endian (ℰ_l);
- enum tags are one octet;
- `Vec` lengths are a compact natural;
- arrays and `FixedVec` have no length;
- `Option` and `Result` have a 0/1 tag.

None of `Instruction`'s fields is `#[codec(compact)]`, so every number in an instruction has a
fixed width.

**The compact natural is not exactly GP's ℰ.** `jam-codec`'s decoder (`WrappedPrimitive::decode`)
works as follows:
- it reads a prefix octet b and takes l = the number of leading ones of b;
- it reads l more octets and returns their value plus (b's low 7 − l bits) · 2^(8l);
- if b = 255, it reads 8 octets.

It does **not** check that the encoding is the shortest one, so `[128, 5]` decodes as 5 just as
`[5]` does. A `Vec` length must also be below 2^32. This is the decoder the binary runs, so the
spec uses it (`Spec.Dec.compact`). The existing `decodeU32` proof covers only the canonical
encodings ℰ(n).

### The instructions

Tags are declaration order. In the table, "pass" means refine copies the instruction to its output
unchanged. Host-call numbers are the SDK's, which are also the model's.

| Tag | Instruction (fields) | Refine | Accumulate: host calls, then result |
| --- | --- | --- | --- |
| 0 | `CreateService` (code hash, code len u64, min item gas u64, min memo gas u64, endowment u64, memo[128], registration `Option<Vec<u8>>`, deposit offset u64, id `Option<u32>`) | pass | `new` (19): on failure `Err(CreateService)`. Then `lookup` (3) of the code in its *own* preimages, and if found `provide` (27) it to the new service, ignoring the reply. Then `transfer` (21) of the endowment, with the min memo gas as gas limit: on failure `Err(Transfer)`, **but the new service stays created**. If a registration name was given, read, update and write the registry, panicking if the write fails. Result: `Ok(ServiceId(id))`. |
| 1 | `Upgrade` (code hash, min item gas, min memo gas) | pass | `upgrade` (20), panicking on failure. `Ok(Unit)` |
| 2 | `Transfer` (dest u32, amount, gas limit, memo) | pass | `transfer` (21). `Ok(Transferred{dest, amount, memo})` or `Err(Transfer)` |
| 3 | `Zombify` (ejector u32) | pass | **First** remove all of bootstrap's own keys (below). Then `info` (6) of itself: unless bytes ≥ 81 and items = 2, `Err(Zombify)`. Then `forget` (25) of its code hash with length bytes − 81: on failure `Err(Forget)`. Then `upgrade` to code hash ℰ₄(ejector) ⌢ 0²⁸ with gas 0 and 0, panicking on failure. `Ok(Unit)` |
| 4 | `Eject` (target u32, code hash) | pass | `eject` (22). `Ok(Unit)` or `Err(Eject)` |
| 5 | `DeleteItems` (keys `Vec<Vec<u8>>`) | pass | `write` (5) of nothing under each key, which removes it. `Ok(Unit)`, whether or not the keys existed |
| 6 | `Solicit` (hash, len u64) | pass | `solicit` (24). `Ok(Hash(hash))` or `Err(Solicit)` |
| 7 | `Forget` (hash, len u64) | pass | `query` (23): if there is no request, `Err(Query)`. Then `forget` (25). `Ok(Hash(hash))` or `Err(Forget)` |
| 8 | `Lookup` (service u32, hash, eager bool) | if eager: `historical_lookup` (7), giving `LookedUp{data}`; else pass | `lookup` (3) in that service. `Ok(Data(d))` or `Err(Lookup)` |
| 9 | `Import` (items `Vec<(u64 index, u64 len)>`) | `fetch` (2) of each import segment, **panicking if it is missing**, truncated to len. Gives `Imported{data}` | `Err(Invalid)`, since refine never passes it on |
| 10 | `Export` (data `Vec<Vec<u8>>`) | `export` (8) of each blob, ignoring the reply. Gives `Exported{count}` | `Err(Invalid)` |
| 11 | `Bless` (manager, assigner, designator, registrar u32, always-acc `Vec<(u32, u64)>`) | pass | `bless` (15), with every core's assigner set to `assigner`. **Panics on failure**, for example when bootstrap is not the manager (HUH). `Ok(Unit)` |
| 12 | `Assign` (core u16, queue = exactly 𝖰 hashes, assigner u32) | pass | `assign` (16). `Ok(Unit)` or `Err(Assign)` |
| 13 | `Designate` (keys `BoundedVec<[336], 3·𝖢>`) | pass | `designate` (17). `Ok(Unit)` or `Err(Designate)` |
| 14 | `Yield` (hash) | pass | `yield` (26), panicking on failure. `Ok(Unit)` |
| 15 | `Checkpoint` | pass | `checkpoint` (18). `Ok(Unit)`. See also the results write below |
| 16 | `Panic` | pass | panic: the whole accumulate traps |
| 17 | `Provide` (service u32, `Hash(h)` or `Inline(bytes)`) | pass | For `Hash`: `lookup` (3) in its own preimages, giving `Err(Lookup)` if absent. Then `provide` (27). `Ok(Unit)` or `Err(Provision)` |
| 18 | `LookedUp` (data `Option<Vec<u8>>`), internal | pass | no call. `Ok(Data(d))` or `Err(Lookup)` |
| 19 | `Imported` (data `Vec<Vec<u8>>`), internal | pass | no call. `Ok(DataVec(data))` |
| 20 | `Exported` (count u64), internal | pass | no call. `Ok(Length(count mod 2³²))` |
| 21 | `RandomStorageRefine` (seed u64, n u8), test | gives `RandomStorageAccumulate(Ok(n keys from rand's SmallRng(seed)))` | `Err(Invalid)` |
| 22 | `RandomStorageAccumulate` (`Result<Vec<[32]>, ()>`), test | pass | if `Ok`: read `"count_random_storage"`, panicking if it is present but under 8 octets; write each key under itself; write the new count. Every write panics on failure. `Ok(Unit)` |
| 23 | `Benchmark`, test | pass | 1000 times: write `"item-{t}-{i}"` → `"{i}"` (panicking on failure), then `checkpoint`. `Ok(Unit)` |
| 24 | `AssignForGasCost` (core u16, queue `Vec<hash>`, assigner u32), test | pass | If the queue is empty, `Ok(Unit)` with no call. Else `assign` (16) is passed **ℰ(queue) including its length prefix**, and reads 𝖰·32 octets from there. `Ok(Unit)` or `Err(Assign)` |

`InstructionError` also has `MissingOutput` and `Panic`, which bootstrap never produces.

### Refine

1. Decode `Instructions` from the payload. If that fails, **panic** (☇).
2. For each instruction in order, apply the "Refine" column above. Only eager lookups, imports,
   exports and random-storage requests change, and only imports can panic.
3. Return ℰ(`BootstrapWorkOutput { instructions, work_item_index: i }`), which is
   ℰ(↕instructions) ⌢ ℰ₂(i).

Refine ignores the core index, the service id and the package hash, except in log lines. It
**passes the internal variants through**. A payload can therefore contain `LookedUp`, `Imported`,
`Exported` or `RandomStorageAccumulate` directly, and accumulate treats them as if refine had
produced them.

### Accumulate

For each accumulate input, in order:

- **Operand with a work error:** nothing.
- **Operand with output `o` (`on_work_item`):**
  1. Decode `BootstrapWorkOutput` from `o`, panicking if that fails, giving instructions `is` and
     item index `k`. Let `K` be the key `InstructionResults(package, k)`.
  2. Record the item in the ring (`add_recent_work_item`):
     - read the counter `c` (0 if it is absent or does not decode);
     - if slot `c` holds (p′, k′), remove `InstructionResults(p′, k′)`;
     - write (package, k) into slot `c`;
     - write the counter as (c + 1) mod 2·𝖢·𝖨.
  3. Write empty results under `K`, then `checkpoint`.
  4. For each instruction: if it is `Checkpoint`, first write the results so far under `K`. Then
     run it (the table above) and append its result.
  5. Unless `is` contains a `Zombify`, write all results under `K`.

  Every write in steps 2–5 panics on failure, for example when the storage is FULL.
- **Incoming transfer (`on_transfer`):**
  - read the u32 under `"transfer-count"` (0 if it is absent or does not decode) and write n + 1
    (wrapping, [A2]);
  - write ℰ(source, amount, memo) under `"transfer{n}"`. Both writes panic on failure.

**Bootstrap's own storage keys** (`StorageKey`, 1 + 32 + 2 octets at most):

| Key | Octets | Value |
| --- | --- | --- |
| `RecentWorkItemCounter` | `[0]` | ℰ₄(c) |
| `RecentWorkItem(c)` | `[1] ⌢ ℰ₄(c)` | package ⌢ ℰ₂(k) |
| `InstructionResults(p, k)` | `[2] ⌢ p ⌢ ℰ₂(k)` | ℰ(↕results) |
| `ServiceRegistry` | `[3]` | ℰ(↕(name, id, code hash)) |

"Remove all keys" (for `Zombify`):
- walk the ring from slot 0, stopping at the first empty slot, removing each slot and its results;
- then remove the counter and the registry.

The source comment says occupied slots always form a prefix of the ring. `DeleteItems` can break
that (see the open questions).

**Host calls made only for logging.** Every log line is `alloc::format!` followed by `log` (100).
The model treats 100 as an unknown host call (WHAT), so it changes only gas and ω₇. Some log lines
also call `gas` (0), and accumulate's first line calls `info` (6). These calls change nothing but
gas and registers, so the spec leaves them out, and the theorems say nothing about them beyond gas.
The formatting itself runs a lot of code, and allocates; see [risks](#risks).

### Things in the source you may not intend

These are what the code does, so the spec does them too. Each is a question for you
([open questions](#6-open-questions)).

1. **A failed `Zombify` still wipes the bookkeeping, and suppresses the final results write.** The
   keys are removed before the precondition check. The "zombified" flag is set before the
   instruction runs, whether or not it succeeds.
2. **`CreateService` reports `Err(Transfer)` but keeps the new service** if the endowment transfer
   fails. There is no checkpoint around the two calls.
3. **`DeleteItems` can delete bootstrap's own bookkeeping keys.** A hole in the ring then stops
   `remove_all_recent_work_items` early, and later entries leak.
4. **`AssignForGasCost` passes the length-prefixed encoding to `assign`.** The queue the host reads
   is shifted by the prefix, and is read past the end of the buffer. Its outcome depends on heap
   contents the spec does not track.
5. **`Bless`, `Upgrade` and `Yield` panic on failure** (SDK `expect`) instead of recording an
   error. For `Bless` this happens whenever bootstrap is not the manager.
6. **Refine passes internal variants through** (above).

---

## 2. The spec

`Services/Bootstrap/Spec.lean` (about 730 lines, no theorems, imports only `JAM.Params`). Its
parts:

| Definition | What it is |
| --- | --- |
| `Consts`, `Consts.ofParams` | 𝖰, the designate limit 3·𝖢, the ring size 2·𝖢·𝖨, and `randomKeys`, the one function the source leaves to a library (rand's `SmallRng`), taken as a parameter |
| `Instr`, `Ret`, `Err`, `Key`, `Preimage` | the source's types, constructor for constructor, in declaration order (constructor index = codec tag) |
| `Instr.encode`, `encodePayload`, `encodeOutput`, `Result.encode`, `Key.encode`, … | ℰ, using the model's `Codec.nat` and `Codec.fixed`, so lengths agree with the existing proofs |
| `Instr.WF` | the instructions ℰ encodes faithfully: field widths, hash/memo/keyset sizes, list lengths |
| `Dec`, `Dec.compact`, `Dec.instr`, `Dec.payload`, `Dec.output`, `Dec.item`, `decode` | the decoder the binary runs, as a `StateT Bytes Option` parser, including the lenient compact naturals |
| `Prog E α` | a program over host operations `E`: return, call an operation and continue with its reply, or panic. A monad, so the spec reads like the Rust |
| `ROp`, `refineInstr`, `refine` | refine's three host operations (historical lookup, import, export) and refine itself |
| `AOp`, `onInstr`, `onWorkItem`, `onTransfer`, `addRecent`, `removeAllKeys`, `accumulate` | accumulate's 19 host operations at the level of the SDK call, and accumulate itself |

**Why `Prog`.** The spec says which host calls bootstrap makes, in what order, with which
arguments, and what it does with each reply. It does not say what the host replies. That keeps it
small and readable. It also separates two concerns:
- **the binary refines the spec:** a statement about code;
- **the spec under the GP host functions has some effect:** a statement about the model, with no
  binary in it.

**What `AOp` abstracts.** An `AOp` is one SDK call. Several are two host calls:
- `read`, `lookup` and `fetchItems` query the length, allocate, then read;
- `info` fills a 96-octet buffer.

Replies are the SDK's Rust return types, with the error code dropped. bootstrap only tests for
success, except where it panics.

**How it was checked** (by `#eval` in a scratch file, not committed):
- encode/decode round trips on a sample of every kind of field;
- `[0] ⌢ salt` decodes to no instructions, and `refine` then gives `[0, i, 0]`, as `psiR_noinstr`
  proves of the binary;
- the empty payload fails to decode, as in `psiR_empty`;
- `[128, 1, 15] ⌢ salt` and `[255, 1, 0⁷, 15] ⌢ salt` decode as one `Checkpoint`;
- a length of 2³² is rejected, and tag 25 is rejected;
- a missing import makes `refine` panic;
- `accumulate` on one operand `[Checkpoint, Solicit]` plus one transfer makes the host calls
  fetch, read [0], read [1], write [1], write [0], write [2], checkpoint, write [2], checkpoint,
  solicit, write [2], read "t…", write "t…", write "t…". That matches the Rust line by line.

---

## 3. The target theorems

The statements below are **proposals**, written as code blocks rather than `theorem … := sorry`.
They use four definitions that step 1 of the plan would add, with no proofs:

```lean
/-- The looked-up preimage is a bootstrap binary: its code passes the deployed layout and
    `checkCode` for bootstrap's code facts, with heap bounds (48, 1044430). These are
    psiR_empty's hypotheses. For the vendored blob the kernel discharges them (step 10). -/
def IsBootstrap (l : List UInt8) : Prop

/-- Refine's host operations under the GP refine host functions:
    * historical_lookup through `Account.historicalLookup` at the lookup anchor;
    * imports from the item's import segments;
    * exports zero-padded and appended while the count stays within 𝖶_X.
    Replies are as the SDK reads them. -/
def RSem.run : Spec.Prog Spec.ROp Bytes → RSem.Env → Option (Bytes × List (List UInt8))  -- none = panic

/-- Accumulate's host operations under the GP accumulate host functions (`JAM.AccHost`), on the
    context (x, y) ∈ 𝕃². Each `AOp` is defined as the model's host function(s) applied to a memory
    holding its arguments. `run n` executes at most n operations, so it stops early if they run out
    (this models ∞). -/
inductive ASem.Stop | done | panicked | stopped
def ASem.run (n : Nat) : Spec.Prog Spec.AOp Unit → AccEnv → AccCtx → ASem.Stop × AccCtx

/-- What Ψ_A reports, without the gas: the regular dimension x after `done`, else the exceptional
    dimension y, which is the last checkpoint. This is GP eq. `accinvocation` with no hash
    returned. -/
def ASem.outcome : ASem.Stop × AccCtx → PartialState × List DeferredTransfer × Option (List UInt8) × Provisions
```

Small predicates that the statements name, such as `Instr.importIndices`, `Instr.Local`,
`Spec.ownKeys`, `credit` and `codeOf`, are one-line definitions that step 1 adds alongside these.

Throughout, `C = Consts.ofParams Params.full rk`, where `rk` is the `randomKeys` function (see open
question 1).

### T1. Refine, for every payload

> For every work item whose code is bootstrap, every core index c < 2¹⁶, item index i < 2¹⁶,
> service id < 2³² and **every payload y**, Ψ_R's result and exports are those of `Spec.refine C i
> y` under the GP refine host functions: the output and exports if it returns, ☇ and no exports if
> it panics. The other possibility is ∞.

```lean
theorem refine_spec (rk) (d : Accounts) (c i : Nat) (p : WorkPackage) (r : List UInt8)
    (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem) (l : List UInt8)
    (hw : p.items[i]? = some w)
    (hl : (d.get? w.service).bind (·.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList) = some l)
    (hboot : IsBootstrap l) (hc : c < 2^16) (hi : i < 2^16) (hs : w.service < 2^32) :
    let o := psiR Params.full d c i p r imports extrinsics off
    let s := RSem.run (Spec.refine C i w.payload.toList) (RSem.Env.of d p imports i off)
    (o.result, o.exports) = (match s with
                             | some (out, ex) => (.ok ⟨out.toArray⟩, ex)
                             | none => (.err .panic, []))
      ∨ (o.result = .err .outOfGas ∧ o.exports = [])
```

**T1′ (exact).** The same, without the ∞ case, when `w.refineGasLimit ≥ Spec.refineGas C y env`.
`refineGas` is an explicit bound, affine in |y|, the instruction count, the imported and exported
octets and the looked-up data, plus the host-call costs. It is defined in step 8. This is witness's
`refine_rejects_exact` pattern.

### T2. Accumulate, for every input

> For every state **e**, timeslot t < 2³², service s < 2³² whose code is bootstrap, gas g and
> inputs **i**, Ψ_A's state, transfers, yield and provisions are those of running
> `Spec.accumulate C t` for some number of host operations from I(**e**′, s), where **e**′ is **e**
> with the incoming transfers credited. If the run completes, the result is its final x. If it
> panics, or stops early, the result is its y: the state at its last checkpoint.

```lean
theorem accumulate_spec (rk) (η : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) (code : ByteArray)
    (hcode : codeOf (credit e s inputs) s = some code) (hboot : IsBootstrapCode code)
    (ht : t < 2^32) (hs : s < 2^32) :
    let o := psiA Params.full η e t s g inputs
    let x₀ := initImplications (credit e s inputs) s t η
    ∃ n, (o.state, o.xfers, o.yield, o.provisions) =
      ASem.outcome (ASem.run n (Spec.accumulate C t) (accEnv η t inputs code) (x₀, x₀))
```

"Some number n" is how gas enters: running out of gas can only cut the spec's run short, and roll
it back to a checkpoint. It never adds an effect the spec does not have.

**T2′ (exact).** With `g ≥ Spec.accGas …`, n can be taken as the full run's length, so the outcome
is `done` or `panicked` and does not depend on gas. Useful, but lower priority than T1′: on chain,
running out of gas in accumulate is a normal outcome.

**"Every valid work result."** T2 holds for every input, including operands whose output does not
decode (the spec panics on those). For the operands bootstrap's own refine produces, step 0 proves
`decode (Dec.output C) (encodeOutput is i) = some (is, i)` whenever `∀ x ∈ is, x.WF C`, and that
`refineInstr` keeps `WF`. So T1 and T2 together say what happens end to end.

### Safety properties, stated separately

Each is a corollary of T1 or T2 plus a lemma about the spec alone, with no binary in it. That
makes them cheap once T1 and T2 exist, and readable on their own.

**S1. Refine never panics on well-formed input.** For `y = encodePayload is salt ++ rest` with
every instruction `WF`, |salt| = 32, fewer than 2³² instructions, and every `Import` index present
among the item's imports: with enough gas, Ψ_R's result is
`.ok (encodeOutput (refined is) i)`, never ☇.

```lean
theorem refine_ok (…) (hwf : ∀ x ∈ is, x.WF C) (hn : is.length < 2^32) (hsalt : salt.length = 32)
    (himp : ∀ x ∈ is, ∀ q ∈ x.importIndices, q < (imports[i]?.getD []).length)
    (hgas : w.refineGasLimit ≥ Spec.refineGas …) (hy : w.payload.toList = encodePayload is salt ++ rest) :
    ∃ out ex, RSem.run (Spec.refine C i w.payload.toList) env = some (out, ex) ∧
      (psiR Params.full d c i p r imports extrinsics off).result = .ok ⟨out.toArray⟩
```

The output `out` is `encodeOutput is' i`, where `is'` is `is` with eager lookups, imports, exports
and random-storage requests replaced by what the host returned.

**S2. Refine rejects exactly the undecodable payloads.** If `decode (Dec.payload C) y = none`, the
result is ☇ (or ∞). This generalizes `psiR_empty` to every malformed payload.

**S3. Refine's gas is bounded.** `(psiR …).gasUsed ≤ Spec.refineGas …`, by the same bound as T1′.

**S4. Local instructions stay local.** If every operand's instructions are among the local ones
(`Checkpoint`, `Solicit`, `Forget`, `DeleteItems`, `Lookup`, `LookedUp`, `Imported`, `Exported`,
`Yield`, `RandomStorageAccumulate`, `Benchmark`, `Panic`), then Ψ_A:
- changes no account but s;
- changes none of the privileged fields (manager, assigners, delegator, registrar,
  always-accumulate, staging keys, authorizer queue);
- creates no transfers and no provisions.

In s's storage it writes only:
- bootstrap's own keys;
- the keys named by `RandomStorageAccumulate` items;
- `"count_random_storage"`, `"item-{t}-{i}"`, `"transfer-count"` and `"transfer{n}"`.

It removes only those keys and the keys named by `DeleteItems`. Witness's `accumulate_confined`
is the model: there it came from a scan for `ecalli`. Here it must come from the spec, because
bootstrap's binary contains every accumulate host call.

```lean
theorem accumulate_local (…) (hloc : ∀ o ∈ operandOutputs inputs, ∀ is k,
      decode (Dec.output C) o = some (is, k) → ∀ x ∈ is, x.Local) :
    let o := psiA Params.full η e t s g inputs
    (∀ s' ≠ s, o.state.accounts.get? s' = (credit e s inputs).accounts.get? s') ∧
    o.state.privileged = e.privileged ∧ o.xfers = [] ∧ o.provisions = ∅ ∧
    StorageChangesWithin (Spec.ownKeys t inputs) ((credit e s inputs).accounts.getD s default) (o.state.accounts.getD s default)
```

**S5. When accumulate does not panic.** Suppose:
- every operand's output decodes;
- no instruction is `Panic`;
- `Bless` appears only if s is the manager;
- every storage write succeeds, that is, s's balance stays above its threshold.

Then the run ends `done` (T2 with T2′), so every operand's results are stored. This is a lemma
about `Spec.accumulate` under `ASem`, carried over by T2.

**S6. Bootstrap's bookkeeping stays consistent.** "The occupied ring slots are `[0, c)`, or all of
them, where c is the stored counter, and each occupied slot's results key is either present or was
overwritten later" is preserved by accumulate, provided no `DeleteItems` key starts with octet 0–3
and has length 1, 5 or 35. This is the invariant the source comment relies on, and it shows the
`DeleteItems` caveat is the only way to break it. It is a statement about the spec alone.

**What is left out on purpose:**
- **Logs.** Their content is unobservable in the GP state.
- **Gas used by accumulate** beyond T2′.
- **Allocator internals.** The theorems are about Ψ_R and Ψ_A only.

---

## 4. The proof plan

### What exists and can be reused

| Piece | Where | Use |
| --- | --- | --- |
| The PVM/JAM model, Ψ_R, Ψ_A, host functions | `PVM/`, `JAM/` | the semantics; `ASem`/`RSem` are defined from `JAM.AccHost` and `RefineHost` |
| Code facts for the vendored blob, `checkCode_ok` | `Services/Bootstrap/Code.lean`, `CodeOk.lean` | every binary-level step |
| Gas-free runs and the lift to Ψ_M / Ψ_R | `PVM/Logic/`, `Services/Witness/Lift.lean`, `PsiRLift.lean` | composing runs into T1 and T2 |
| Refine's prefix, args decode, payload copy and halt | `Prefix`, `NoInstrArgs`, `NoInstrHead`, `NoInstrTail*`, `NoInstrFinish` | T1's beginning and end. The tails are per hex-digit count of the service id, from a log line |
| `decodeU32` (canonical ℰ(n)), `memcpy_small`, `memcpy_big_aligned`, the reader | `DecodeU32`, `Memcpy*`, `Reader*` | the codec layer |
| The decode loop for `Checkpoint` lists | `DecodeLoop` | the shape of the general decode loop (the frame, the 232-octet slot, the buffer) |
| picoalloc: model, `WF`, and `alloc`/`dealloc`/`realloc` refinement | `Services/Picoalloc/`, `Services/Bootstrap/Alloc/` | every allocation (section 5) |
| `refineContract`, `grow_heap` | `JAM/Theorems/RefineContract.lean`, `GrowHeap.lean` | the heap-growth host call |
| Witness's exact-gas pattern: `checkMaxBlockCost`, `gasBound` | `Services/Witness/PsiREmpty.lean` | T1′, S3 |
| `psiA_confined`, `psiR_noExports` | `JAM/Theorems/Confinement.lean` | pattern only; S4 needs the spec route |

### What is missing

1. **A heap model with contents.** The allocator theorems describe metadata (`Rep`). Bootstrap's
   correctness depends on the *data* in live blocks: the payload copy, the instruction `Vec`, the
   output buffer, the strings. We need:
   - a separation-style predicate, "these blocks are live and hold these octets";
   - the frame lemma for `alloc`, `dealloc` and `realloc` (other blocks' data unchanged);
   - `realloc`'s copied-data statement.

   whats-proven lists both as not yet stated.
2. **The general codec in the binary:**
   - the lenient compact decoder (all 9 prefix shapes, u32 and u64);
   - `Vec<u8>`;
   - the 25 instruction decoders, including every failure path to the `unwrap` trap;
   - the `AccumulateItem` decoder;
   - the encoders (`Instruction`, results, keys, registry).
3. **Loop invariants instead of unrolling.** The decode loop, the refine loop, accumulate's item
   and instruction loops, `DeleteItems`, `Export`, `Import` and the ring walk all run a
   data-dependent number of times. `DecodeLoop` has the pattern; it must be generalized from one
   element kind to all.
4. **Logging.** Every path formats and logs, as described under [risks](#risks).
5. **SDK host-call wrappers:** about 20 summaries, one per `AOp`/`ROp`. Each says what memory the
   wrapper passes to the host, and what it returns from the reply.
6. **The semantic bridge `RSem`/`ASem`**, with a lemma per operation tying it to `JAM.AccHost` /
   `RefineHost` on a memory holding the arguments.
7. **Gas** bounds for T1′/S3: block costs × step bounds, as for witness.

### Steps

Effort is relative: S < M < L < XL. Steps 0, 1 and 9 involve no binary.

| # | Step | Depends on | Effort |
| --- | --- | --- | --- |
| 0 | **Spec lemmas.** decode ∘ encode round trip under `WF`; `refineInstr` keeps `WF`; `Spec.refine` panics iff the decode fails or an import is missing | — | S |
| 1 | **Bridge.** Define `IsBootstrap`, `RSem`, `ASem`, `credit`, `codeOf`; one lemma per operation tying it to the model's host function | — | M |
| 2 | **SDK wrappers in the binary.** One summary per `ROp`/`AOp` (two-phase read/lookup/fetch, info, write/remove, …). Repetitive; a candidate for `genwitnesssteps`-style generation | 4a | M |
| 3 | **Codec in the binary.** Lenient compact (generalizing `decodeU32`), `Vec<u8>`, the 25 instruction decoders with failure paths, the item decoder, the encoders | 4a | L |
| 4a | **Heap with contents.** A live-blocks predicate over `Rep`, the frame for other blocks, `realloc`'s copy. Partly in progress elsewhere (copied data) | allocator work | L |
| 4b | **Lift the 14-page cap** (in progress elsewhere), so large payloads, preimages and outputs are covered | — | — |
| 5 | **Logging.** A frame-and-termination summary for every `format!` + `log` site: allocates only fresh blocks, frees them, changes no live data, terminates within a gas bound, calls only `log` | 4a | L–XL |
| 6 | **T1** (and S2): compose the prefix, the general decode loop, the refine loop (three host operations and the pass-through), the output encode and the halt; lift to Ψ_R | 2, 3, 4, 5 | M |
| 7 | **T2:** the entry, the items fetch and decode, the item loop, `on_work_item`, the 25 `on_instruction` branches, the ring and registry helpers; lift to Ψ_A with checkpoints | 2, 3, 4, 5 | L |
| 8 | **Gas:** block-cost bound for the blob (as `checkMaxBlockCost`), then `refineGas`; T1′, S3, S1. Optionally `accGas` and T2′ | 6 (7) | M |
| 9 | **Spec-level safety:** S4, S5 and S6 about `Spec.accumulate` under `ASem`, carried over by T2 | 1, 7 | S–M each |
| 10 | **The vendored blob:** discharge `IsBootstrap` for `jam-bootstrap-service.jam`, as witness's `refine_rejects` does | 6 | S |

**Suggested milestones,** each a usable statement:
- **M1:** T1 for payloads of pass-through instructions only (no refine host call). This builds on
  `DecodeLoop` and `NoInstr*`, and forces the general decode loop and the heap-contents layer.
- **M2:** T1 in full, then T1′ and S1–S3.
- **M3:** T2 for operands whose instructions are among `Checkpoint`, `Solicit`, `Forget`,
  `DeleteItems`, `Yield` and `Transfer`, plus transfers. This brings in the ring, the results
  writes and checkpoints, and gives S4 for that subset.
- **M4:** T2 in full, then S4–S6.

### Risks

- **Logging is on every path, and it is real code.**
  - Refine ends with `debug!("Returning {:?} into accumulate", out)`, which formats the *entire*
    output with derived `Debug`.
  - Accumulate formats every instruction (`PrettyInstruction`) and every result.
  - `NoInstr` already needed eight tails for one hex-formatted service id.

  A functional proof of the formatting is out of reach and not needed. What is needed is a generic
  frame/termination/gas summary for `core::fmt` as linked here. That is new and may be the largest
  single item. Mitigation: prove it once per formatting entry point, with the formatted value
  abstracted. The output is unobservable, so only memory safety and gas matter.
- **Proof size and build memory.** The current tooling produces per-path segment theorems. Bootstrap
  has far more paths: 25 tags, lenient lengths and data-dependent loops. Without loop invariants
  and generated per-function summaries, file count and elaboration memory will grow quickly.
  Already "some proof files take several GB".
- **The lenient decoder** roughly multiplies the length-decoding paths by nine. Option: do M1–M2 for
  canonical payloads first, then generalize (open question 3).
- **Heap growth.** Until the 14-page cap is parametrized, any allocation more than 56 KiB beyond the
  heap top is outside the proved allocator theorems. That includes:
  - payloads or outputs of that size;
  - `CreateService`/`Provide` code lookups (up to 𝖶_C ≈ 4 MB);
  - large `Lookup` data;
  - the accumulate inputs buffer.
- **Spec versus intent.** The spec is what the code does, including the quirks listed above. If any
  quirk is a bug you would rather have the spec reject, the theorem would then (correctly) fail.
  Decide before step 7.
- **Under-determined instructions.** `AssignForGasCost` reads heap contents the spec does not track.
  `RandomStorageRefine` needs `rand`'s `SmallRng` (Xoshiro256++ seeded by SplitMix64) as a Lean
  function, and a proof that the binary computes it.

---

## 5. The allocator assumptions against bootstrap

From [whats-proven.md](whats-proven.md#assumptions-and-limits):

| Assumption | Does bootstrap meet it? |
| --- | --- |
| **Alignment one unit (≤ 32 octets)** for `alloc` | **Yes, from the source.** Every type bootstrap allocates is aligned to 8 or less: `u8`, `u16`, `u32` and `u64` fields, `Vec`, `String`, the 232-octet `Instruction` enum, `Box<Hash>`, and the results. Nothing is `#[repr(align)]` or uses `u128`. So every Rust allocation is one unit, and `alloc_wrap_refines*` applies. **To confirm on the binary:** a scan of the alignment argument at every call to the `alloc` (40494) and `realloc` (40701) wrappers, cheap with the code facts. The model's any-alignment theorems are not needed. |
| **Heap growth ≤ 14 pages per call** (`hcost`; `hostCostMax` = 2000) | **No, in general.** Small runs fit: `psiR_noinstr`'s allocations are a few hundred octets. But allocations scale with the input: the payload copy (\|y\|), the instruction `Vec` (232 octets per instruction), the output and its encode buffer, the `debug!` string (several times the output), the accumulate inputs, `lookup` results (up to 𝖶_C = 4,000,000 octets for code), `Lookup` data, and 4104-octet import segments. "Every payload" therefore needs the parametrized cap now in progress. With it, the hypothesis becomes a gas condition (275 + 121 per page within the cap), which T1 and T2 absorb into "or ∞". Until then, T1 and T2 can be proved under a size hypothesis that keeps each growth within 14 pages. |
| **Writable heap and stack only** (`WrAt`, `HeapPages`) | **Yes.** This is how Y lays bootstrap out. `HeapPages` holds at the first allocation (`first_grows`) and is kept by each growth. |
| **Stack range and room** (sp ≥ 2147483800, below 2³²; 40–304 octets below sp; 8-aligned sp for the `realloc` fallback) | **Range: yes.** Bootstrap's stack is just below 2³² − 2¹⁶ (the decode loop's frame is at sp = 4278057688). **Room: probably yes, unproved.** The source has no recursion. `core::fmt` recursion is bounded by the nesting of the formatted types, at most about five levels here. The maximum stack depth at each allocator call site is still to be computed: a call-graph analysis over the code facts, new tooling of moderate size. 8-alignment of sp holds at the call sites seen so far and is to be checked per site. |
| **Heap base ≥ 206864, heap below 2³¹, `allocated < 2³¹`** | **Yes** for the base: picoalloc's chunk area starts at 206880 (`init_rep`). "Below 2³¹" is a size condition: it holds while the live heap stays under about 2 GB, which a gas bound or the size hypothesis gives. |
| **`req < 2³¹` units for `alloc_impl`** | **Yes:** only the public wrapper is called, and it passes ⌈size/32⌉ < 2³¹. |
| **`realloc` fallback needs ≥ 1 unit of usable size** | **Yes, from Rust's `RawVec`**, which never reallocates a zero-capacity buffer; it allocates instead. To confirm with the call-site scan. |
| **Alloc failure** (`alloc_refines_fail`) | **Needed only for the panic case.** Rust calls `handle_alloc_error`, which panics and traps. With heap bounds of (48, 1044430) pages, failure needs about 4 GB live. T1/T2 can either carry "☇ if the heap is exhausted" or rule it out with a size or gas bound (open question 4). |

**Is `realloc`'s copied-data statement needed? Yes, on the critical path of T1 and T2.** Bootstrap
relies on `realloc` preserving contents in at least these places:
- refine's output `Vec` (`vec![]`, then one `push` per instruction);
- the decoder's chunked `Vec` growth;
- every `format!` string, which grows as it is written;
- the registry's `push`.

`results` is allocated with capacity, so it does not reallocate. The frame lemma (data in *other*
live blocks unchanged across `alloc`, `dealloc` and `realloc`) is needed just as much, and is not
yet stated either. Both are step 4a.

---

## 6. Open questions

1. **Which instructions should the theorems cover?** The test-only ones are `RandomStorageRefine`,
   `RandomStorageAccumulate`, `Benchmark` and `AssignForGasCost`.
   - `RandomStorageRefine` needs `rand`'s `SmallRng` as a Lean function and a proof that the binary
     computes it.
   - `AssignForGasCost` has an outcome the spec cannot pin down.

   *Proposal:* keep them in the spec, as now, but exclude `RandomStorageRefine` and
   `AssignForGasCost` from T1 and T2 by hypothesis, and leave `randomKeys` a parameter. Or cover
   them only by the safety properties.
2. **Are the quirks intended?** These are the six items in
   [Things in the source you may not intend](#things-in-the-source-you-may-not-intend): the failed
   `Zombify` side effects, `CreateService` keeping the service after a failed transfer,
   `DeleteItems` on own keys, the `AssignForGasCost` prefix, `Bless`/`Upgrade`/`Yield` panicking,
   and refine passing internal variants through.
   - The spec follows the code. If any of them is a bug, should the spec say what was intended, so
     that the proof fails and the finding is reported upstream? Or should it keep the behaviour and
     only document it?
   - Items 1, 3 and 4 look like upstream candidates (`docs/upstream-candidates.md`).
3. **Every payload, or canonical payloads first?** "Every payload" means the lenient decoder, with
   about nine times the length paths. *Proposal:* M1–M2 for payloads of the form
   `encodePayload is salt ++ rest` plus S2 for malformed ones, then generalize.
4. **How should heap exhaustion and large inputs be treated?** The options:
   - (a) wait for the parametrized `grow_heap` cap, and allow "☇ if the heap is exhausted";
   - (b) a size hypothesis, for example every allocation within 14 pages of the top;
   - (c) a gas argument that rules exhaustion out.

   *Proposal:* (b) for the first milestones, then (a).
5. **Is a frame-only treatment of logging acceptable?** That is: memory safety, termination and gas,
   with log content unspecified. *Proposal:* yes. Log content is invisible in the GP state.
6. **Which safety properties matter most?** The candidates are S1 (no panic on well-formed input),
   S3 (refine gas), S4 (local instructions stay local), S5 (when accumulate completes) and S6 (ring
   invariant). *Proposal:* S1 and S4 first, as the clearest statements to show reviewers; S6 as a
   cheap spec-only result that documents the `DeleteItems` caveat.
7. **Is "∃ n" an acceptable form for accumulate?** It reads "the outcome of some prefix of the
   spec's run, rolled back to its last checkpoint". The alternatives are a gas bound for every
   input (T2′), or a trace-level statement: "the binary's sequence of state-changing host calls is
   a prefix of the spec's". *Proposal:* T2 as stated. The trace form is how step 7 would prove it
   anyway, and can be exported as a lemma.
8. **Should the spec live in the repository at all, or should it be the source?** The spec is a
   transliteration of about 400 lines of Rust (plus SDK and codec details), not an independent
   statement of intent. That is what makes T1/T2 "the binary does what its source says". If you
   want "the binary does what it should", someone has to write the intended behaviour
   independently. The quirks above are where the two would differ.
