# Logging in bootstrap: frame-only summaries of `format!` / `core::fmt`

Settled decision (Adam): logging has no effect on state or output and is left out of the spec.
So these proofs show only that each formatting function:
- terminates within a step bound;
- makes no host calls except `grow_heap` (inside the allocator);
- changes nothing except its stack frame, its own fresh allocations, the allocator's fields and
  headers, and the `String` it writes into.

**The text is never stated.**

## Interfaces (`Frame.lean`)

- `Keeps pb sp E s₀ μ₀ μ s`: the frame of a run.
  - Page access is kept outside the heap pages 48 … pb.
  - Non-writable octets there are kept (read-only data, for one).
  - Octets at or above sp are kept, except `E`.
  - The globals are kept (`Glob`).
  - Every allocated chunk of s₀ stays allocated in s, with its data.
  - `Keeps.trans'` composes frames, `Keeps.of_frame` builds one from explicit writes, and
    `Keeps.rebase` moves one to an earlier s₀.
- `Exhausts`: the run reaches an allocator wrapper's return with null where the model's call fails:
  40611 for `alloc`, 40821 for `realloc`.
- `AllocOk p R env pb S0 S1` and `ReallocOk …`: one call of each wrapper, as the summaries assume
  it. Every summary is generic in the host relation R.
  - `OracleRefine.allocOk_refine` proves `AllocOk` for refine's `refineContractK`.
  - The `ReallocOk` refine instance needs `ReallocCall.realloc_call`'s planned extra conjuncts:
    Glob kept, base kept, and the block fresh or the old one. `realloc_fresh` already proves the
    last two from the model.

## Proved, from these hypotheses

| Theorem | File | Function |
| --- | --- | --- |
| `write_str` | `Sink.lean` | `<String as fmt::Write>::write_str` (59959), with the reserve path 58615/58717 into `alloc`/`realloc`. The `String` invariant is `Str`. Bound: 7n + 2(cap' − cap) + 2000. |
| `pad_plain` | `Spec.lean` | `Formatter::pad_integral` (61857) with plain options, through a `Fmtr` (a `Formatter` into a `String`) |
| `hex32` | `Hex.lean` | `<u32 as LowerHex>::fmt` (60525) |
| `dec32` | `Dec*.lean` | `<u32 as Display>::fmt` (68146) |

## Next

1. `<u64 as Display>::fmt` (68449): the same shape as `dec32`. The loop runs up to 5 times with
   the u64 multiplier 3777893186295716171 (>> 11). It needs an induction like `hx_loop`.
2. `core::fmt::write` (64495): the byte-template interpreter. Bytes 1 … 127 are a literal,
   written with the vtable's `write_str`. 0xC0 is an argument with default options, called
   through its function pointer with a fresh `Formatter` at sp + 48. 0x80 is a long literal.
   Other bytes are an argument with explicit options. 0 ends the template.
   - Plan: a statement by induction on the template's remaining bytes, taking for each argument
     an `FmtSpec`-style hypothesis, which is the shape of `hex32` and `dec32`.
3. `alloc::fmt::format` / `format_inner` (59375): the capacity estimate (a loop over the
   template), `alloc`, then `core::fmt::write` with the `String` vtable 77016.
4. Accumulate's first line (6580 → 59375): `{:x}` (60525), Display (68146) and u64 Display
   (68449).
5. Refine's level-3 line (6159 → 59375): `Debug` of the output. That needs the `DebugStruct`,
   `DebugList` and `DebugTuple` builders and each `Instruction` variant's `Debug`.
