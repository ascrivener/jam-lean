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
| `dec64` | `Du*.lean` | `<u64 as Display>::fmt` (68449) |
| `hex32_ok`, `dec32_ok`, `dec64_ok` | `Template.lean` | the three above as `ArgOk` arguments |
| `fmt_write` | `Write.lean` (steps in `WriteSteps.lean`) | `core::fmt::write` (64495) into a `String`, over a template `Tmpl` of literals and default-option arguments, each argument an `ArgOk`. Bound `tcost M C ts + 100 + 2(cap' − cap)`. |
| `format_inner` | `Format.lean` (steps in `FormatSteps.lean`) | `alloc::fmt::format_inner` (59375): `FmtCall` within `fmtCost M C ts` steps |

### Templates and arguments (`Template.lean`)

- `Tmpl μ tp ts`: the byte template at tp holds the items ts (`TItem.lit n`, 1 ≤ n < 128, or
  `TItem.arg`, the byte 0xC0), then 0. The bytes 0x80 (long literal) and explicit-option arguments
  are not covered: the templates the logging calls use (66464, 66099) have none.
- `ArgOk … μA sA spA e v M C`: an argument's function e with value v, from any memory reached from
  the caller's (μA, sA) keeping its frame at or above spA, returns `Ok` with the `String` at most M
  octets longer within 7n + 2(cap' − cap) + C steps, or `Exhausts`.
- `ArgsAt … args i ts M C`: the (value, function) pairs at args + 16 j, in the caller's memory.

### `FmtCall` (`Format.lean`)

`StrOut s s' μ' O` lives in `Format.lean`, not `Frame.lean`, because `Str` is defined in `Sink.lean`.
`FmtCall p R env pb S0 S1 ω μ x s sp O t N` is the agreed interface:

```
(∃ ω' μ' x' s', FreeStepsH p R 59375 ω μ x t ω' μ' x' N ∧ HeapCtx env pb S0 S1 μ' s' ∧
   s'.base = s.base ∧ Keeps pb sp (fun a => O ≤ a ∧ a < O + 24) s μ μ' s' ∧ StrOut s s' μ' O ∧
   ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
 Exhausts p R pb 59375 ω μ x N
```

`format_inner` needs: sp = S with S0 + 800 ≤ S, S % 8 = 0, 2147484500 ≤ S ≤ S1; O at or above S with
O + 24 ≤ S1; `RoW μ` (the `String` vtable's words and the read-only data readable); the template
in the read-only data; even args; `ArgsAt … μ s S args 0 ts M C`; `tlen M ts < 2²⁷`.

## Handoff plan

Status: everything above is proved, including steps 1 and 2 below. Pick up at step 3.

### The interface the callers expect (agreed with T1 and T2)

`FmtCall` for a call of `alloc::fmt::format` / `format_inner` at 59375 with return address t,
output `String` at O (ω₇), pieces ω₈ and arguments ω₉, generic in R:

```
(∃ ω' μ' x' s', FreeStepsH p R 59375 ω μ x t ω' μ' x' N ∧ HeapCtx env pb S0 S1 μ' s' ∧
   s'.base = s.base ∧ Keeps pb sp (fun a => O ≤ a ∧ a < O + 24) s μ μ' s' ∧ StrOut s s' μ' O ∧
   ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
 Exhausts p R pb 59375 ω μ x N
```

`StrOut s s' μ' O` (not yet defined; it belongs in `Frame.lean`) says O holds a `String` (`Str` with some cap and len) whose buffer is a chunk
allocated in s' and fresh against s. The text stays unstated.

### Steps

1. **Done** (`fmt_write`). `core::fmt::write` (64495): the byte-template interpreter. Bytes 1 … 127 are a literal,
   written with the vtable's `write_str`. 0xC0 is an argument with default options, called
   through its function pointer with a fresh `Formatter` at sp + 48. 0x80 is a long literal.
   Other bytes are an argument with explicit options. 0 ends the template.
   - Plan: induction on the template's remaining bytes, taking for each argument an
     `FmtSpec`-style hypothesis (the shape of `hex32`, `dec32` and `dec64`: from the call with
     a `Fmtr`, return with the `Fmtr` at a larger len, `Keeps`, or `Exhausts`).
   - The arguments are dispatched through jump-table addresses (`jte_k` facts in CodeF).
2. **Done** (`format_inner`). `format_inner` (59375): the capacity estimate (a loop over the template), `alloc` through
   `AllocOk`, then `core::fmt::write` with the `String` vtable 77016. Gives `FmtCall`.
3. **Accumulate's first log line** (T2's `Acc/Args.lean`, sp = 4278057152):
   - `info(6)` summary at 6501 (→ 49454): the `info` host call that feeds the line. Logging only,
     so the summary keeps state and says only that the record at sp + 1600 is written.
     It has to be generic in R, with an `info` contract hypothesis like `AllocOk`.
   - `Acc.fmt_setup` (6508 → 6580) already sets up the call: ω₇ = sp + 744 (the `String`),
     ω₈ = 66464 (pieces), ω₉ = sp + 1144, and the argument pairs
     (sp + 260, 2616 → 60525 `hex32`), (sp + 256, 2800 → 68146 `dec32`),
     (sp + 1600, 2804 → 68449 `dec64`).
   - The `FmtOk` site is the call at 6580 (return 6587); then the `log` host call (100) at 6608
     with the message unspecified, then the `String`'s dealloc.
   - Compose these into one frame-only summary 6501 → after the dealloc, for T2.
4. **Refine's level-3 line** (6159 → 59375, return 6166; ω₇ = M + 168, ω₈ = 66099,
   ω₉ = M + 272; Debug fn 1382 → 29675): `Debug` of the output. That needs the `DebugStruct`,
   `DebugList` and `DebugTuple` builders and each `Instruction` variant's `Debug`.
5. The `ReallocOk` refine instance, once `ReallocCall.realloc_call` gains its planned conjuncts
   (Glob kept, base kept, block fresh or old); `realloc_fresh` already proves the last two.
