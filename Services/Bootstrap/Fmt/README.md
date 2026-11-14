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
| `read_exact`, `rd_uN` | `ReadExact.lean` | a slice reader's `read_exact` (58434), `rd_u64` (46040), `rd_u32` (46008) |
| `FreeStepsH.infoSelf` | `InfoStep.lean` | the `info` (6) host step on the service itself, from `accContractK` (Ω_I) |
| `info_self` | `Info.lean` (steps in `InfoSteps.lean`) | accumulate's `info` call at 6501 (49454), frame-only, under `accContractK cap env` (703 ≤ cap) |
| `FreeStepsH.logAcc`, `log_site` | `LogSteps.lean`, `LogSite.lean` | the `log` (100) step under `accContractK` (ω₇ := WHAT, the message unspecified), and 6587 … 6630: `log`, then the `String`'s `dealloc` (`Decode.DeallocCall.dealloc_call`) |
| `acc_fmt_site` | `AccFmt.lean` | 6580 … 6630: `format!` of the template at 66464 (`accTmpl`) with its three arguments, `log`, `dealloc` |
| `acc_log_line` | `AccFmt.lean` | **accumulate's first log line, 6501 … 6630** (sp = 4278057152): `info_self`, `Acc.fmt_setup`, `acc_fmt_site`; from sp up only `logE` changes |

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
3. **Done: accumulate's first log line** (`acc_log_line`) (T2's `Acc/Args.lean`, sp = 4278057152):
   - **Done** (`info_self`). Its two preconditions on the context x, **for T2 to discharge** from
     Ψ_A's setup and the paper's typing (the code hash is in ℍ, so the record is 96 octets):
     `x.1.state.accounts.get? x.1.id = some a` and `(infoValue a).length < 2⁶⁴ − 9`.
   - `info(6)` summary at 6501 (→ 49454): the `info` host call that feeds the line. Logging only,
     so the summary keeps state and says only that the record at sp + 1600 is written.
     It has to be generic in R, with an `info` contract hypothesis like `AllocOk`.
   - `Acc.fmt_setup` (6508 → 6580) already sets up the call: ω₇ = sp + 744 (the `String`),
     ω₈ = 66464 (pieces), ω₉ = sp + 1144, and the argument pairs
     (sp + 260, 2616 → 60525 `hex32`), (sp + 256, 2800 → 68146 `dec32`),
     (sp + 1600, 2804 → 68449 `dec64`).
   - **For T2**: `acc_log_line` takes `AllocOk`/`ReallocOk` for `accContractK cap env` as hypotheses
     (the interface every Fmt summary uses), the template's 42 octets at 66464 (`accTmplBytes`), its
     readability, and `RoW` (the `String` vtable's words at 77040, 77048 and the read-only data's
     readability), all to be discharged from the accumulate start state, plus the two `info`
     preconditions above. Its context x' at 6630 is existential (the contract's `alloc` may in
     principle change it).
   - The `FmtOk` site is the call at 6580 (return 6587); then the `log` host call (100) at 6608
     with the message unspecified, then the `String`'s dealloc.
   - Compose these into one frame-only summary 6501 → after the dealloc, for T2.
4. **Refine's level-3 line** — in progress. Findings from the binary:
   - No level check: 6159 always formats. The one argument (sp + 272) is (sp + 248, 1382 → 29675),
     `<Vec<Instruction> as Debug>::fmt`: `debug_list` (61708), per element `entry` (66019) and
     `finish` (66310). Elements are 232 octets; the loop passes a frame slot holding the element's
     address with vtable 75784 (fmt 1264 → 26990, `<&Instruction as Debug>`): the niche tag (word at
     +0, 0x7fff… + t, jump table 67576), then per variant `debug_struct_fields_finish` (63820), the
     `debug_tuple_field*_finish` builders, or `write_str` (64485) for unit variants.
   - Refine's other `format!` sites: 4742 (covered by the generated BTail5 traces), the `Lookup`
     handler's 5398 and the `Export` handler's 5744 (`"Exported slice: {:?} -> {:?}"`, a `Vec<u8>`
     and a `Result<u64, HostCallError>`).
   - Done (`DebugList`, `VecDebug`, `DebugTuple`, `Dec8`, `ResultDebug`): the `DebugList` builders
     (`debug_list_new`, `debug_entry`, `debug_finish`), `debug_tuple1`
     (`debug_tuple_field1_finish`), `dec8` (u8 `Display`), and as arguments `vec_u8_ok`
     (`<&Vec<u8> as Debug>`) and `result_ok` (`<Result<u64, HostCallError> as Debug>`). An entry
     or field is formatted through a slot holding its address: `RefOk` (as `ArgOk`, the value
     reached through the slot), with `ref_u8_ok`, `ref_u64_ok`, `ref_hce_ok`. `ValAt` says where a
     value may lie (at or above the caller's frame, or in an allocated chunk of the caller's state).
   - Done (`OptionDebug`): `option_vec_ok`, `<Option<Vec<u8>> as Debug>` (17465, the `Lookup`
     line's argument: `None` when the first word is 2⁶⁴ − 1, else `Some(…)`), with
     `ref_vec_u8_ok` (`<&Vec<u8> as Debug>` as a `RefOk`). `RefOk`, `debug_entry` and
     `debug_tuple1` take the field's stack depth Z too (600 ≤ Z; 768 for a `Vec`).
   - Interface: `ArgOk`, `ArgsAt`, `fmt_write` and `format_inner` take the stack depth Z a function
     may use below its caller (sp ≥ S0 + Z and 2³¹ + Z; the earlier statements are Z = 600), and
     `ArgOk` has the premise W + 24 ≤ spA (every caller had it), so nested calls keep the caller's
     frame.
   - Next: `debug_struct_fields_finish`, the `Instruction` variants (table-driven), 29675, and
     `refine_debug_line` (6159 → 6209) taking the `Vec` at M + 248 and a per-element `DebugRep`
     (T1 proves `DebugRep` of its elements).
5. The `ReallocOk` refine instance, once `ReallocCall.realloc_call` gains its planned conjuncts
   (Glob kept, base kept, block fresh or old); `realloc_fresh` already proves the last two.


## Brief: the field formatters of refine's 6159 Debug line (for the field-formatter session)

Refine's level-3 line at 6159 formats the `Vec` at sp + 248 with `<Vec<Instruction> as Debug>`
(29675). Each 232-octet element goes through `<&Instruction as Debug>` (26990): the niche tag
(the word at +0 minus 0x7fff…ff, 25 variants) indexes the jump table at 67576, and each arm calls a
builder with its fields. **This session** does the builders (`DebugStruct::field` 65057,
`debug_struct_field1..5_finish` 62816 / 62972 / 63149 / 63347 / 63570, `debug_struct_fields_finish`
63820, the shared tails 28576 / 28280 / 27665 / 28458), the 25 arms, 29675 and
`refine_debug_line`. **The field-formatter session** proves each field formatter below as a
`RefOk` lemma in new files under `Fmt/` (e.g. `Fmt/Field<addr>.lean`), and edits no existing file.

**Interface.** `RefOk p P R env pb S0 S1 Z μA sA spA e a M C` (`DebugList.lean`, with Z from #184):
called at e with ω₇ = a slot v (sp ≤ v, v + 8 ≤ S1, disjoint from the `String` W) holding the field's
address a, and ω₈ = the `Formatter` F (`Fmtr`, plain options). It returns `Ok` (ω₇ = 0) to the return
address within 7n + 2·Δcap + C steps, having written n ≤ M octets (not stated), with the allocator's
context kept, `Keeps` from sp up except W … W + 24, and ω₀, ω₁, ω₅, ω₆ restored. Otherwise it
`Exhausts` within 2³⁰ + C. Where the field lies is a hypothesis via `ValAt` (on the caller's stack
or in an allocated chunk). See `ref_u8_ok`, `ref_u64_ok` (37589, done), `ref_hce_ok` and
`ref_vec_u8_ok` for worked examples; the composite ones reuse `debug_tuple1`, `debug_entry` /
`vd_loop` and (soon) the struct builders. Statements take Z (600 ≤ Z, or more if the formatter
nests) and say which read-only words they need (vtables' `fmt` words, as `option_vec_ok` does).
Code facts: all of these lie in `fnRangesF` (`Tests/GenWitnessSteps.lean`), so `CodeF` has them.

Field formatters (entry addresses; a vtable's `fmt` word resolves to them through the jump table):

| formatter | ~instructions to its first return (callees not counted) | used by tags |
|---|---|---|
| 315 | ~52 | 0 |
| 26397 | ~33 | 5, 10, 19 |
| 26605 | ~31 | 11 |
| 26706 | ~31 | 9 |
| 26905 | ~16 | 17 |
| 28739 | ~16 | 0 |
| 28801 | ~99 | 12, 24 |
| 28822 | ~93 | 2, 4, 8, 11, 17 |
| 28843 | ~87 | 0, 1, 2 |
| 29877 | ~30 | 24 |
| 33162 | ~232 | 2 |
| 33167 | ~230 | 4 |
| 36529 | ~18 | 14 |
| 36534 | ~16 | 18 |
| 36594 | ~16 | 0 |
| 36654 | ~15 | 22 |
| 36732 | ~25 | 13 |
| 36972 | ~29 | 21 |
| 37522 | ~93 | 8 |
| 37549 | ~84 | 3, 12, 24 |
| 37589 | ~72 | 1, 6, 7, 20 |
| 37611 | ~65 | 12 |
| 56340 | ~359 | 0, 1, 6, 7, 8 |
| 57485 | ~48 | 0 |

Arms (tag → arm entry → builder, or the shared tail it jumps to → the formatters of its fields, in
the order their vtables are loaded):

| tag | arm | builder / tail | field formatters (fmt entry) |
|---|---|---|---|
| 0 | 27058 | 63820 | 56340, 28843, 57485, 28739, 36594, 315 |
| 1 | 27937 | 63149 | 37589, 28843, 56340 |
| 2 | 27685 | 63347 | 33162, 28843, 28822 |
| 3 | 27852 | 28576 | 37549 |
| 4 | 27451 | 28280 | 33167, 28822 |
| 5 | 28134 | 28576 | 26397 |
| 6 | 28228 | 62972 | 37589, 56340 |
| 7 | 27883 | 28280 | 37589, 56340 |
| 8 | 28378 | 63149 | 37522, 56340, 28822 |
| 9 | 27570 | 28576 | 26706 |
| 10 | 28347 | 28576 | 26397 |
| 11 | 27294 | 63570 | 26605, 28822 |
| 12 | 27505 | 27665 | 37549, 37611, 28801 |
| 13 | 28197 | 28576 | 36732 |
| 14 | 27263 | 28576 | 36529 |
| 15 | 27824 | 64485 | — |
| 16 | 27235 | 64485 | — |
| 17 | 28049 | 28280 | 26905, 28822 |
| 18 | 28316 | 28576 | 36534 |
| 19 | 28547 | 62816 | 26397 |
| 20 | 28103 | 28576 | 37589 |
| 21 | 28165 | 62471 | 36972 |
| 22 | 28498 | 62471 | 36654 |
| 23 | 28607 | 64485 | — |
| 24 | 27601 | 28458 | 37549, 29877, 28801 |

**Milestone subset (do these first).** T1's `DebugLineOk` slot predicate (`MFixed` ∪ `Exported`)
admits only tags 1, 2, 3, 4, 6, 7, 8, 14, 15, 16, 20 and 23, so only these field formatters are needed:
28843, 56340, 33162, 33167, 28822, 37549, 37522, 36529 (37589 is done). The builders those arms use
are field2/3/4 (62972, 63149, 63347; `debug_struct2`–`4`, generated by
`scripts/gen_struct_fields.py`) and the tails 28576 and 28280.

Tags 15, 16 and 23 are unit variants (`write_str`, 64485). 37589 (`&u64`) is done (`ref_u64_ok`).
56340 is shared with T2's accumulate log sites.
