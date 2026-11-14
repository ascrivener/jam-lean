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
  **Known looseness:** one constant C serves as both the `Ok` step bound (7n + 2(cap' − cap) + C)
  and the `Exhausts` budget (2³⁰ + C). Exhaust budgets compound across nested allocations (for
  example, 1.5 · 2³⁰ in `debug_entry`), so C, and with it the `Ok` bound, ends up near 2³¹ even
  where the `Ok` path takes far fewer steps. The same holds for `RefOk` and `vec_u8_ok`. This is
  sound but useless for exact gas. Planned fix, at exact-gas time and additive only: an `ArgOk2`
  with separate C_ok and C_exh, with the leaves and composition lemmas re-proved against it and
  `ArgOk` derived as a corollary (C := max). Nothing existing changes.
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

## Handoff (2026-11-14, work paused for the account move)

### Done (on main)
#170, #184 (DebugList, VecDebug, DebugTuple, Dec8, ResultDebug, OptionDebug, OracleRefineK, RefOk with Z),
#187 (dec32/dec64 accept values in heap chunks; `ref_u64_okV`).

### In flight
- **#188**, branch `claude/bootstrap-fmt-6`, head 2524a6b (merged with main *before* #187). Open; CI was
  running. Contents:
  - DebugStruct (`FieldOk`, `debug_field`) and StructField1–4 (generator
    `scripts/gen_struct_fields.py`);
  - InstrDebug: the `<&Instruction as Debug>` (26990) arms for tags 15, 16, 20 and 23;
    InstrDebugSteps holds the step lemmas for tags 1, 2, 3, 4, 6, 7, 8 and 14;
  - VecInstr (`vec_instr_ok`, 29675);
  - RefineDebugLine (`rdl_post`, 6166 → 6209);
  - FmtRO.

  A local full build reached 2602/2612 with no errors before it was stopped. Next step: merge
  origin/main (it now has #187, which changed the imported Template and ResultDebug), full build,
  and merge on green.
- **Branch `claude/bootstrap-fmt-ro`**, 8c2561d: FmtRO.lean alone, plus its Services.lean import,
  from main. No PR yet. T1 asked for it so Refine can import `FmtRO`. Open the PR (or let #188
  carry it) after a full build.
- **Branch `claude/bootstrap-fmt-sink-heap`**: `write_str_heap`, Sink.lean only (compiles; full build not yet run), this
  note, and the C-looseness note above. hsrc gains a third disjunct: a source in an allocated chunk of s₀.
  `write_str` is unchanged, as a corollary. The field-formatter session needs it for 56340/57485.
  No PR yet.

### Next steps (my assignment, parent's option B)
1. The remaining 26990 arms, as their field formatters land:
   - 56340: tags 1, 6, 7, 8;
   - 28843/28822 (dec32/dec64 `ArgOk` at heap addresses, now possible after #187): tags 1, 2, 4, 8;
   - 33162/33167: tags 2, 4;
   - 37549: tag 3;
   - 36529 (`ref_u8x32_ok`, #189, Z ≥ 752): tag 14;
   - 37522 (`ref_bool_ok`, #189): tag 8.

   The step lemmas are in InstrDebugSteps; compose with `debug_struct{1..4}` / `FieldOk` as
   `instr20_ok` does.
2. `refine_debug_line` (6159), discharging T1's `DebugLineOk`. Ingredients:
   - the ro premise, via `FmtRO`;
   - S0 + 7560 ≤ M;
   - `refineKeep` → `refineContractK`;
   - element `RefOk` from `DR` via the arms, with a uniform Ze and `RefOk.mono`.

   Report the actual max stack depth to the parent and T1; above 7560 is a model/binary finding.
3. The 4742 `ArgsLineOk` site (template 66657, arg fmt 2616; needs s'.base = s.base), then T1's
   Export 5744 and Lookup 5398 sites (`ExportFmtOk`).

### Open dependencies and decisions
- The field-formatter session (session_017ptjPC1ZVytPi3sRR7WgBe) owns the field formatters,
  #189, and an explicit-spec `fmt_write` in its own file (agreed). It will send exact RO slices:
  70818, 70824, 70833, 71060, 71076, 71078. Add them to FmtRO as new conjuncts.
- The C_ok / C_exh split is deferred to exact-gas time and will be additive (`ArgOk2`), as the
  parent agreed.
