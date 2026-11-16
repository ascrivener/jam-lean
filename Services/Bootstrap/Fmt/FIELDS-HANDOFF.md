# Field formatters of refine's 6159 Debug line: paused (2026-11-16)

The formatter line is paused (Adam, decision 19): T1 keeps the field-formatter facts as named
hypotheses instead of discharging them. This note records what is proved and what remains.

## Proved (all build; axioms propext, Classical.choice, Quot.sound only)
- On main: `FieldSteps` / `Field` (`ref_bool_ok`, 37522), `U8x32` (`ref_u8x32_ok`, 36529), `FieldInt`
  (`u32_ok` 28822, `u64_ok` 28843, `ref_u32_ok` 37549; #213), `write_str_heap` (#216).
- PR "N56*" (#219): `N56Steps` (56340's 32 octet checks), `N56Checks` (`n56_checks`), `N56Len` (`n56_len`,
  the length before `from_utf8`), `FieldMemoScan` (`memo_scan`, 57485's prologue and first scan).
- PR "hex path" (#220): `FieldWriteSpec` (`fmt_write_spec`, explicit-options items), `FieldWriteChar`
  (`write_char`, 59743), `FieldPadWidth` (`pad_wp`, `pad_z2`), `FieldU8Hex` (`u8hex_ok`, 60209;
  `u8hexref_okW`, 57917), `FieldWriteNested` / `FieldWriteNestedPlain` (nested `core::fmt::write`),
  `FieldSliceHex` (`slice_hex_ok`, 57922), `FieldN56Hex` (`n56_hex`), `FieldN57Hex` (`n57_hex`).
  - **Named RO hypotheses added** (decision D3; in `docs/whats-proven.md`, discharged in step 10 like
    `FmtRO`): `RO70833` (octets 70833 … 70840, `{:02x}`) and `RO70824` (octets 70824, 70827, 70828,
    70832, `0x{}...`).
- PR "step 8" (#221): `opt_vec_28739_ok`, `ref_opt_vec_36534_ok`, `ref_code_26905_ok`,
  `ref_opt_u32_36594_ok`, `ref_input_36972_ok` (+ `u64b_ok`, 37857), `u16_ok` (28801) with `dec16`
  (67932), `ref_vecvec_26397_ok` (assumes each inner `Vec<u8>` ≤ L octets) and `ref_vecvec_core`.
  Also the `Fmt/README.md` fix: there is no field formatter 315 (74968 is tag 0's field-names array).

## Remains
- **M1 formatters 56340 and 57485** (and the derefs 33167 / 33162): the string paths need the
  `from_utf8` step bound (executor line, after #194). Left for 56340: its prologue 56340 … 56356 and the
  string path (56921 → `from_utf8` 57327 → `write(70818)` with a `&str` arg; `fmt_writeW` covers that
  write). Left for 57485: the search for the first 0 (57532 … 57549) and its two `from_utf8` calls
  (57618, 57552), then `write(70818)` at 57635. Then 56340 / 57485 as `RefOk`/`ArgOk`, and 33167 /
  33162 (2-instruction derefs, as `u8hexref_okW`).
- **Step 8, reached by T1's new kinds but not done**: 26605 and 36732 need the `DebugTuple` builder
  (61767 new, 65573 `field`, 65868 `finish`; unproved) and a `write_str` variant for an empty name
  (61767 passes src = 1, n = 0, which `write_str`'s `hsrc` does not admit); 36732 also needs 37158 (a
  336-octet struct with several fields). 29877 and 37611 need 56340. 36654 is drafted (below).
- **Drafts, not built** (on `claude/bootstrap-fields-3-wip`, commit "step 8, WIP"): the 36654 chain:
  `FieldStruct1Steps` / `FieldStruct1` (`s1_tail`, `ref_item_36917_ok`), `FieldVecItemSteps` /
  `FieldVecItem` (26504, `&Vec<Item>`), `FieldResultSteps` / `FieldResult` (37571 `"()"`, 37067
  `Output`, 36654). All step files compile. To finish: `FieldResult` needs `fo_r` / `fo_tail` to accept
  the returns 36693 and 36724; extending their `hi` disjunction breaks the `Or.inr …` literals in
  `FieldCode` / `FieldOptU32` (adjust those, or give 36654 its own return lemma), then build the tops.
- Not reached by the new kinds (T1, 2026-11-16): 26706, 36972 (done anyway).

## Survey (vtable `fmt` word at vt + 24, resolved through the jump table; RO base at .jam offset 92)

| formatter | what (tag) | status |
|---|---|---|
| 28739 | `Option<Vec<u8>>` (0) | done |
| 36534 | `&Option<Vec<u8>>` (18) | done |
| 26905 | `&Code`: `Hash([u8;32])` / `Inline(Vec<u8>)` (17) | done |
| 36594 | `&Option<u32>` (0) | done |
| 36972 | `&Input { seed: u64, nb_items: u8 }` (21) | done |
| 28801 | `<u16 as Debug>` (12, 24) | done |
| 26397 | `&Vec<Vec<u8>>` (5, 10, 19) | done |
| 36654 | `&Result<Output { items: Vec<Item { key: [u8;32] }> }, ()>` (22) | drafted |
| 26605 / 26706 | `&Vec<(u32, u64)>`-like via a tuple builder (11 / 9) | needs DebugTuple builder |
| 36732 | `BoundedVec(Vec<37158>, u64)` (13) | needs DebugTuple builder, 37158 |
| 29877 | `Vec<Hash>` via 33152 → 56340 (24) | needs 56340 |
| 37611 | `[a, b, …]` of hashes via 56340 (12) | needs 56340 |

## Tactics notes
- `post_simp` ends in `try rfl`, which can hang on goals left with a memory term; for runs with many
  stores split the run (e.g. `in36_a1` / `in36_a2`, `pz_a1` / `pz_a2`).
- `omega` hits max recursion on `x * 2^49 % 2^64 / 2^48 = 2x`; use `sh49` (`Dec16Steps`).
- Loops with a parametric per-element budget (Me, Ce): give `Nat.mul_succ` facts and one distributive
  fact (`dX` in `FieldVecVec`) so `omega` sees the products as atoms.
- Generators and the disassembler are in `Fmt/gen/` (`dis.py`; RO words: read the .jam at offset 92).
