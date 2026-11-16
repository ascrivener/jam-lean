# Handoff: field formatters of refine's 6159 Debug line

## Current state (session 3, branch `claude/bootstrap-fields-2-wip`, 2026-11-16 ~09:30 UTC)
- **Open PRs**: #213 (FieldInt) and #216 (write_str_heap). #213's proofs job timed out on attempt 1 and
  resumed in attempt 2; #216 was on attempt 1. Merge each on green (subscribed in session 3).
- **Done this session** (all build, axioms clean; on the wip branch, after the session-2 commits):
  - `FieldPadWidthSteps.lean` / `FieldPadWidth.lean`: `pad_wp` (options 0x69000020, width w ≤ n: the
    plain path) and `pad_z2` (width 2, one digit: the zero-pad path, `write_char` of '0' then
    `write_str`, the options word saved and restored; `Keeps.restore`). `pz_a` had to be split
    (`pz_a1`, `pz_a2`): one 30-instruction run with 14 stores made `post_simp` time out.
  - `FieldU8HexSteps.lean` / `FieldU8Hex.lean`: `u8hex_okW` (60209 for a fixed String W) and
    `u8hex_ok` (`ArgOkO`, M 2, C 536875000: the C carries the exhaustion budget, the Ok path is
    ≤ 2(cap' − cap) + 3900); `FmtrO.congr`; `u8hexref_okW` (57917, `<&u8 as LowerHex>`).
  - `FieldWriteNested.lean`: **nested writes.** 57922 and 57346 call `core::fmt::write` from their own
    frames, with the arguments *below* the String, while `ArgOk`/`ArgOkO`/`fmt_write`/`fmt_write_spec`
    need W + 24 ≤ spA ≤ args. New, in my files only: `ArgOkW` (the caller's frame kept but for W, W a
    parameter; `ArgOkW.toO`), `ValAt.readableW`, `fmt_write_c3` (template = one 0xC3 item + end).
  - `FieldWriteNestedPlain.lean`: `ArgOkWp` (`ArgOkWp.toArgOk`), `ArgsAtW`, `WrLoopW`, `wr_itemW`,
    `wr_loopW`, `fmt_writeW`: Write.lean's loop copied under the nested frame (generated from
    Write.lean with substitutions, then fixed).
  - `FieldSliceHexSteps.lean` / `FieldSliceHex.lean`: `sh_loop`, `slice_hex_okW`, `slice_hex_ok`
    (57922 as `ArgOk`, M 2·len, C 1073741924 + 536875500·len), named hypothesis `RO70833`.
  - `FieldN56Hex.lean`: `n56_hex`, 56340 from 57346 to its return (≤ 21 octets), named hypotheses
    `RO70824`, `RO70833`.
  - `FieldN57Hex.lean`: `n57_hex`, 57485's hex path (57567 … the return), the same shape as `n56_hex`
    (80-octet frame, args at U, slice at U + 40, F in ω₅, the memo in ω₆).
  - `FieldMemoScan.lean`: `memo_scan`, 57485's prologue and first scan (128 octets: 32 ≤ b < 128 or 0
    goes on) to 57532 or 57567, memory written only in the frame.
  - Imports in `Services.lean` (FieldWriteSpec, FieldWriteChar and the new leaves); `docs/whats-proven.md`
    lists RO70833 and RO70824 under "In progress" (D3). A full local `lake build` (main@dd373c2 + the wip
    commits) was green before FieldN57Hex/FieldMemoScan; `lake build Services` green after them.
- **Tactics notes.** `post_simp` ends in `try rfl`, which hangs (whnf timeout, not caught by `try`) on
  any goal simp leaves with a memory term or `decodeLE (encodeLE 8 v)`. Add `rdN_lit8` / `rdN_lit4`
  (stores of literals), `Num.decodeLE_encodeLE, Nat.reduceMul, Nat.reducePow` and `Nat.mod_eq_of_lt`
  facts for every stored value. To find the culprit fast: replace the post block with a
  `simp (disch := pvm_arith) only [...]` (post_simp's list, no rfl), `trace_state`, `all_goals sorry`
  in a scratch copy (pvm_go itself takes ~20–40 s).
- **Next steps, in order:**
  1. PR 2 (N56Steps / N56Len / N56Checks + imports) and PR 3 (FieldWriteSpec, FieldWriteChar and this
     session's files) onto main after #213 / #216 merge (cherry-pick; the base must be main).
  2. 56340 as a whole: the string path (56921 → `from_utf8` 57327 → `write(70818)` at 57412 with a
     `&str` arg 2530) needs the from_utf8 step bound (after #194, from the executor line); the hex path
     is `n56_hex` + `n56_checks` (its prologue 56340 … 56356 still to state). Then 56340 / 33167 as
     `RefOk`/`ArgOk`. `fmt_writeW` covers 70818's write too.
  3. 57485: left are the search for the first 0 (57532 … 57549: a 0 at i → `from_utf8(memo, i)` at
     57618, none → `from_utf8(memo, 128)` at 57552; Err → 57567, Ok → `write(70818)` with a `&str`
     arg 2530 at 57635), all after from_utf8 blocked. 33162 / 33167 are 2-instruction derefs (load
     ω₇ from ω₇, jump to 57485 / 56340), like 57917 (`u8hexref_okW`), once 57485 / 56340 are done.
  4. The step-8 survey.
- **Context**: session 3 asked the parent for a restart at ~330k tokens; the PR events for #213 / #216
  go to whichever session is subscribed (re-subscribe in the new session).
- Local builds: `scripts/fetch-lake.sh` unpacked main@dd373c2; I worked on a local branch `local-build`
  = dd373c2 + the wip commits, and cherry-picked onto `claude/bootstrap-fields-2-wip` (base
  16b767f) to push.

## Session 2 state (superseded), branch `claude/bootstrap-fields-2`, 2026-11-16)
- **Open PRs (2026-11-16 ~03:00 UTC)**: #213 (FieldInt) and #216 (write_str_heap, D1). For both, the `model`
  job is green and the proofs build is running. Subscribe and merge each on green.
- **Branch layout**: `claude/bootstrap-fields-2-wip` = main@16b767f + write_str_heap (a81005a, = #216) + the
  FieldInt commit (= #213) + the N56* commits + FieldWriteSpec + FieldWriteChar + this note. After #213 and
  #216 merge, cherry-pick the rest onto main for the next PRs: PR 2 = N56Steps / N56Len / N56Checks
  (+ imports); PR 3 = FieldWriteSpec + FieldWriteChar (+ imports), once the hex-path pieces below are
  done or as they stand.
- **Next steps, in order**: FieldPadWidth (pad_integral with o = 0x69000020, w = 2: the plain path for 2
  digits, the zero-pad path for 1 digit using `write_char`); `<u8 as LowerHex>` 60209 as an `ArgOkO`;
  the 57922 slice loop (8 octets, `fmt_write_spec` per octet); 57346 (`fmt_write` 70824 with that arg);
  then, once the executor's from_utf8 step bound is on main, the string path and 56340 / 33167 as `RefOk`;
  then 57485 / 33162. After that, step 8 (non-M1 formatters).
- **Ready for PR 2**, on `claude/bootstrap-fields-2-wip` (based on main@16b767f, the published cache;
  cherry-pick onto main after #213 merges), full `lake build` green locally, axioms clean:
  - `N56Steps.lean` (P1): the 32 octet checks build (3 min). The store octets (8–30) read back their
    stack slot, so `pvm_go` needs `rdN_writeN_same8, rdN_zero, rdN_lit8` (in `gen/gen_n56.py`).
  - `N56Checks.lean` (`gen/gen_n56chain.py`): `n56_checks`, 56356 → 56921 or → 57346 in ≤ 224 steps.
  - `N56Len.lean` (P2, `gen/gen_n56len.py`): `n56_len`, 56921 → 57327 (the `from_utf8` call) in 134
    steps with ω₉ ≤ 32, ω₇ = sp + 200, ω₈ = ω₅ = a; writes only sp … sp + 16. Nine `pvm_go` chunks of 16
    instructions, register bounds from `gen/bounds.py`; bound goals closed by `n56l_bnd` after a light
    `simp only` (the generic `post_simp` times out on bitwise conditions).
  - Imports of N56Checks and N56Len in `Services.lean`.
- **Which formatters M1 needs.** Tag t is the t-th constructor of `Spec.Instr` (0 createService … 24
  assignForGasCost). M1's tags (`MFixed`) are 1, 2, 3, 4, 6, 7, 8, 14, 15, 16, 20 and 23, and besides
  what is on main they need only **56340** (code hashes: tags 1, 6, 7, 8; via 33167: tag 4) and
  **57485** (the transfer memo, via 33162: tag 2). The other formatters in the brief's table (315,
  26397, …) are for full T1 only.
- **Blocked or awaiting decisions** (sent to the parent 2026-11-15):
  - `from_utf8_call` / `from_utf8_ascii` (#194) have no step bound (`∃ k`), and RefOk needs one.
    Proposed: the executor adds k ≤ A·len + B.
  - D1: write_str with a heap source (the name lies in the `Vec<Instruction>`'s heap buffer). It is on
    `claude/bootstrap-fmt-sink-heap` (unmerged, old base). Recommended: rebase it and open its PR.
  - D2: explicit-spec `fmt_write` and pad_integral's width path, in new files of ours (recommended).
  - D3: FmtRO slices 70818, 70824, 70833, 71060, 71076, 71078 as named hypotheses (recommended).
- **Decisions (parent, 2026-11-15)**: D1 (a), the write_str_heap PR is **#216**. D2: new files of ours
  (FieldWriteSpec, FieldPadWidth); leave Write.lean and PadIntegral.lean alone. D3 (a): named RO
  hypotheses with exact (address, length), listed in docstrings, in `docs/whats-proven.md` and in the
  PR body (discharged in step 10, like FmtRO); don't edit FmtRO. from_utf8 step bound: the executor
  line adds it as a follow-up PR after #194, and the parent will say when it lands.
- **Hex path progress.** `FieldWriteSpec.lean` (builds, axioms clean): `FmtrO` / `ArgOkO` (a
  Formatter with options o, width w, precision 0), `SpecAt`, `wr_spec` (64611 → fn), `wr_spec_ret`
  (64843 → 64600), `wr_item_spec`, and `fmt_write_spec` (template = one 0xC3 item, then plain items).
- `FieldWriteChar.lean` (builds, axioms clean): **`write_char`** (59743, the `String` sink's
  write_char for c < 128): `Ok` with the `String` one octet longer within 2(cap' − cap) + 1600 steps,
  frame-only, or a failed allocator call. Pieces: `rt2g` / `wc_back` (reserve's end, any caller),
  `wc1` and `wc_reserve` (as Sink's `ws_reserve`, from 59815 to 59840), `wc_entry`, `wc_fast`,
  `wc_after` and `wc_post`.
- **Hex path, what remains:**
  - RO bytes (RO base in the .jam file at offset 92; RO starts at 65536): 70818 = `"{}"`
    (01 22 C0 01 22 00); 70824 = `0x{}...` (02 30 78 C0 03 2E2E2E 00); 70833 = C3, o = 0x69000020,
    w = 2, end byte at 70840; 71060 = "0123456789abcdef"; 71076 = "0x" (the prefix, unused without `#`).
  - 57346: `core::fmt::write`(70824) with the arg (slice (a, 8), 2534 → 57922). The hex path
    prints only the first 8 octets.
  - 57922 (slice Debug-as-hex): for len < 1027, a loop at 57976 over the octets: 64495(70833) with
    (&octet, 2532 → `<u8 as LowerHex>` 60209); an error goes to 58233, the end to 58215.
  - 60209: the digit loop (1 or 2 iterations), then pad_integral 61857 (digits at sp + 7 − k).
  - pad_integral with o = 0x69000020, w = 2: bit 21 (+) and bit 23 (#) are clear, so no sign and no
    prefix. With 2 digits (len ≥ w) it is the plain path (61994 → write_prefix → write_str), as
    `pi_a`/`pi_b`/`pi_c` but with o. With 1 digit, bit 24 (zero pad) gives 62076: the options are
    saved and set to fill '0'; write_prefix; a fill loop of w − len = 1 `write_char` (vtable +32 =
    2592 → jt 1295 → **59743**, String push; it grows through reserve 58615 like write_str, so it
    needs a `wc_reserve` like Sink's `ws_reserve`, reusing `rs2a`/`rs2b` with return 2594); then
    the digits via write_str (62219); the options are restored at 62248.
- Local builds: use a base matching the latest published `lake-cache` (`fetch-lake.sh` prints it;
  main after #192/#201/#204 is near-cold against it), and cherry-pick onto main before pushing.

The notes below are from session 1 (paused 2026-11-14).

The field-formatter session wrote this handoff note. The brief is the last section of `Fmt/README.md` (on `claude/bootstrap-fmt-6`).

## Done
- **PR #189** (`claude/bootstrap-fields-1`, head 878ebaf), open, not merged. It contains:
  - `FieldSteps.lean`: `f_u32` (28822), `f_u64` (28843), `rf_u32` (37549), `rf_bool` (37522 → 64029) and `pad_str` (`Formatter::pad` plain path, 64029 → write_str).
  - `Field.lean`: `ref_bool_ok : RefOk … 600 … 37522 a 5 2100`, with `ValAt … a 1`.
  - `U8x32Steps.lean` (generated by `gen/gen_u8x32.py`) and `U8x32.lean`: `ref_u8x32_ok : RefOk … Z … 36529 a 162 2147632648`, with `752 ≤ Z`, 32 octets by `ValAt`, and `rdN μA 76000 8 = 1788`.
  - Two import lines in `Services.lean`.
  - Checks: built locally with `lake build` of both modules; axioms are only propext, Classical.choice and Quot.sound. CI was pending when work paused. The local full `lake build` was started but stopped at the pause.

## In flight (this branch, `claude/bootstrap-fields-wip`, not built)
- `FieldInt.lean`: `u32_ok` (28822, ArgOk, M 10, C 2710), `u64_ok` (28843, ArgOk, M 20, C 2910) and `ref_u32_ok` (37549, RefOk, M 10, C 2710), all with `ValAt`.
  - It needs #187 (fmt session's `claude/bootstrap-fmt-dec`: `dec32`/`dec64` take a value below the frame) to be merged first. It is uncompiled.
  - Next step: after #187 merges, start a branch from main, take `FieldInt.lean`, add its import to `Services.lean`, build it, then open a PR.
- `N56Steps.lean` (generated by `gen/gen_n56.py`): the 32 per-octet checks of 56340 (`n56_0` … `n56_31`), each going to the next check or to the hex path 57346. It is uncompiled.
  - In scratch tests, a single octet's three cases closed by `pvm_go` with `sx8_signed` and the case hypothesis.

## Next steps (plan agreed with the parent; estimate ≈ 7 days)
Order: the 56340 string path, then the hex path, then a PR for 56340 + 33167, then 57485 + 33162.
1. **P1**: compile `N56Steps.lean`. If the post-goals time out, replace `post_simp` with explicit tactics, as `pad_str` does.
2. **P2** (56921 → 57327, about 110 straight-line ALU/cmov instructions): it computes the length without trailing NULs, which goes to `from_utf8` in ω₉.
   - Only `len ≤ 32` is needed. Every value in it is a 0/1 flag or a constant ≤ 32.
   - Plan: pvm_go in chunks of about 15 instructions, abstracting the registers to bounded values between chunks. `gen/trace.py` shows the dataflow.
3. **P3**: `str::from_utf8` (60681) for n ≤ 32: termination, frame, Ok or Err.
4. **P4a**: `core::fmt::write`, template 70818 = [lit 1, arg, lit 1], with the arg `<str as Display>` (57901 → 65046 → `pad_str` → write_str).
   - **Blocked:** `write_str`'s `hsrc` allows only RO data or the stack, not a heap chunk. The fmt session was asked to widen it.
5. **Hex path** (57346): template 70824 = [lit 2, arg, lit 3], with the arg 57922. 57922 is a loop calling `core::fmt::write` on template 70833, which has one explicit-options arg (`{:02x}`), `<u8 as LowerHex>` 60209, then pad_integral with width.
   - It needs fmt_write for explicit-spec items. The parent's default is a new file of ours, unless fmt prefers to extend `Write.lean`; fmt was asked and had not answered.
   - It also needs pad_integral's width path.
6. **57485** (128 octets, real loops at 57511 and 57537) and its derefs **33162** / **33167**.

## Open decisions and dependencies
- #187 (fmt) must merge before `FieldInt.lean`.
- The `write_str` heap-source widening (fmt).
- The explicit-spec fmt_write: new file, or fmt extends `Write.lean`.
- RefOk/ArgOk have a single C for both the Ok bound and the Exhausts budget, which forces C ≈ 2^31 in `ref_u8x32_ok`. The parent asked about this; the suggestion was separate C_ok and C_exh (fmt/T1 interface).
- RO slices for FmtRO (owned by fmt):
  - #189 needs only 76000.
  - The 56340 work will need 70818, 70824, 70833, 71060, 71076 and 71078.

## Tooling notes
- `gen/dis.py` prints instructions from the code facts (`python3 gen/dis.py <pc> <n>`).
- `pvm_go` runs fast; the generic `post_simp` can blow up after stack stores, and explicit `rw`/`simp only` per goal fixes it.

## Updates received just before the pause
- #187 is merged (squash 12a33d0), so `FieldInt.lean` is unblocked. `ref_u64_okV` (37589) is on main and belongs to the fmt session.
- `write_str_heap` is on branch `claude/bootstrap-fmt-sink-heap` (1d10116; the fmt session opens its PR after the full build).
  - Its third `hsrc` disjunct is `∃ d ∈ chunks s₀, d.used = true ∧ d.addr + 32 ≤ src ∧ src + n ≤ d.addr + 32 * d.size`.
  - Once it merges, P4a is unblocked.
- The fmt session agreed that the explicit-spec fmt_write goes in a new file of ours.
- The parent accepted the ≈7-day plan.
  - Until fmt answers on C_ok/C_exh, keep C as it is.
  - Note the real Ok-path bound (~148,100 for `ref_u8x32_ok`) in each docstring, so it's easy to restate later. This is not yet done in #189.
- Send fmt the exact (address, length) slices for 70818, 70824, 70833, 71060, 71076 and 71078 once those lemmas are stated (FmtRO is on `claude/bootstrap-fmt-ro`).
