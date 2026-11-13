import Services.Bootstrap.Fmt.Tac

/-!
# `core::fmt::write` (64495): its steps

`core::fmt::write(out, vtable, template, args)` interprets a byte template. Its arguments:
- ω₇: the sink's data pointer (the `String`, W);
- ω₈: the sink's `fmt::Write` vtable (77016 for `String`);
- ω₉: the template;
- ω₁₀: the arguments, an array of (value, formatting function) pairs, 16 octets each, at an even
  address (an odd ω₁₀ is a static string, not followed here).

Each template byte starts an item:
- 0 ends the template;
- 1 … 127 is a literal of that many octets, which follow; it goes to the vtable's `write_str`;
- 0xC0 is the next argument with default options: its function is called with the value and a
  fresh `Formatter` at T + 48;
- 0x80 (a long literal) and the other bytes (an argument with explicit options) are not followed:
  the templates the logging calls use have none.

The frame is 96 octets at T = sp − 96:
- T + 0: the default options word 0x60000020;
- T + 8: the vtable; T + 16: the arguments; T + 24: the next argument's index;
- T + 32: the vtable's `write_str`; T + 40: W;
- T + 48 … T + 72: the `Formatter` handed to an argument;
- T + 72, T + 80, T + 88: ω₆, ω₅, ω₀.

These are the steps:
- `wr_entry`: 64495 … 64611, a template with a first item;
- `wr_entry0`: 64495 … the return, an empty template;
- `wr_head`: 64600 … 64611, the next item;
- `wr_end`: 64600 … the return, the template's end;
- `wr_lit`: 64611 … `write_str` (59959), a literal;
- `wr_lit_ret`: 64633 … 64600, after the literal;
- `wr_arg`: 64611 … the argument's function, an argument;
- `wr_arg_ret`: 64589 … 64600, after the argument.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word read as its first m octets and the n after them. -/
theorem readN_add' (μ : Memory) (a m n : Nat) : μ.readN a (m + n) = μ.readN a m ++ μ.readN (a + m) n := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_assoc]

theorem rdN_add (μ : Memory) (a m n : Nat) : rdN μ a (m + n) = rdN μ a m + 256 ^ m * rdN μ (a + m) n := by
  unfold rdN
  rw [readN_add', decodeLE_append, Memory.length_readN]

/-- The default options word 0x60000020, read as a `Formatter`'s options (4 octets) and width
    (2 octets). -/
theorem rdN_opts {μ : Memory} {a : Nat} (h : rdN μ a 8 = 1610612768) :
    rdN μ a 4 = 1610612768 ∧ rdN μ (a + 4) 2 = 0 := by
  have e1 := rdN_add μ a 4 4
  have e2 := rdN_add μ (a + 4) 2 2
  have l1 := rdN_lt μ a 4
  have l2 := rdN_lt μ (a + 4) 2
  have l3 := rdN_lt μ (a + 4 + 2) 2
  simp only [show (4 : Nat) + 4 = 8 from rfl] at e1
  simp only [show (2 : Nat) + 2 = 4 from rfl] at e2
  omega

/-- 64495 … 64548, a template whose first byte b is not 0: the 96-octet frame at T = S − 96
    (ω₀, ω₅, ω₆ at T + 88, T + 80, T + 72; the arguments at T + 16; index 0 at T + 24; the vtable at
    T + 8 and its `write_str` at T + 32; the options word at T; W at T + 40), and a jump to 64611
    with b in ω₅, the template in ω₉ and W in ω₁₂. -/
theorem wr_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (S W tp args b r0 v5 v6 : Nat) (hS : 196608 + 96 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat 77016)
    (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      W < 18446744073709551616 ∧ tp < 4294967296 ∧ args < 18446744073709551616 ∧ args % 2 = 0)
    (hb : rdN μ tp 1 = b) (hb0 : b ≠ 0) (hrt : μ.readable tp = true) (htS : tp + 1 ≤ S - 96)
    (hws : rdN μ 77040 8 = 2596) (hrws : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, S - 96 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64495 ω μ x 64611 ω' μ' x 22 ∧
      ω'[1] = UInt64.ofNat (S - 96) ∧ ω'[5] = UInt64.ofNat b ∧ ω'[9] = UInt64.ofNat tp ∧
      ω'[12] = UInt64.ofNat W ∧
      rdN μ' (S - 96) 8 = 1610612768 ∧ rdN μ' (S - 96 + 8) 8 = 77016 ∧
      rdN μ' (S - 96 + 16) 8 = args ∧ rdN μ' (S - 96 + 24) 8 = 0 ∧ rdN μ' (S - 96 + 32) 8 = 2596 ∧
      rdN μ' (S - 96 + 40) 8 = W ∧ rdN μ' (S - 96 + 72) 8 = v6 ∧ rdN μ' (S - 96 + 80) 8 = v5 ∧
      rdN μ' (S - 96 + 88) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < S - 96 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 96 ≤ a → a < S → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hbl : b < 256 := by rw [← hb]; exact rdN_lt μ tp 1
  have ha1 : args % 2 = 0 := hv.2.2.2.2.2.2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, hS, hv, hb, hb0, hbl, hrt, htS, hws, hrws, hw, hr, ha1, bitwise_and_m1,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      h8, h9, h10, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2.1]

/-- 64495 … 64522 and 64880 … the return, an empty template (first byte 0): the frame's words
    stored, `Ok` (ω₇ = 0) returned to t with ω₀, ω₅, ω₆ restored. -/
theorem wr_entry0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (S tp args r0 t v5 v6 : Nat) (hS : 65536 + 96 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      tp < 4294967296 ∧ args < 18446744073709551616 ∧ args % 2 = 0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hb : rdN μ tp 1 = 0) (hrt : μ.readable tp = true) (htS : tp + 1 ≤ S - 96)
    (hw : ∀ a, S - 96 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64495 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → (a < S - 96 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 96 ≤ a → a < S → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha1 : args % 2 = 0 := hv.2.2.2.2
  have hr0 : r0 < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h9, h10, hS, hv, hb, hrt, htS, hw, hr, ha1, hr0, hret, hjt, hbt, bitwise_and_m1,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, h0, h1, h5, h6, h9, h10]

/-- 64600 … 64607, the next item: its first byte b ≠ 0, read from the cursor c (ω₆), goes to ω₅,
    c to ω₉ and W (T + 40) to ω₁₂. -/
theorem wr_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T W c b : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296) (hc : c < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat c) (hb : rdN μ c 1 = b) (hb0 : b ≠ 0)
    (rW : rdN μ (T + 40) 8 = W) (hrc : μ.readable c = true)
    (hr : ∀ a, T + 40 ≤ a → a < T + 48 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 64600 ω μ x 64611 ω' μ x 4 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat b ∧ ω'[9] = UInt64.ofNat c ∧
      ω'[12] = UInt64.ofNat W := by
  have hbl : b < 256 := by rw [← hb]; exact rdN_lt μ c 1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hT, hc, hb, hb0, hbl, rW, hrc, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [Nat.mod_eq_of_lt (rdN_lt64 μ (T + 40))]

/-- 64600 … 64607 and 64880 … the return, the template's end (byte 0 at the cursor c): `Ok`
    returned to t, with ω₀, ω₅, ω₆ restored from the frame and sp back to T + 96. -/
theorem wr_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T c r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296) (hc : c < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat c) (hb : rdN μ c 1 = 0)
    (r0' : rdN μ (T + 88) 8 = r0) (r5 : rdN μ (T + 80) 8 = v5) (r6 : rdN μ (T + 72) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hrc : μ.readable c = true)
    (hr : ∀ a, T ≤ a → a < T + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 64600 ω μ x t ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hT, hc, hb, r0', r5, r6, hret, hjt, hbt, hrc, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [Nat.mod_eq_of_lt (rdN_lt64 μ (T + 88)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 80)),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 72))]

/-- 64611 … 64628, a literal (1 ≤ b < 128 at the cursor c): `write_str` (59959, through 2596 at
    T + 32) called with W, the b octets at c + 1, and the return address 2728 (64633); b and c + 1
    stay in ω₅, ω₆. -/
theorem wr_lit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T W c b : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296) (hc : c + 1 < 4294967296)
    (hb : 1 ≤ b ∧ b < 128) (hW : W < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat b) (h9 : ω[9] = UInt64.ofNat c)
    (h12 : ω[12] = UInt64.ofNat W) (rws : rdN μ (T + 32) 8 = 2596)
    (hr : ∀ a, T + 32 ≤ a → a < T + 40 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 64611 ω μ x 59959 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 2728 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat b ∧
      ω'[6] = UInt64.ofNat (c + 1) ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (c + 1) ∧
      ω'[9] = UInt64.ofNat b := by
  have hsx : sx8 b = b := sx8_of_lt b hb.2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h9, h12, hT, hc, hb, hW, rws, hr, hsx, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [hsx, Nat.mod_eq_of_lt hW, h1, h5, h9, h12]

/-- 64633 … 64640, after a literal's `Ok`: the cursor moves to c + 1 + b (ω₆) and the loop goes on
    at 64600. -/
theorem wr_lit_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (c b : Nat) (hc : c + 1 + b < 4294967296)
    (h5 : ω[5] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat (c + 1)) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 64633 ω μ x 64600 ω' μ x 3 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[6] = UInt64.ofNat (c + 1 + b) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, h7, hc]
  · refine ⟨?_, ?_, ?_⟩
    all_goals post_simp [h5, h6, h7]

/-- 64611 … 64584, an argument with default options (0xC0 at the cursor c): the argument i (the
    index at T + 24), the pair (v, fn) at args + 16 i, is called through fn with v (ω₇) and the
    `Formatter` at T + 48 (ω₈): W at T + 48, the vtable at T + 56, the options word at T + 64. The
    return address is 2726 (64589); i and c + 1 stay in ω₅, ω₆. -/
theorem wr_arg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T W c i args v fn e : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296)
    (hc : c + 1 < 4294967296) (hW : W < 18446744073709551616) (hi : args + 16 * i + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 192) (h9 : ω[9] = UInt64.ofNat c)
    (h12 : ω[12] = UInt64.ofNat W)
    (ro : rdN μ T 8 = 1610612768) (rvt : rdN μ (T + 8) 8 = 77016) (ra : rdN μ (T + 16) 8 = args)
    (ri : rdN μ (T + 24) 8 = i) (rv : rdN μ (args + 16 * i) 8 = v) (rf : rdN μ (args + 16 * i + 8) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hra : ∀ a, args + 16 * i ≤ a → a < args + 16 * i + 16 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 32 → μ.readable a = true)
    (hw : ∀ a, T + 48 ≤ a → a < T + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64611 ω μ x e ω' μ' x 22 ∧
      ω'[0] = UInt64.ofNat 2726 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat i ∧
      ω'[6] = UInt64.ofNat (c + 1) ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (T + 48) ∧
      rdN μ' (T + 48) 8 = W ∧ rdN μ' (T + 56) 8 = 77016 ∧ rdN μ' (T + 64) 8 = 1610612768 ∧
      (∀ a, a < 4294967296 → (a < T + 48 ∨ T + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : sx8 192 = 18446744073709551552 := by decide
  have hi64 : i < 268435456 := by omega
  have e16 : args + i * 16 = args + 16 * i := by omega
  have rv' : rdN μ (args + i * 16) 8 = v := by rw [e16]; exact rv
  have rf' : rdN μ (args + i * 16 + 8) 8 = fn := by rw [e16]; exact rf
  have hra' : ∀ a, args + i * 16 ≤ a → a < args + i * 16 + 16 → μ.readable a = true := by rw [e16]; exact hra
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  have hv64 : v < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h9, h12, hT, hc, hW, hi, hi64, ro, rvt, ra, ri, rv', rf', hfn, hfn', hjt, hbt, hra', hr, hw, hsx,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv64, rdN_lit8,
      Num.decodeLE_encodeLE, h1, h9, h12]

/-- 64589 … 64599, after an argument's `Ok`: the index (T + 24) goes to i + 1 and the loop goes on
    at 64600. -/
theorem wr_arg_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (T i : Nat) (hT : 65536 ≤ T ∧ T + 96 < 4294967296) (hi : i < 268435456)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat i) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, T + 24 ≤ a → a < T + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64589 ω μ x 64600 ω' μ' x 4 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧ rdN μ' (T + 24) 8 = i + 1 ∧
      (∀ a, a < 4294967296 → (a < T + 24 ∨ T + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hT, hi, hw]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]

end Services.Bootstrap.Fmt
