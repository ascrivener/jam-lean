import Services.Bootstrap.Fmt.Tac

/-!
# `alloc::fmt::format_inner` (59375): its steps

`format_inner(out, template, args)` (ω₇ = O, the `String` it returns; ω₈ the template; ω₉ the
arguments, at an even address) estimates the capacity, allocates the `String`'s buffer, runs
`core::fmt::write` (64495) into it, and moves the `String` to O.

The frame is 72 octets at U = sp − 72: the arguments at U, the template at U + 8, O at U + 16, the
`String` at U + 24 … U + 48, and the saved ω₆, ω₅, ω₀ at U + 48, U + 56, U + 64.

The capacity estimate sums the literals' lengths L over the template; it is 0 when the template
starts with an argument and L < 16, and 2L otherwise.

These are the steps:
- `fi_entry`: 59375 … 59441, a template with a first item;
- `fi_entry0`: 59375 … 64495, an empty template (`String::new()`, then `core::fmt::write`);
- `fi_head`: 59436 … 59441, the next item;
- `fi_lit`: 59441 … 59436, a literal;
- `fi_arg`: 59441 … 59436, an argument;
- `fi_est`: 59436 … 59536, the end: the estimate;
- `fi_zero`: 59536 … 64495, an estimate of 0;
- `fi_alloc`: 59536 … 40494, a nonzero estimate: the buffer's `alloc`;
- `fi_alloced`: 59557 … 64495, after `alloc`;
- `fi_ret`: 59665 … the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 59375 … 59427, a template whose first byte b is not 0: the frame at U = S − 72 (ω₀, ω₅, ω₆ at
    U + 64, U + 56, U + 48; O at U + 16), the template and the arguments kept in ω₂, ω₃, ω₄ = 0,
    and the estimate's loop entered at 59441 with b in ω₁₀, the cursor tp in ω₁₁, the sum 0 (ω₆),
    the flag 0 (ω₇), 128 in ω₈ and 2⁶² in ω₉. -/
theorem fi_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (S O tp args b r0 v5 v6 : Nat) (hS : 65536 + 72 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat tp)
    (h9 : ω[9] = UInt64.ofNat args)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      O < 18446744073709551616 ∧ tp < 4294967296 ∧ args < 18446744073709551616 ∧ args % 2 = 0)
    (hb : rdN μ tp 1 = b) (hb0 : b ≠ 0) (hrt : μ.readable tp = true) (htS : tp + 1 ≤ S - 72)
    (hw : ∀ a, S - 72 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59375 ω μ x 59441 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat (S - 72) ∧ ω'[2] = UInt64.ofNat tp ∧ ω'[3] = UInt64.ofNat args ∧
      ω'[4] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat 0 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[8] = UInt64.ofNat 128 ∧ ω'[9] = UInt64.ofNat 4611686018427387904 ∧ ω'[10] = UInt64.ofNat b ∧
      ω'[11] = UInt64.ofNat tp ∧
      rdN μ' (S - 72 + 16) 8 = O ∧ rdN μ' (S - 72 + 48) 8 = v6 ∧ rdN μ' (S - 72 + 56) 8 = v5 ∧
      rdN μ' (S - 72 + 64) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 72 ≤ a → a < S → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hbl : b < 256 := by rw [← hb]; exact rdN_lt μ tp 1
  have ha1 : args % 2 = 0 := hv.2.2.2.2.2.2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hv, hb, hb0, hbl, hrt, htS, hw, hr, ha1, bitwise_and_m1,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      h8, h9, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1]

/-- 59375 … 59403, 59636 … 64495, an empty template (first byte 0): the frame, `String::new()`
    (capacity 0, buffer 1, length 0) at U + 24, and `core::fmt::write` called with it (ω₇ = U + 24),
    the `String` vtable (77016), the template and the arguments, returning to 59665 (2588). -/
theorem fi_entry0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (S O tp args r0 v5 v6 : Nat) (hS : 65536 + 72 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat tp)
    (h9 : ω[9] = UInt64.ofNat args)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      O < 18446744073709551616 ∧ tp < 4294967296 ∧ args < 18446744073709551616 ∧ args % 2 = 0)
    (hb : rdN μ tp 1 = 0) (hrt : μ.readable tp = true) (htS : tp + 1 ≤ S - 72)
    (hw : ∀ a, S - 72 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59375 ω μ x 64495 ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat 2588 ∧ ω'[1] = UInt64.ofNat (S - 72) ∧ ω'[7] = UInt64.ofNat (S - 72 + 24) ∧
      ω'[8] = UInt64.ofNat 77016 ∧ ω'[9] = UInt64.ofNat tp ∧ ω'[10] = UInt64.ofNat args ∧
      rdN μ' (S - 72 + 16) 8 = O ∧ rdN μ' (S - 72 + 24) 8 = 0 ∧ rdN μ' (S - 72 + 32) 8 = 1 ∧
      rdN μ' (S - 72 + 40) 8 = 0 ∧
      rdN μ' (S - 72 + 48) 8 = v6 ∧ rdN μ' (S - 72 + 56) 8 = v5 ∧ rdN μ' (S - 72 + 64) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 72 ≤ a → a < S → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha1 : args % 2 = 0 := hv.2.2.2.2.2.2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hv, hb, hrt, htS, hw, hr, ha1, bitwise_and_m1,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      h8, h9, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1]

/-- 59436 … 59438, the next item's byte b ≠ 0, read at the cursor c (ω₁₁), into ω₁₀. -/
theorem fi_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (c b : Nat) (hc : c < 4294967296) (h11 : ω[11] = UInt64.ofNat c)
    (hb : rdN μ c 1 = b) (hb0 : b ≠ 0) (hrc : μ.readable c = true) :
    ∃ ω', FreeStepsH p R 59436 ω μ x 59441 ω' μ x 2 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat b ∧
      ω'[11] = ω[11] := by
  have hbl : b < 256 := by rw [← hb]; exact rdN_lt μ c 1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h11, hc, hb, hb0, hbl, hrc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h11]

/-- 59441 … 59435, a literal (1 ≤ n < 128 in ω₁₀, the cursor c in ω₁₁): the sum L (ω₆) goes to
    L + n and the cursor to c + 1 + n. -/
theorem fi_lit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (c n L : Nat) (hc : c + 1 + n < 4294967296) (hL : L + n < 4294967296)
    (hn : 1 ≤ n ∧ n < 128) (h6 : ω[6] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat n)
    (h11 : ω[11] = UInt64.ofNat c) :
    ∃ ω', FreeStepsH p R 59441 ω μ x 59436 ω' μ x 8 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧
      ω'[6] = UInt64.ofNat (L + n) ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      ω'[11] = UInt64.ofNat (c + 1 + n) := by
  have hsx : sx8 n = n := sx8_of_lt n hn.2
  have h255 : Exec.bitwise (· && ·) n 255 = n := by
    rw [bitwise_and_low n 255 8 rfl (by decide)]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h6, h10, h11, hc, hL, hn, hsx, h255]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [hsx, h255, h6, h10, h11]

/-- 59441 … 59516, an argument (0xC0 in ω₁₀, the cursor c in ω₁₁, with 128 in ω₈, 2⁶² in ω₉ and the
    flag f ≤ 1 in ω₇): the cursor goes to c + 1, the sum L (ω₆) is kept, and the flag is set when
    L = 0. -/
theorem fi_arg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (c L f : Nat) (hc : c + 1 < 4294967296) (hL : L < 4294967296) (hf : f ≤ 1)
    (h6 : ω[6] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat f) (h8 : ω[8] = UInt64.ofNat 128)
    (h9 : ω[9] = UInt64.ofNat 4611686018427387904) (h10 : ω[10] = UInt64.ofNat 192)
    (h11 : ω[11] = UInt64.ofNat c) :
    ∃ ω' f', f' ≤ 1 ∧ FreeStepsH p R 59441 ω μ x 59436 ω' μ x 24 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧
      ω'[6] = UInt64.ofNat L ∧ ω'[7] = UInt64.ofNat f' ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      ω'[11] = UInt64.ofNat (c + 1) := by
  have hsx : sx8 192 = 18446744073709551552 := by decide
  have hif : (if L < 1 then 1 else 0) % 18446744073709551616 = (if L < 1 then 1 else 0) := by split <;> rfl
  have hor : Exec.bitwise (· || ·) f (if L < 1 then 1 else 0) ≤ 1 := by
    rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl <;> by_cases hl : L < 1 <;> simp only [hl, ↓reduceIte] <;>
      decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, Exec.bitwise (· || ·) f (if L < 1 then 1 else 0), hor, ?_, ?_⟩
  rotate_left
  · pvm_go [h6, h7, h8, h9, h10, h11, hc, hL, hf, hsx]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [hsx, hif, h6, h7, h8, h9, h10, h11]

/-- 59436 … 59536, the template's end (byte 0 at the cursor c): with the sum L (ω₆) and the flag
    f ≤ 1 (ω₇), the estimate in ω₆ is 0 or 2L. -/
theorem fi_est {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (c L f : Nat) (hc : c < 4294967296) (hL : L < 1073741824) (hfl : f ≤ 1)
    (h6 : ω[6] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat f) (h11 : ω[11] = UInt64.ofNat c)
    (hb : rdN μ c 1 = 0) (hrc : μ.readable c = true) :
    ∃ ω' e, (e = 0 ∨ e = 2 * L) ∧ FreeStepsH p R 59436 ω μ x 59536 ω' μ x 10 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧
      ω'[6] = UInt64.ofNat e := by
  have b11 : Exec.bitwise (· && ·) 1 1 = 1 := by decide
  have b10 : Exec.bitwise (· && ·) 1 0 = 0 := by decide
  have b01 : Exec.bitwise (· && ·) 0 1 = 0 := by decide
  have b00 : Exec.bitwise (· && ·) 0 0 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl <;> clear hfl <;> by_cases hl : L < 16
  · refine ⟨?_, 2 * L, Or.inr rfl, ?_, ?_⟩
    rotate_left
    · pvm_go [h6, h7, h11, hc, hL, hb, hrc, hl, b11, b10, b01, b00, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h6, h7, h11]
  · refine ⟨?_, 2 * L, Or.inr rfl, ?_, ?_⟩
    rotate_left
    · pvm_go [h6, h7, h11, hc, hL, hb, hrc, hl, b11, b10, b01, b00, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h6, h7, h11]
  · refine ⟨?_, 0, Or.inl rfl, ?_, ?_⟩
    rotate_left
    · pvm_go [h6, h7, h11, hc, hL, hb, hrc, hl, b11, b10, b01, b00, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h6, h7, h11]
  · refine ⟨?_, 2 * L, Or.inr rfl, ?_, ?_⟩
    rotate_left
    · pvm_go [h6, h7, h11, hc, hL, hb, hrc, hl, b11, b10, b01, b00, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h6, h7, h11]

/-- 59536 … 64495, an estimate of 0 (with ω₄ = 0): `String::new()` (capacity 0, buffer 1, length 0)
    at U + 24 and the call of `core::fmt::write` as in `fi_entry0`. -/
theorem fi_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (U tp args : Nat) (hU : 65536 ≤ U ∧ U + 72 < 4294967296)
    (htp : tp < 18446744073709551616) (hargs : args < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat U) (h2 : ω[2] = UInt64.ofNat tp) (h3 : ω[3] = UInt64.ofNat args)
    (h4 : ω[4] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat 0)
    (hw : ∀ a, U + 24 ≤ a → a < U + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59536 ω μ x 64495 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 2588 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat (U + 24) ∧
      ω'[8] = UInt64.ofNat 77016 ∧ ω'[9] = ω[2] ∧ ω'[10] = ω[3] ∧
      rdN μ' (U + 24) 8 = 0 ∧ rdN μ' (U + 32) 8 = 1 ∧ rdN μ' (U + 40) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < U + 24 ∨ U + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h2, h3, h4, h6, hU, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, h1, h2, h3, h4, h6,
      Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hargs]

/-- 59536 … 59551, a nonzero estimate e (with ω₄ = 0): the template and the arguments saved at
    U + 8, U, and `alloc` (40494) called with size e, align 1, returning to 59557 (2584). -/
theorem fi_alloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (U tp args e : Nat) (hU : 65536 ≤ U ∧ U + 72 < 4294967296) (he : 0 < e ∧ e < 4294967296)
    (htp : tp < 18446744073709551616) (hargs : args < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat U) (h2 : ω[2] = UInt64.ofNat tp) (h3 : ω[3] = UInt64.ofNat args)
    (h4 : ω[4] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat e)
    (hw : ∀ a, U ≤ a → a < U + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59536 ω μ x 40494 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 2584 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat e ∧
      ω'[7] = UInt64.ofNat e ∧ ω'[8] = UInt64.ofNat 1 ∧
      rdN μ' U 8 = args ∧ rdN μ' (U + 8) 8 = tp ∧
      (∀ a, a < 4294967296 → (a < U ∨ U + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h2, h3, h4, h6, hU, he, htp, hargs, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt htp,
      Nat.mod_eq_of_lt hargs, h1, h2, h3, h4, h6]

/-- 59557 … 64495, after `alloc` returned the buffer ptr ≠ 0 (with ω₅ = 0 and the estimate e in
    ω₆): the `String` (capacity e, buffer ptr, length 0) at U + 24 and the call of
    `core::fmt::write`, as in `fi_entry0`. -/
theorem fi_alloced {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (U tp args e ptr : Nat) (hU : 65536 ≤ U ∧ U + 72 < 4294967296)
    (he : e < 18446744073709551616) (hp : 0 < ptr ∧ ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat U) (h5 : ω[5] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat e)
    (h7 : ω[7] = UInt64.ofNat ptr) (ra : rdN μ U 8 = args) (rt : rdN μ (U + 8) 8 = tp)
    (hr : ∀ a, U ≤ a → a < U + 16 → μ.readable a = true)
    (hw : ∀ a, U + 24 ≤ a → a < U + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59557 ω μ x 64495 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2588 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat (U + 24) ∧
      ω'[8] = UInt64.ofNat 77016 ∧ ω'[9] = UInt64.ofNat tp ∧ ω'[10] = UInt64.ofNat args ∧
      rdN μ' (U + 24) 8 = e ∧ rdN μ' (U + 32) 8 = ptr ∧ rdN μ' (U + 40) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < U + 24 ∨ U + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hta : args < 18446744073709551616 := ra ▸ rdN_lt64 μ U
  have htt : tp < 18446744073709551616 := rt ▸ rdN_lt64 μ (U + 8)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hU, he, hp, ra, rt, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hp.2,
      Nat.mod_eq_of_lt (rdN_lt64 μ U), Nat.mod_eq_of_lt (rdN_lt64 μ (U + 8)), h1, h5, h6, h7, ra, rt, rdN_lit8,
      Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hta, Nat.mod_eq_of_lt htt]

/-- 59665 … the return, after `core::fmt::write` returned `Ok`: the `String`'s three words at U + 24
    copied to O (read at U + 16), ω₀, ω₅, ω₆ restored, the frame closed, and a return to t. -/
theorem fi_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs)
    (μ : Memory) (U O r0 t v5 v6 w0 w1 w2 : Nat) (hU : 65536 ≤ U ∧ U + 72 < 4294967296)
    (hO : O + 24 < 4294967296 ∧ (O + 24 ≤ U ∨ U + 72 ≤ O))
    (h1 : ω[1] = UInt64.ofNat U) (h7 : ω[7] = UInt64.ofNat 0)
    (r24 : rdN μ (U + 24) 8 = w0) (r32 : rdN μ (U + 32) 8 = w1) (r40 : rdN μ (U + 40) 8 = w2)
    (rO : rdN μ (U + 16) 8 = O) (r0' : rdN μ (U + 64) 8 = r0) (r5 : rdN μ (U + 56) 8 = v5)
    (r6 : rdN μ (U + 48) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, U ≤ a → a < U + 72 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59665 ω μ x t ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (U + 72) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      rdN μ' O 8 = w0 ∧ rdN μ' (O + 8) 8 = w1 ∧ rdN μ' (O + 16) 8 = w2 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hw0 := rdN_lt64 μ (U + 24)
  have hw1 := rdN_lt64 μ (U + 32)
  have hw2 := rdN_lt64 μ (U + 40)
  rw [r24] at hw0
  rw [r32] at hw1
  rw [r40] at hw2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hU, hO, r24, r32, r40, rO, r0', r5, r6, hret, hjt, hbt, hr, hw, hw0, hw1, hw2,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1,
      Nat.mod_eq_of_lt hw2, Nat.mod_eq_of_lt (rdN_lt64 μ (U + 64)), Nat.mod_eq_of_lt (rdN_lt64 μ (U + 56)),
      Nat.mod_eq_of_lt (rdN_lt64 μ (U + 48)), Num.decodeLE_encodeLE, h1, h7]

/-- The `alloc` wrapper's return (40611) to `format_inner` (59557, 2584). -/
theorem fi_ret_alloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2584) : FreeStepsH p R 40611 ω μ x 59557 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Fmt
