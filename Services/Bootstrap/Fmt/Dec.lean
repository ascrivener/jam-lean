import Services.Bootstrap.Fmt.Spec

/-!
# `<u32 as fmt::Display>::fmt` (68146), frame-only

The function renders the value's decimal digits into its 72-octet frame at T = sp − 72
(T + 38 … T + 48). It works four digits at a time while the value is at least 1000, dividing by
10000 by a multiply-shift (`dl_q`), with two digits from the table at 70844 for each half (`dl_r`,
`dl_m`). Then it does two digits, then one, and calls `pad_integral` (61857). With plain options,
`pad_integral` is the sink's `write_str` (`pad_plain`). Which digits are written is not stated.

The value is loaded sign-extended. The arithmetic lemmas hold for any 64-bit word: the low 32 bits
are what counts.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `a & b ≤ b`. -/
theorem bitwise_and_le (a b : Nat) : Exec.bitwise (· && ·) a b ≤ b := by
  have e : Exec.bitwise (· && ·) a b = (a &&& b) % 2 ^ 64 := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_mod_two_pow, Nat.testBit_and]
    all_goals skip
  rw [e]
  exact Nat.le_trans (Nat.mod_le _ _) Nat.and_le_right

/-- The quotient by 10000, as a multiply-shift of the low 32 bits. -/
theorem dl_q (w : Nat) :
    w * 4294967296 % 18446744073709551616 * 15111572745684516864 / 18446744073709551616 / 35184372088832 =
      w % 4294967296 / 10000 := by
  omega

/-- The remainder by 10000, over 4. -/
theorem dl_r (w : Nat) :
    (w - w % 4294967296 / 10000 * 10000) * 281474976710656 % 18446744073709551616 / 1125899906842624 =
      w % 4294967296 % 10000 / 4 := by
  omega

theorem dl_100 (r : Nat) (hr : r < 10000) : r / 4 * 5243 / 131072 = r / 100 := by omega

/-- Twice the remainder by 100, the table offset of the low digit pair. -/
theorem dl_m (y : Nat) :
    (y - (y % 4294967296 / 10000 * 10000 + y % 4294967296 % 10000 / 4 * 5243 / 131072 * 100)) *
      562949953421312 % 18446744073709551616 / 281474976710656 = 2 * (y % 4294967296 % 100) := by
  rw [dl_100 _ (Nat.mod_lt _ (by decide))]
  omega

/-- `dl_q`, `dl_r` and `dl_m` for a value below 2³², in the forms the stepping leaves. -/
theorem dl_q' (y : Nat) (h : y < 4294967296) :
    y * 4294967296 * 15111572745684516864 / 18446744073709551616 / 35184372088832 = y / 10000 := by
  omega

theorem dl_r' (y : Nat) (h : y < 4294967296) :
    (y - y / 10000 * 10000) * 281474976710656 / 1125899906842624 = y % 10000 / 4 := by
  omega

theorem dl_m' (y : Nat) (h : y < 4294967296) :
    (y - (y / 10000 * 10000 + y % 10000 / 4 * 5243 / 131072 * 100)) * 562949953421312 %
      18446744073709551616 / 281474976710656 = 2 * (y % 100) := by
  rw [dl_100 _ (Nat.mod_lt _ (by decide))]
  omega

/-- 68209 … 68314: four digits. From the value y (ω₈, its low 32 bits counting) at least 1000, the
    offset o (ω₉) of the digit block B = T + 44 + o: four digit octets at B … B + 4, y / 10000 (of
    the low 32 bits) in ω₈, o − 4 in ω₉. The loop goes on while y > 9999999. -/
theorem dl_iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T y o B : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296) (hy : y < 18446744073709551616)
    (hy1 : 1000 ≤ y % 4294967296) (ho : o < 18446744073709551616)
    (hB : (T + 44 + o) % 18446744073709551616 = B) (hB1 : T ≤ B ∧ B + 4 ≤ T + 48)
    (h1 : ω[1] = UInt64.ofNat T) (h2 : ω[2] = UInt64.ofNat 15111572745684516864)
    (h3 : ω[3] = UInt64.ofNat 9999999) (h7 : ω[7] = UInt64.ofNat 70844)
    (h8 : ω[8] = UInt64.ofNat y) (h9 : ω[9] = UInt64.ofNat o)
    (r24 : rdN μ (T + 24) 8 = 10000) (r16 : rdN μ (T + 16) 8 = 5243)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 72 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68209 ω μ x (if 9999999 < y then 68209 else 68317) ω' μ' x 40 ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[7] = ω[7] ∧
      ω'[8] = UInt64.ofNat (y % 4294967296 / 10000) ∧
      ω'[9] = UInt64.ofNat ((o + 18446744073709551612) % 18446744073709551616) ∧
      (∀ a, a < 4294967296 → (a < B ∨ B + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hz := bitwise_and_le (y % 4294967296 % 10000 / 4 * 5243 / 65536) 2046
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : 9999999 < y
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_68209 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h1, h2, h3, h7, h8, h9, hT, hy, hy1, dl_q, dl_r, dl_m, ho, hB, hB1, hc, r24, r16, hro, hr, hw,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h1, h2, h3, h7]
  · rw [if_neg hc]
    have hyl : y < 4294967296 := by omega
    have q1 := dl_q' y hyl
    have q2 := dl_r' y hyl
    have q3 := dl_m' y hyl
    have hz' := bitwise_and_le (y % 10000 / 4 * 5243 / 65536) 2046
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_68209 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h1, h2, h3, h7, h8, h9, hT, hy, hy1, q1, q2, q3, ho, hB, hB1, hc, r24, r16, hro, hr, hw,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h1, h2, h3, h7]
      all_goals rw [Nat.mod_eq_of_lt hyl]

end Services.Bootstrap.Fmt
