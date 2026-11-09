import Services.Bootstrap.Fmt.Dec4

/-!
# `<u64 as fmt::Display>::fmt` (68449): the four-digit step

The same shape as `<u32 as Display>` (`Dec*.lean`). It divides by 10000 with the u64
multiply-shift `du_q`, writing digits from T + 55 down, four at a time.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The quotient by 10000, as the u64 multiply-shift. -/
theorem du_q (y : Nat) (hy : y < 18446744073709551616) :
    y * 3777893186295716171 / 18446744073709551616 / 2048 = y / 10000 := by
  omega

/-- 68521 … 68595: four digits of y (ω₅): the pairs for y mod 10000 at Q − 3 … Q + 1 (Q = ω₁₂); y / 10000
    in ω₅, the count ω₁₁ up by 4, Q − 4 in ω₁₂. The loop goes on while y > 9999999. -/
theorem du_iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T y a Q : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296) (hy : y < 18446744073709551616) (hy1 : 1000 ≤ y)
    (ha : a < 18446744073709551616) (hQ : T + 3 ≤ Q ∧ Q + 1 ≤ T + 80)
    (h0 : ω[0] = UInt64.ofNat 5243) (h1 : ω[1] = UInt64.ofNat T) (h3 : ω[3] = UInt64.ofNat 70844)
    (h4 : ω[4] = UInt64.ofNat 9999999) (h5 : ω[5] = UInt64.ofNat y) (h6 : ω[6] = UInt64.ofNat 100)
    (h11 : ω[11] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat Q)
    (r16 : rdN μ (T + 16) 8 = 3777893186295716171) (r24 : rdN μ (T + 24) 8 = 10000)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 80 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68521 ω μ x (if 9999999 < y then 68521 else 68598) ω' μ' x 40 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[6] = ω[6] ∧
      ω'[5] = UInt64.ofNat (y / 10000) ∧ ω'[11] = UInt64.ofNat ((a + 4) % 18446744073709551616) ∧
      ω'[12] = UInt64.ofNat (Q - 4) ∧
      (∀ a, a < 4294967296 → (a + 3 < Q ∨ Q + 1 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have q1 := du_q y hy
  have q2 : (y - y / 10000 * 10000) * 281474976710656 % 18446744073709551616 / 1125899906842624 =
      y % 10000 / 4 := by omega
  have q3 : (y - y / 10000 * 10000) * 281474976710656 / 1125899906842624 = y % 10000 / 4 := by omega
  have q4 := dl_100 (y % 10000) (Nat.mod_lt _ (by decide))
  have hz := bitwise_and_le (y % 10000 / 4 * 5243 / 65536) 2046
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : 9999999 < y
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_68521 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h0, h1, h3, h4, h5, h6, h11, h12, hT, hy, hy1, ha, hQ, hc, q1, q2, q3, q4, r16, r24, hro, hr, hw,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h0, h1, h3, h4, h6]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_68521 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h0, h1, h3, h4, h5, h6, h11, h12, hT, hy, hy1, ha, hQ, hc, q1, q2, q3, q4, r16, r24, hro, hr, hw,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h0, h1, h3, h4, h6]

/-- **The four-digit loop** (68521 …), for y ≥ 1000 below 1000 · 10000^j: c ≤ j passes; the
    remaining value y / 10000^c (below 1000) in ω₅, the count ω₁₁ up by 4c, ω₁₂ down by 4c, the digits
    at Q + 1 − 4c … Q + 1; then 68598. -/
theorem du_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (T : Nat)
    (hT : 65536 ≤ T ∧ T + 80 < 4294967296) :
    ∀ (j y a Q : Nat) (ω : Regs) (μ : Memory), y < 18446744073709551616 → 1000 ≤ y →
      y < 1000 * 10000 ^ j → a < 18446744073709551616 → T + 32 + 4 * j ≤ Q + 1 → Q + 1 ≤ T + 80 →
      ω[0] = UInt64.ofNat 5243 → ω[1] = UInt64.ofNat T → ω[3] = UInt64.ofNat 70844 →
      ω[4] = UInt64.ofNat 9999999 → ω[5] = UInt64.ofNat y → ω[6] = UInt64.ofNat 100 →
      ω[11] = UInt64.ofNat a → ω[12] = UInt64.ofNat Q →
      rdN μ (T + 16) 8 = 3777893186295716171 → rdN μ (T + 24) 8 = 10000 →
      (∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true) →
      (∀ a, T ≤ a → a < T + 80 → μ.writable a = true) →
      ∃ ω' μ' c, 1 ≤ c ∧ c ≤ j ∧ FreeStepsH p R 68521 ω μ x 68598 ω' μ' x (40 * c) ∧
        ω'[1] = ω[1] ∧ ω'[3] = ω[3] ∧ ω'[5] = UInt64.ofNat (y / 10000 ^ c) ∧ y / 10000 ^ c < 1000 ∧
        ω'[11] = UInt64.ofNat ((a + 4 * c) % 18446744073709551616) ∧ ω'[12] = UInt64.ofNat (Q - 4 * c) ∧
        (∀ a, a < 4294967296 → (a + 4 * c < Q + 1 ∨ Q + 1 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro j
  induction j with
  | zero => intro y a Q ω μ _ h1 h2; simp at h2; omega
  | succ j ih =>
    intro y a Q ω μ hy hy1 hyj ha hQ1 hQ2 h0 h1 h3 h4 h5 h6 h11 h12 r16 r24 hro hw
    obtain ⟨ω1, μ1, run1, a0, a1, a3, a4, a6, a5, a11, a12, fr1, rd1, wr1⟩ := du_iter (p := p) (P := P) (R := R)
      x ω μ T y a Q hT hy hy1 ha ⟨by omega, hQ2⟩ h0 h1 h3 h4 h5 h6 h11 h12 r16 r24 hro
      (fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)) hw
    by_cases hc : 9999999 < y
    · rw [if_pos hc] at run1
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hyj; omega
        · exact h
      have hyj' : y / 10000 < 1000 * 10000 ^ j := by
        rw [Nat.pow_succ, ← Nat.mul_assoc] at hyj
        exact (Nat.div_lt_iff_lt_mul (by decide)).2 hyj
      have k16 : rdN μ1 (T + 16) 8 = 3777893186295716171 := by
        rw [rdN_frame (fun j hj => fr1 _ (by omega) (by omega))]; exact r16
      have k24 : rdN μ1 (T + 24) 8 = 10000 := by
        rw [rdN_frame (fun j hj => fr1 _ (by omega) (by omega))]; exact r24
      obtain ⟨ω2, μ2, c, hc1, hc2, run2, b1, b3, b5, bq, b11, b12, fr2, rd2, wr2⟩ :=
        ih (y / 10000) ((a + 4) % 18446744073709551616) (Q - 4) ω1 μ1 (by omega) (by omega) hyj'
          (by omega) (by omega) (by omega) (a0.trans h0) (a1.trans h1) (a3.trans h3) (a4.trans h4) a5
          (a6.trans h6) a11 a12 k16 k24 (fun a h1 h2 => by rw [rd1]; exact hro a h1 h2)
          (fun a h1 h2 => by rw [wr1]; exact hw a h1 h2)
      refine ⟨ω2, μ2, c + 1, by omega, by omega, (run1.trans run2).mono (by omega), b1.trans a1, b3.trans a3,
        ?_, ?_, ?_, by rw [b12]; congr 1; omega,
        fun a h1 h2 => by rw [fr2 a h1 (by omega), fr1 a h1 (by omega)], fun a => by rw [rd2, rd1],
        fun a => by rw [wr2, wr1]⟩
      · rw [b5, Nat.pow_succ, Nat.mul_comm (10000 ^ c), ← Nat.div_div_eq_div_mul]
      · rw [Nat.pow_succ, Nat.mul_comm (10000 ^ c), ← Nat.div_div_eq_div_mul]; exact bq
      · rw [b11]; congr 1; omega
    · rw [if_neg hc] at run1
      refine ⟨ω1, μ1, 1, Nat.le_refl _, by omega, run1.mono (by omega), a1, a3, by simp [a5],
        by simp; omega, by rw [a11], by rw [a12],
        fun a h1 h2 => fr1 a h1 (by omega), rd1, wr1⟩

end Services.Bootstrap.Fmt
