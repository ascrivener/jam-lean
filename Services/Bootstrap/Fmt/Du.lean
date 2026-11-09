import Services.Bootstrap.Fmt.Dec4

/-!
# `<u64 as fmt::Display>::fmt` (68449): the four-digit step

The same shape as `<u32 as Display>` (`Dec*.lean`). It divides by 10000 with the u64
multiply-shift `du_q`, writing digits from T + 55 down, four at a time.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

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

end Services.Bootstrap.Fmt
