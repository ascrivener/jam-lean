import Services.Bootstrap.Alloc.AllocRight

/-!
# The binary's `alloc_impl`: the next chunk's `prev` and the return

42054 … 41423, not zeroing (the saved ω₁₀ = 0): the chunk after the last one written records its
size, if it lies below the heap's end; then the data address is returned in ω₇.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem bitwise_and_zero (a : Nat) : Exec.bitwise (· && ·) a 0 = 0 := by
  rw [bitwise_and_land _ _ (by decide), Nat.and_zero]

/-- **42054 … 41404**, the final chunk F = N + 32·rhs below the heap's end: F's `prev` becomes pv;
    ω₁₁ the data address. -/
theorem an_tail_in {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs pv base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : N + 32 * rhs < base + 1073741824)
    (hpv : pv < 4294967296) (hD : D < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42054 ω μ x 41404 ω' μ' x 16 ∧ rdN μ' (N + 32 * rhs) 4 = pv ∧
      ω'[11] = UInt64.ofNat D ∧
      (∀ a, a < 4294967296 → (a < N + 32 * rhs ∨ N + 32 * rhs + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : ¬ base + 1073741824 ≤ rhs * 32 + N := by omega
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h3, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3, bitwise_and_zero ω[10].toNat,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show N + 32 * rhs = rhs * 32 + N by omega]; rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- **42054 … 41404**, the final chunk at the heap's end: nothing written. -/
theorem an_tail_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = 0) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : base + 1073741824 ≤ N + 32 * rhs)
    (hF1 : N + 32 * rhs < 2147483648) (hD : D < 4294967296)
    (hsp : sp + 152 < 4294967296) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42054 ω μ x 41404 ω' μ x 16 ∧ ω'[11] = UInt64.ofNat D ∧
      ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : base + 1073741824 ≤ rhs * 32 + N := by omega
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3,
    bitwise_and_zero ω[10].toNat, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41404 … 41423**: ω₇ = ω₁₁ returned, the frame popped; at the return. -/
theorem an_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 152 < 4294967296) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 41404 ω μ x 41423 ω' μ x 6 ∧ ω'[7] = ω[11] ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val; rfl, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

end Services.Bootstrap.Alloc
