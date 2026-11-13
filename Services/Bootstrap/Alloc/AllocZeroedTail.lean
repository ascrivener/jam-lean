import Services.Bootstrap.Alloc.AllocTail
import Services.Bootstrap.Memzero

/-!
# The binary's `alloc_impl` with the zero flag: the tail

`alloc_impl` (41177) stores its argument ω₁₀, the zero flag, at its frame + 112. The tail
(42054 … 42128) computes w = ω₁₀ ∧ flag (ω₁₀ there: whether the block may hold old data); w = 0
returns at 41404 … 41423 as in `AllocTail.lean`, and w ≠ 0 pops the frame and tail-calls `memzero`
(70133) on the block's 32·req data octets, which returns to the caller itself. Both end at the
caller's return target t, with ω₇ the data address, ω₁ the caller's stack pointer, and ω₀, ω₅, ω₆
restored from the frame. The flag-0 lemmas (`an_tail_in`, `an_tail_end`, `an_ret`) are unchanged.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41404 … 41423 and the return**: ω₇ = ω₁₁, the frame popped, and the jump to the caller's
    return target t (ω₀ = ret from the frame, an entry of **j**). -/
theorem an_retZ {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ret t : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h144 : rdN μ (sp + 144) 8 = ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41404 ω μ x t ω' μ x 7 ∧ ω'[7] = ω[11] ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hr, h144, hret, hjt, hbt, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val; rfl, by reg_val, by reg_val, by reg_val, by reg_val⟩

/-- **42054 … 41404**, the flag z with ω₁₀ ∧ z = 0 (no zeroing), the final chunk F = N + 32·rhs below the heap's end: F's `prev` becomes pv;
    ω₁₁ the data address. -/
theorem an_tail_inZ0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs pv base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (z : Nat) (hz : z < 18446744073709551616) (h112 : rdN μ (sp + 112) 8 = z)
    (hw : Exec.bitwise (· && ·) ω[10].toNat z = 0) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : N + 32 * rhs < base + 1073741824)
    (hpv : pv < 4294967296) (hD : D < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hNT : 196608 ≤ N + 32 * rhs ∧ N + 32 * rhs + 4 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42054 ω μ x 41404 ω' μ' x 16 ∧ rdN μ' (N + 32 * rhs) 4 = pv ∧
      ω'[11] = UInt64.ofNat D ∧
      (∀ a, a < 4294967296 → (a < N + 32 * rhs ∨ N + 32 * rhs + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : ¬ base + 1073741824 ≤ rhs * 32 + N := by omega
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h3, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3, Nat.mod_eq_of_lt hz, hw,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show N + 32 * rhs = rhs * 32 + N by omega]; rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- **42054 … 41404**, the flag z with ω₁₀ ∧ z = 0 (no zeroing), the final chunk at the heap's end: nothing written. -/
theorem an_tail_endZ0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (z : Nat) (hz : z < 18446744073709551616) (h112 : rdN μ (sp + 112) 8 = z)
    (hw : Exec.bitwise (· && ·) ω[10].toNat z = 0) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : base + 1073741824 ≤ N + 32 * rhs)
    (hF1 : N + 32 * rhs < 2147483648) (hD : D < 4294967296)
    (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 42054 ω μ x 41404 ω' μ x 16 ∧ ω'[11] = UInt64.ofNat D ∧
      ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : base + 1073741824 ≤ rhs * 32 + N := by omega
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3,
    hw, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **42054 … 42128**, the flag z with w = ω₁₀ ∧ z ≠ 0, the final chunk F = N + 32·rhs below the heap's end:
    F's `prev` becomes pv; the frame popped and the jump to `memzero` (70133) with ω₇ = D, ω₈ = 0,
    ω₉ the low word of ω₄ and ω₀ the caller's return address. -/
theorem an_tail_inZ1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs pv base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h3 : ω[3] = UInt64.ofNat pv) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (z : Nat) (hz : z < 18446744073709551616) (h112 : rdN μ (sp + 112) 8 = z)
    (hw : Exec.bitwise (· && ·) ω[10].toNat z ≠ 0)
    (hwl : Exec.bitwise (· && ·) ω[10].toNat z < 18446744073709551616) (n4 : Nat) (h4 : ω[4] = UInt64.ofNat n4) (hn4 : n4 < 4294967296) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : N + 32 * rhs < base + 1073741824)
    (hpv : pv < 4294967296) (hD : D < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hNT : 196608 ≤ N + 32 * rhs ∧ N + 32 * rhs + 4 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42054 ω μ x 70133 ω' μ' x 30 ∧ rdN μ' (N + 32 * rhs) 4 = pv ∧
      ω'[7] = UInt64.ofNat D ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat n4 ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      (∀ a, a < 4294967296 → (a < N + 32 * rhs ∨ N + 32 * rhs + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : ¬ base + 1073741824 ≤ rhs * 32 + N := by omega
  have e4 : n4 % 18446744073709551616 * 4294967296 % 18446744073709551616 / 4294967296 = n4 := by omega
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h3, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3, Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hwl, hw, h4, e4,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, fun a ha h1 => ?_, fun a => ?_⟩
    · rw [show N + 32 * rhs = rhs * 32 + N by omega]; rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]


/-- **42054 … 42128**, the flag z with w = ω₁₀ ∧ z ≠ 0, the final chunk at the heap's end: nothing written;
    the frame popped and the jump to `memzero` (70133) as in `an_tail_inZ1`. -/
theorem an_tail_endZ1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp N rhs base D : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h8 : ω[8] = UInt64.ofNat N) (h2 : ω[2] = UInt64.ofNat D)
    (h120 : rdN μ (sp + 120) 8 = 204984) (z : Nat) (hz : z < 18446744073709551616) (h112 : rdN μ (sp + 112) 8 = z)
    (hw : Exec.bitwise (· && ·) ω[10].toNat z ≠ 0)
    (hwl : Exec.bitwise (· && ·) ω[10].toNat z < 18446744073709551616) (n4 : Nat) (h4 : ω[4] = UInt64.ofNat n4) (hn4 : n4 < 4294967296) (hb : rdN μ 206520 4 = base)
    (hbT : base + 1073741824 < 2147483648) (hF : base + 1073741824 ≤ N + 32 * rhs)
    (hF1 : N + 32 * rhs < 2147483648) (hD : D < 4294967296)
    (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 42054 ω μ x 70133 ω' μ x 30 ∧
      ω'[7] = UInt64.ofNat D ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat n4 ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) := by
  rw [show ω = regsNF ω [] from rfl]
  have e1 : (rhs * 32 + N) % 18446744073709551616 = rhs * 32 + N := Nat.mod_eq_of_lt (by omega)
  have e2 : (base + 1073741824) % 18446744073709551616 = base + 1073741824 := Nat.mod_eq_of_lt (by omega)
  have e3 : base + 1073741824 ≤ rhs * 32 + N := by omega
  have e4 : n4 % 18446744073709551616 * 4294967296 % 18446744073709551616 / 4294967296 = n4 := by omega
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h12, h8, h2, h120, h112, hb, sxw4_small (show base < 2147483648 by omega), e1, e2, e3,
    Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hwl, hw, h4, e4, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val⟩


end Services.Bootstrap.Alloc
