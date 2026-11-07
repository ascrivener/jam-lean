import Services.Bootstrap.Alloc.AllocUnreg

/-!
# The binary's `alloc_impl`: the allocated chunk and the rest

41726 … 42054: no free space on the left (alignment one unit), the allocated chunk's header, and
the free space on the right registered.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41726 … 41870**, nothing on the left: ω₂ the allocated chunk `base + 32·c`, ω₀ its `prev`. -/
theorem aw_left0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp base c pv : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat (32 * c))
    (h0 : ω[0] = UInt64.ofNat 0) (hb : rdN μ (sp + 96) 8 = base) (hp : rdN μ (sp + 48) 8 = pv)
    (hbc : base + 32 * c < 18446744073709551616) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41726 ω μ x 41870 ω' μ x 5 ∧ ω'[2] = UInt64.ofNat (base + 32 * c) ∧
      ω'[0] = UInt64.ofNat pv ∧ ∀ j : Fin 13, j.val ∉ [0, 2] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h8, h0, hb, hp, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_frame⟩

/-- **41870 … 41910**: the allocated chunk M's header (`prev`, `req + 1` units, used); ω₂ the data,
    ω₈ the next chunk, ω₁₂ the space on the right. -/
theorem aw_hdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp M pv req A d rhs : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat M)
    (h0 : ω[0] = UInt64.ofNat pv) (h4 : ω[4] = UInt64.ofNat (req + 1)) (h9 : ω[9] = UInt64.ofNat req)
    (hA : rdN μ (sp + 80) 8 = A) (hd : rdN μ (sp + 72) 8 = d) (hrh : rdN μ (sp + 104) 8 = rhs)
    (hM : M + 32 * (req + 1) < 2147483648) (hpv : pv < 4294967296) (hrq : 2 * (req + 1) + 1 < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hMT : 196608 ≤ M ∧ M + 8 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41870 ω μ x 41910 ω' μ' x 14 ∧
      rdN μ' M 4 = pv ∧ rdN μ' (M + 4) 4 = sizeWord (req + 1) true ∧
      ω'[2] = UInt64.ofNat (M + 32) ∧ ω'[8] = UInt64.ofNat (M + 32 * (req + 1)) ∧ ω'[12] = UInt64.ofNat rhs ∧
      ω'[3] = UInt64.ofNat (req + 1) ∧
      (∀ a, a < 4294967296 → (a < M ∨ M + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [2, 3, 4, 6, 8, 10, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h2, h0, h4, h9, hA, hd, hrh, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; unfold sizeWord; simp only [Nat.reducePow, Nat.reduceMul, ↓reduceIte]; omega
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]; congr 1; omega
    · reg_val
    · reg_val
    · rd_simp []
    · rd_simp [hwr]

end Services.Bootstrap.Alloc
