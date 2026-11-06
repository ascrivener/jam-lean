import Services.Bootstrap.Alloc.Register

/-!
# `free`'s merge with the next chunk in the binary

42597 … 42814: the chunk after the freed one (at nc = M + 32·size), if below the heap's end and
free, leaves its bin's list and is merged in.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- Close a register-frame goal `∀ j ∉ l, ω'[j] = ω[j]` after `pvm_go`. -/
macro "reg_frame" : tactic => `(tactic| (
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp only [Fin.getElem_fin]
  rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
  simp_all [PVM.lookup_cons_nat]))

/-- Close a register-value goal `ω'[j] = UInt64.ofNat v` after `pvm_go`. -/
macro "reg_val" : tactic => `(tactic| (
  simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
    Option.getD_some]
  try (congr 1; omega)))

/-- 42597 … 42609: ω₁₂ = the heap's end, ω₉ = the next chunk's address. -/
theorem nx_addr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (base M size : Nat) (h5 : ω[5] = UInt64.ofNat base) (h2 : ω[2] = UInt64.ofNat size)
    (h8 : ω[8] = UInt64.ofNat M) (hb : base + 1073741824 < 2147483648) (hM : M + 32 * size < 2147483648) :
    ∃ ω', FreeStepsH p R 42597 ω μ x 42609 ω' μ x 3 ∧ ω'[12] = UInt64.ofNat (base + 1073741824) ∧
      ω'[9] = UInt64.ofNat (M + 32 * size) ∧ ∀ j : Fin 13, j.val ∉ [9, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h2, h8]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_frame⟩

/-- 42609: past the heap's end, to 42814. -/
theorem nx_br_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat b) (hab : b ≤ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42609 ω μ x 42814 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12, hab]

/-- 42609: below the heap's end, to 42613. -/
theorem nx_br_in {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat b) (hab : a < b)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42609 ω μ x 42613 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12, hab]

/-- 42613 … 42626: ω₅ = the next chunk's size word w, ω₁₀ = its used bit, ω₁₁ = its address. -/
theorem nx_hdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc w : Nat) (h9 : ω[9] = UInt64.ofNat nc) (hnc : nc < 2147483648)
    (hw : rdN μ (nc + 4) 4 = w) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42613 ω μ x 42626 ω' μ x 5 ∧ ω'[5] = UInt64.ofNat w ∧
      ω'[10] = UInt64.ofNat (w % 2) ∧ ω'[11] = UInt64.ofNat nc ∧
      ∀ j : Fin 13, j.val ∉ [5, 10, 11] → ω'[j] = ω[j] := by
  have hw32 : w < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      Option.getD_some, PVM.bitwise_and_m1]

/-- 42626, the next chunk allocated: to 42814. -/
theorem nx_br_used {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (c : Nat) (h10 : ω[10] = UInt64.ofNat c) (hc : c ≠ 0) (hc2 : c < 2) :
    FreeStepsH p R 42626 ω μ x 42814 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h10, hc]

/-- 42626, the next chunk free: to 42630. -/
theorem nx_br_free {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h10 : ω[10] = UInt64.ofNat 0) :
    FreeStepsH p R 42626 ω μ x 42630 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h10]

/-- 42630 … 42672, a free chunk of 1 … 127 units (size word w = 2·sz): ω₅ = its bin sz − 1,
    ω₆ = the bin's head slot, ω₁₀ = the bin's head `hd`, ω₀ = sz. -/
theorem nx_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sz hd : Nat) (h5 : ω[5] = UInt64.ofNat (2 * sz)) (h7 : ω[7] = UInt64.ofNat 196792)
    (hs1 : 1 ≤ sz) (hs2 : sz < 128) (hhd : rdN μ (196792 + (sz - 1) * 4) 4 = hd) (hhd1 : hd < 2147483648)
    (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42630 ω μ x 42672 ω' μ x 13 ∧ ω'[0] = UInt64.ofNat sz ∧
      ω'[5] = UInt64.ofNat (sz - 1) ∧ ω'[6] = UInt64.ofNat (196792 + (sz - 1) * 4) ∧
      ω'[10] = UInt64.ofNat hd ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 6, 10] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hsh : 2 * sz / 2 = sz := by omega
  have hb : (sz - 1) % 4294967296 = sz - 1 := by omega
  have hq : (sz - 1) * 4294967296 / 1073741824 = (sz - 1) * 4 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h7, hhd, hr, hsx, hsh, hb, hq, ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

end Services.Bootstrap.Alloc
