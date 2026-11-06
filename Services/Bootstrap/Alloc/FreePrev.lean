import Services.Bootstrap.Alloc.FreeNext

/-!
# `free`'s prologue and merge with the previous chunk in the binary

42327 … 42369: the frame and the freed chunk X = ptr − 32 (its size word, `prev`, and offset from
the base); 42369 … 42597: the chunk before X, if X is not the first and that chunk is free, leaves
its bin's list and takes X in.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **42327 … 42369**: the frame below sp, and the freed chunk's fields. -/
theorem free_pro {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr base w pv : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h7 : ω[7] = UInt64.ofNat 196792) (hsp : 2147483672 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = base) (hw : rdN μ (ptr - 32 + 4) 4 = w) (hp : rdN μ (ptr - 32) 4 = pv)
    (hpv : pv < 2147483648) (hptr : 32 + base ≤ ptr) (hptr2 : ptr < 2147483648)
    (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42327 ω μ x 42369 ω' μ' x 14 ∧
      ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[8] = UInt64.ofNat (ptr - 32) ∧ ω'[4] = UInt64.ofNat 204984 ∧
      ω'[5] = UInt64.ofNat base ∧ ω'[10] = UInt64.ofNat w ∧ ω'[3] = UInt64.ofNat pv ∧
      ω'[9] = UInt64.ofNat (ptr - 32 - base) ∧ ω'[11] = UInt64.ofNat 31 ∧ ω'[2] = UInt64.ofNat (w / 2) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [1, 2, 3, 4, 5, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  have hsx : sxw 4 pv = pv := sxw4_small hpv
  have hsub : (ptr - 32 + 4294967296 - base) % 4294967296 = ptr - 32 - base := by omega
  have hw32 : w < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h8, h7, hb, hw, hp, hsx, hsub, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
      by reg_val, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show sp - 8 = sp - 24 + 16 by omega]; rd_simp []; rfl
    · rw [show sp - 16 = sp - 24 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- 42369: X is the first chunk (offset ≤ 31), to 42597. -/
theorem pv_br_first {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h11 : ω[11] = UInt64.ofNat 31) (ha : a ≤ 31) :
    FreeStepsH p R 42369 ω μ x 42597 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h11, ha]

/-- 42369: X has a chunk before it, to 42373. -/
theorem pv_br_has {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h11 : ω[11] = UInt64.ofNat 31) (ha : 31 < a)
    (ha1 : a < 4294967296) :
    FreeStepsH p R 42369 ω μ x 42373 ω μ x 1 := by
  have hna : ¬ 31 ≥ a := by omega
  rw [show ω = regsNF ω [] from rfl]
  apply FreeStepsH.step_decode (d_42369 (p := p) (P := P))
  · pvm_simp [h9, h11, hna]
  exact FreeStepsH.refl

/-- 42373 … 42392: the chunk before X at P = X − 32·pv; ω₀ = its size word pw, ω₁₂ = its used
    bit, ω₉ = ω₁₁ = P. -/
theorem pv_hdr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (Xa pv pw : Nat) (h3 : ω[3] = UInt64.ofNat pv) (h8 : ω[8] = UInt64.ofNat Xa) (hpv : 32 * pv ≤ Xa)
    (hX : Xa < 2147483648) (hw : rdN μ (Xa - 32 * pv + 4) 4 = pw) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42373 ω μ x 42392 ω' μ x 7 ∧ ω'[0] = UInt64.ofNat pw ∧
      ω'[12] = UInt64.ofNat (pw % 2) ∧ ω'[9] = UInt64.ofNat (Xa - 32 * pv) ∧ ω'[11] = UInt64.ofNat (Xa - 32 * pv) ∧
      ∀ j : Fin 13, j.val ∉ [0, 9, 11, 12] → ω'[j] = ω[j] := by
  have hw32 : pw < 4294967296 := by rw [← hw]; exact rdN_lt μ _ 4
  have hsub : (Xa + 4294967296 - pv * 32) % 4294967296 = Xa - 32 * pv := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h3, h8, hw, hr, hsub, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      Option.getD_some, PVM.bitwise_and_m1]

/-- 42392, the chunk before allocated: to 42597. -/
theorem pv_br_used {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (c : Nat) (h12 : ω[12] = UInt64.ofNat c) (hc : c ≠ 0) (hc2 : c < 2) :
    FreeStepsH p R 42392 ω μ x 42597 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12, hc]

/-- 42392, the chunk before free: to 42396. -/
theorem pv_br_free {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h12 : ω[12] = UInt64.ofNat 0) :
    FreeStepsH p R 42392 ω μ x 42396 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12]

end Services.Bootstrap.Alloc
