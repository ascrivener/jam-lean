import Services.Bootstrap.Alloc.AllocSearch

/-!
# The binary's `alloc_impl`: the chunk's offsets
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **41425 … 41455**, alignment one unit: the bin's slot, word and bit and the bitmap's address
    saved; the base, the allocated space and the chunk's offset in octets. -/
theorem al_offs1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp C base A : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C)
    (h8 : ω[8] = UInt64.ofNat 1)
    (hf : rdN μ (sp + 120) 8 = 204984) (hb : rdN μ 206520 8 = base) (ha : rdN μ 206840 4 = A)
    (hA : A < 2147483648) (hbC : base ≤ C) (hC : C < 18446744073709551616)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41425 ω μ x 41455 ω' μ' x 12 ∧ ω'[2] = UInt64.ofNat A ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat base ∧ ω'[12] = UInt64.ofNat (C - base) ∧
      μ'.readN (sp + 64) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (sp + 32) 8 = Num.encodeLE 8 ω[2].toNat ∧
      μ'.readN (sp + 40) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp + 88) 8 = Num.encodeLE 8 ω[3].toNat ∧
      (∀ a, a < 4294967296 → (a < sp + 32 ∨ sp + 96 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h10, h8, hf, hb, ha, sxw4_small hA, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha1 ha2 => ?_, fun a => ?_,
      by reg_frame⟩
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

theorem andInv_zero (a : Nat) : Exec.bitwise (fun x y => x && !y) a 0 = a % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_mod_two_pow, Nat.zero_testBit,
    Bool.not_false, Bool.and_true]

/-- **41455 … 41476**: the base saved; in units, the base B, the chunk's offset c and the data's
    unit B + c + 1. -/
theorem al_offs2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat D)
    (h6 : ω[6] = UInt64.ofNat base) (h5 : ω[5] = UInt64.ofNat 0)
    (hD : D < 4294967296) (hb : base < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41455 ω μ x 41476 ω' μ' x 7 ∧ ω'[6] = UInt64.ofNat (base / 32) ∧
      ω'[8] = UInt64.ofNat (base / 32 + D / 32 + 1) ∧ ω'[12] = UInt64.ofNat (D / 32) ∧
      μ'.readN (sp + 96) 8 = Num.encodeLE 8 base ∧
      (∀ a, a < 4294967296 → (a < sp + 96 ∨ sp + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h12, h6, h5, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, ?_, fun a ha1 ha2 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff,
        andInv_zero]
      congr 1; omega
    · rd_simp []
    · rd_simp []
    · rd_simp [hwr]

/-- `xor` with all ones is the complement. -/
theorem xor_ones {v : Nat} (hv : v < 18446744073709551616) :
    Exec.bitwise (fun x1 x2 => x1 ^^ x2) v 18446744073709551615 = 18446744073709551615 - v := by
  rw [show (18446744073709551615 : Nat) - v = 2 ^ 64 - (v + 1) by
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega]
  apply Nat.eq_of_testBit_eq
  intro i
  have hv' : v < 2 ^ 64 := by rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; exact hv
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_two_pow_sub_succ hv']
  have h1 : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
  rw [h1, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64 <;> simp [hi]

/-- **41476 … 41514**, alignment one unit: the data's offset c + 1, the header's c, the space left
    on the left (0) and on the right, `sz − req − 1`, and the end of the allocation in units. -/
theorem al_offs3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp B c req sz A C : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat B)
    (h8 : ω[8] = UInt64.ofNat (B + c + 1)) (h12 : ω[12] = UInt64.ofNat c) (h9 : ω[9] = UInt64.ofNat req)
    (h11 : ω[11] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat A) (h10 : ω[10] = UInt64.ofNat C)
    (hc : B + c + 1 < 4294967296) (hrq : req + 1 ≤ sz) (hsz : sz < 2147483648) (hcr : c + 1 + req + 1 < 2147483648) (hB : B < 4294967296) (hA : A < 2147483648) (hC : C < 18446744073709551616)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41476 ω μ x 41514 ω' μ' x 13 ∧ ω'[6] = UInt64.ofNat (c + 1) ∧
      ω'[3] = UInt64.ofNat c ∧ ω'[0] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (sz - req - 1) ∧
      ω'[8] = UInt64.ofNat (req + (c + 1)) ∧
      ω'[5] = UInt64.ofNat (c + 1 + req + (if sz - req - 1 = 0 then 0 else 1)) ∧
      μ'.readN (sp + 72) 8 = Num.encodeLE 8 (c + 1) ∧ μ'.readN (sp + 104) 8 = Num.encodeLE 8 (sz - req - 1) ∧
      μ'.readN (sp + 80) 8 = Num.encodeLE 8 A ∧ μ'.readN (sp + 56) 8 = Num.encodeLE 8 C ∧
      (∀ a, a < 4294967296 → (a < sp + 56 ∨ sp + 64 ≤ a) → (a < sp + 72 ∨ sp + 88 ≤ a) →
        (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 6, 8, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have e1 : (B + c + 1 + 4294967296 - B) % 4294967296 = c + 1 := by omega
  have e2 : (c + 1) / 2147483648 = 0 := by omega
  have e3 : (c + 4294967296 - c) % 4294967296 = 0 := by omega
  have e4 : Exec.bitwise (fun x1 x2 => x1 ^^ x2) req 18446744073709551615 % 18446744073709551616 =
      18446744073709551615 - req := by rw [xor_ones (by omega)]; omega
  have e5 : (sz + (18446744073709551615 - req)) % 4294967296 = sz - req - 1 := by omega
  have e6 : (sz - req - 1) / 2147483648 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h8, h12, h9, h11, h2, h10, e1, e2, e3, Nat.zero_add, e4, e5, e6, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha1 ha2 ha3 ha4 => ?_, fun a => ?_,
      by reg_frame⟩
    · reg_val; rw [Nat.sub_sub]
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
      congr 1
      by_cases hz : sz - req - 1 = 0
      · rw [if_neg (by omega), if_pos hz]; omega
      · rw [if_pos (by omega), if_neg hz]; omega
    · rd_simp []
    · rd_simp [Nat.sub_sub]
    · rd_simp [Nat.mod_eq_of_lt (show A < 18446744073709551616 by omega)]
    · rd_simp [Nat.mod_eq_of_lt hC]
    · rd_simp []
    · rd_simp [hwr]

/-- 41514: the allocated space covers the allocation's end, to 41589 (no growth). -/
theorem al_nogrow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A E : Nat) (h2 : ω[2] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat E) (hAE : E ≤ A)
    (hA : A < 18446744073709551616) :
    FreeStepsH p R 41514 ω μ x 41589 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h2, h5, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (show E < 18446744073709551616 by omega), hAE]

/-- 41514: the allocation ends past the allocated space, to the growth at 41517. -/
theorem al_grow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A E : Nat) (h2 : ω[2] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat E) (hAE : A < E)
    (hE : E < 18446744073709551616) :
    FreeStepsH p R 41514 ω μ x 41517 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h2, h5, Nat.mod_eq_of_lt hE, Nat.mod_eq_of_lt (show A < 18446744073709551616 by omega),
    show ¬ E ≤ A by omega]

end Services.Bootstrap.Alloc
