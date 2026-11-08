import Services.Bootstrap.Alloc.AllocWrap

/-!
# The binary's `alloc_impl` with any alignment: the blocks

`alloc_impl` (41177 …) with an alignment of `al = 2^k` units (ω₈), the heap in use, no growth:

* 41425 … 41514: the chunk's offsets. The data's unit, counted from address 0, is the first
  multiple of `al` after C's header: `(B + c + al) &~ (al − 1)`, B = base / 32 and c = (C − base) / 32
  — the model's `dataOff`. Then the header's unit, the left remainder `lhs` (the model's `leftOf`),
  the right remainder and the allocation's end;
* 41726 … 41870, `lhs ≠ 0`: the left remainder, at C, registered free (`register_free_space`): its
  bin, C's header (C's old `prev`, `lhs` units free, the bin's old head, 0), the bin's head C, the
  old head's back link, and the bin's bits; the allocated chunk's `prev` is then `lhs`;
* 40494 … 41177: the wrapper `alloc` passes the alignment `(ω₈ + 31) / 32` units.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `and` with the complement of the low `k` bits rounds down to a multiple of `2^k`. -/
theorem andInv_pow {a k : Nat} (ha : a < 2 ^ 64) :
    Exec.bitwise (fun x y => x && !y) a (2 ^ k - 1) = a / 2 ^ k * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < 64
  · by_cases hik : i < k
    · simp [hi, hik]; omega
    · simp [hi, hik, Nat.sub_add_cancel (Nat.le_of_not_lt hik)]; omega
  · have : a.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    by_cases hik : k ≤ i
    · simp [hi, hik, Nat.sub_add_cancel hik, this]
    · simp [hi, hik]

/-- **41425 … 41455**, alignment `al` units: as `al_offs1`, with ω₅ = al − 1. -/
theorem al_offs1A {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp C base A al : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C)
    (h8 : ω[8] = UInt64.ofNat al) (hal : 1 ≤ al) (hal1 : al < 4294967296)
    (hf : rdN μ (sp + 120) 8 = 204984) (hb : rdN μ 206520 8 = base) (ha : rdN μ 206840 4 = A)
    (hA : A < 2147483648) (hbC : base ≤ C) (hC : C < 18446744073709551616)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41425 ω μ x 41455 ω' μ' x 12 ∧ ω'[2] = UInt64.ofNat A ∧
      ω'[5] = UInt64.ofNat (al - 1) ∧
      ω'[6] = UInt64.ofNat base ∧ ω'[12] = UInt64.ofNat (C - base) ∧
      μ'.readN (sp + 64) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (sp + 32) 8 = Num.encodeLE 8 ω[2].toNat ∧
      μ'.readN (sp + 40) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp + 88) 8 = Num.encodeLE 8 ω[3].toNat ∧
      (∀ a, a < 4294967296 → (a < sp + 32 ∨ sp + 96 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  have e5 : (al % 18446744073709551616 + 18446744073709551615) % 18446744073709551616 = al - 1 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h10, h8, hf, hb, ha, sxw4_small hA, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha1 ha2 => ?_, fun a => ?_,
      by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- **41455 … 41476**, alignment `2^k` units: the base saved; in units, the base B, the chunk's
    offset c, and the data's unit `(B + c + 2^k) / 2^k · 2^k`. -/
theorem al_offs2A {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D base k : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat D)
    (h6 : ω[6] = UInt64.ofNat base) (h5 : ω[5] = UInt64.ofNat (2 ^ k - 1)) (hk : k < 32)
    (hD : D < 4294967296) (hb : base < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41455 ω μ x 41476 ω' μ' x 7 ∧ ω'[6] = UInt64.ofNat (base / 32) ∧
      ω'[8] = UInt64.ofNat ((base / 32 + D / 32 + 2 ^ k) / 2 ^ k * 2 ^ k) ∧ ω'[12] = UInt64.ofNat (D / 32) ∧
      μ'.readN (sp + 96) 8 = Num.encodeLE 8 base ∧
      (∀ a, a < 4294967296 → (a < sp + 96 ∨ sp + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hk2 : 2 ^ k < 4294967296 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hk) (by decide)
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h12, h6, h5, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, ?_, fun a ha1 ha2 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
      congr 1
      rw [andInv_pow (by simp only [Nat.reducePow]; omega)]
      congr 2; omega
    · rd_simp []
    · rd_simp []
    · rd_simp [hwr]

/-- **41476 … 41514**, a left remainder of `lhs` units: the data's offset d = c + lhs + 1, the
    header's c + lhs, `lhs`, the space on the right `sz − lhs − req − 1`, and the end of the
    allocation in units. -/
theorem al_offs3A {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp B c lhs req sz A C : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat B)
    (h8 : ω[8] = UInt64.ofNat (B + (c + lhs + 1))) (h12 : ω[12] = UInt64.ofNat c) (h9 : ω[9] = UInt64.ofNat req)
    (h11 : ω[11] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat A) (h10 : ω[10] = UInt64.ofNat C)
    (hc : B + c + lhs + 1 < 4294967296) (hrq : lhs + req + 1 ≤ sz) (hsz : sz < 2147483648)
    (hcr : c + lhs + 1 + req + 1 < 2147483648) (hB : B < 4294967296) (hA : A < 2147483648)
    (hC : C < 18446744073709551616)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41476 ω μ x 41514 ω' μ' x 13 ∧ ω'[6] = UInt64.ofNat (c + lhs + 1) ∧
      ω'[3] = UInt64.ofNat (c + lhs) ∧ ω'[0] = UInt64.ofNat lhs ∧ ω'[11] = UInt64.ofNat (sz - lhs - req - 1) ∧
      ω'[8] = UInt64.ofNat (req + (c + lhs + 1)) ∧
      ω'[5] = UInt64.ofNat (c + lhs + 1 + req + (if sz - lhs - req - 1 = 0 then 0 else 1)) ∧
      μ'.readN (sp + 72) 8 = Num.encodeLE 8 (c + lhs + 1) ∧
      μ'.readN (sp + 104) 8 = Num.encodeLE 8 (sz - lhs - req - 1) ∧
      μ'.readN (sp + 80) 8 = Num.encodeLE 8 A ∧ μ'.readN (sp + 56) 8 = Num.encodeLE 8 C ∧
      (∀ a, a < 4294967296 → (a < sp + 56 ∨ sp + 64 ≤ a) → (a < sp + 72 ∨ sp + 88 ≤ a) →
        (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 6, 8, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have e1 : (B + (c + lhs + 1) + 4294967296 - B) % 4294967296 = c + lhs + 1 := by omega
  have e2 : (c + lhs + 1) / 2147483648 = 0 := by omega
  have e3 : (c + lhs + 4294967296 - c) % 4294967296 = lhs := by omega
  have e3' : lhs / 2147483648 = 0 := by omega
  have e4 : Exec.bitwise (fun x1 x2 => x1 ^^ x2) (lhs + req) 18446744073709551615 % 18446744073709551616 =
      18446744073709551615 - (lhs + req) := by rw [xor_ones (by omega)]; omega
  have e5 : (sz + (18446744073709551615 - (lhs + req))) % 4294967296 = sz - lhs - req - 1 := by omega
  have e6 : (sz - lhs - req - 1) / 2147483648 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h8, h12, h9, h11, h2, h10, e1, e2, e3, e3', Nat.zero_add, e4, e5, e6, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha1 ha2 ha3 ha4 => ?_,
      fun a => ?_, by reg_frame⟩
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
      congr 1
      by_cases hz : sz - lhs - req - 1 = 0
      · rw [if_neg (by omega), if_pos hz]; omega
      · rw [if_pos (by omega), if_neg hz]; omega
    · rd_simp []
    · rd_simp []; congr 1; omega
    · rd_simp [Nat.mod_eq_of_lt (show A < 18446744073709551616 by omega)]
    · rd_simp [Nat.mod_eq_of_lt hC]
    · rd_simp []
    · rd_simp [hwr]

/-- **41726 … 41736**, a left remainder (ω₀ = lhs ≠ 0): ω₂ the allocated chunk `base + 32·c`. -/
theorem al_lbr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp base c lhs : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat (32 * c))
    (h0 : ω[0] = UInt64.ofNat lhs) (hl0 : lhs ≠ 0) (hl : lhs < 18446744073709551616)
    (hb : rdN μ (sp + 96) 8 = base)
    (hbc : base + 32 * c < 18446744073709551616) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat}
    (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41726 ω μ x 41736 ω' μ x 3 ∧ ω'[2] = UInt64.ofNat (base + 32 * c) ∧
      ∀ j : Fin 13, j.val ∉ [2] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h8, h0, hb, Nat.mod_eq_of_lt hl, hl0, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- **41736 … 41777**, a left remainder of 1 … 127 units: ω₁₂ = its bin + 1. -/
theorem al_lbin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (lhs : Nat) (h0 : ω[0] = UInt64.ofNat lhs) (h1 : 1 ≤ lhs) (h2 : lhs ≤ 127) :
    ∃ ω', FreeStepsH p R 41736 ω μ x 41777 ω' μ x 2 ∧ ω'[12] = UInt64.ofNat (binDown lhs + 1) ∧
      ∀ j : Fin 13, j.val ∉ [12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h2]
  case post =>
    refine ⟨?_, by reg_frame⟩
    rw [binDown_small h1 h2]; reg_val

/-- **41736 … 41777**, a left remainder of 128 units or more: ω₁₂ = its bin + 1. -/
theorem al_lbin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (lhs : Nat) (h0 : ω[0] = UInt64.ofNat lhs) (hs : 128 ≤ lhs) (hs32 : lhs < 4294967296) :
    ∃ ω', FreeStepsH p R 41736 ω μ x 41777 ω' μ x 14 ∧ ω'[12] = UInt64.ofNat (binDown lhs + 1) ∧
      ∀ j : Fin 13, j.val ∉ [6, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, show ¬ lhs ≤ 127 by omega]
  case post =>
    refine ⟨?_, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
    congr 1
    have hy : (if lhs ≤ 33554432 then lhs else 33554432) % 18446744073709551616 % 4294967296 =
        min lhs 33554432 := by split <;> omega
    rw [hy, binDown_big hs]
    have hy0 : min lhs 33554432 ≠ 0 := by omega
    have hy1 : 128 ≤ min lhs 33554432 := by omega
    have hy2 : min lhs 33554432 ≤ 33554432 := by omega
    clear hy
    generalize min lhs 33554432 = y at *
    rw [clz32 hy0 (by omega)]
    have hL1 : 7 ≤ Nat.log2 y := (Nat.le_log2 hy0).mpr (by simpa using hy1)
    have hL2 : Nat.log2 y < 26 := (Nat.log2_lt hy0).mpr (by simpa using Nat.lt_of_le_of_lt hy2 (by decide))
    have hv : y / 2 ^ (Nat.log2 y - 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have := Nat.lt_log2_self (n := y)
      calc y < 2 ^ (Nat.log2 y + 1) := this
        _ = 256 * 2 ^ (Nat.log2 y - 7) := by
          rw [show Nat.log2 y + 1 = 8 + (Nat.log2 y - 7) by omega, Nat.pow_add]
    rw [show (18446744073709551640 - (31 - Nat.log2 y) % 18446744073709551616) % 18446744073709551616 % 32 =
      Nat.log2 y - 7 by omega]
    generalize y / 2 ^ (Nat.log2 y - 7) = v at *
    simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
      bitwise_and_m127]
    omega

/-- **41777 … 41870**: ω₁₂ = bin + 1; the left remainder C's header (C's old `prev`, `lhs` units
    free, the bin's old head, 0), the bin's head C, the old head's back link C, and the bin's bits
    set (`register_free_space`). -/
theorem al_lwrite {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin C pv lhs old : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat (bin + 1))
    (h0 : ω[0] = UInt64.ofNat lhs) (h7 : ω[7] = UInt64.ofNat 196792)
    (h56 : rdN μ (sp + 56) 8 = C) (h48 : rdN μ (sp + 48) 8 = pv)
    (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hb : bin < 2432) (hN : C < 2147483648) (hNa : 206864 ≤ C) (hpv : pv < 4294967296)
    (hsz : 2 * lhs < 4294967296)
    (hold : rdN μ (bin * 4 + 196792) 4 = old) (hold1 : old < 2147483648)
    (holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ C ∨ C + 16 ≤ old))
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hNT : C + 16 ≤ HT) (holdT : old ≠ 0 → old + 16 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41777 ω μ x 41870 ω' μ' x 40 ∧
      rdN μ' (bin * 4 + 196792) 4 = C ∧ rdN μ' C 4 = pv ∧ rdN μ' (C + 4) 4 = 2 * lhs ∧
      rdN μ' (C + 8) 4 = old ∧ rdN μ' (C + 12) 4 = 0 ∧ (old ≠ 0 → rdN μ' (old + 12) 4 = C) ∧
      rdN μ' (bin / 64 * 8 + 204984 + 1544) 8 = rdN μ (bin / 64 * 8 + 204984 + 1544) 8 ||| 2 ^ (bin % 64) ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (bin / 64) ∧
      (∀ a, a < 4294967296 → (a < bin * 4 + 196792 ∨ bin * 4 + 196796 ≤ a) → (a < C ∨ C + 16 ≤ a) →
        (old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a) →
        (a < bin / 64 * 8 + 204984 + 1544 ∨ bin / 64 * 8 + 204984 + 1552 ≤ a) → (a < 206832 ∨ 206840 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hbin : (bin + 1 + 18446744073709551615) % 4294967296 = bin := by omega
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0' : old = 0
  · subst h0'
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h12, h0, h7, h56, h48, h88, h120, hbin, hold, hw, hr, rdN_writeN_disjoint,
      ↓rdN_fold, ↓loadI_fold]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_frame⟩
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · intro h; exact absurd rfl h
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; rw [show bin % 64 % 18446744073709551616 % 64 = bin % 64 by omega]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (Nat.mod_lt _ (by decide))
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (by omega)
      · clear h0 h7 h56 h48 h88 h120 hold holda holdT hNT hSTk hHTs h12 hbin hold1 hpv hsz hsp0 hsp hr hw
        rd_simp [bitwise_and_m63, rdN_mod64]
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]
  · obtain ⟨ho1, ho2⟩ := holda h0'
    clear holda
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h12, h0, h7, h56, h48, h88, h120, hbin, hold, hw, hr, rdN_writeN_disjoint,
      ↓rdN_fold, ↓loadI_fold]
    case post' =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_frame⟩
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; rw [show bin % 64 % 18446744073709551616 % 64 = bin % 64 by omega]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (Nat.mod_lt _ (by decide))
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (by omega)
      · clear h0 h7 h56 h48 h88 h120 hold holdT hNT hSTk hHTs h12 hbin hpv hsz hsp0 hsp hr hw
        have h3' : a < old + 12 ∨ old + 16 ≤ a := by omega
        clear h3 h0'
        rd_simp [bitwise_and_m63, rdN_mod64]
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]

/-- **40494 … 41177**, an alignment of `al` octets: as `al_lock`, the units of the alignment,
    `K = (al + 31) / 32`, passed in ω₈. -/
theorem al_lock_align {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp size al K : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size)
    (h8 : ω[8] = UInt64.ofNat al) (hK : (al + 31) / 32 = K) (hK1 : K < 2147483648)
    (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40494 ω μ x 41177 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat K ∧
      ω'[9] = UInt64.ofNat ((size + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1984 ∧
      ω'[5] = UInt64.ofNat 196792 ∧ ω'[4] = ω[4] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
        (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 4, 5, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  have hal : al < 137438953440 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hand, show ¬ 137438953440 < al by omega, show 137438953440 ≥ size by omega,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, ?_, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_,
      fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rw [hK]
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rw [show sp - 8 = sp - 16 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

end Services.Bootstrap.Alloc
