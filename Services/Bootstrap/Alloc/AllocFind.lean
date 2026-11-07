import Services.Bootstrap.Alloc.AllocPro

/-!
# The binary's `alloc_impl`: the bin search

`BitMask::find_first` (41297 … 41378): the first non-empty bin at or after the rounded-up bin, from
the primary word and one secondary word.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The code's bit test: `(v >> k) & 1`. -/
theorem bit_test {v k : Nat} (hv : v < 18446744073709551616) :
    Exec.bitwise (· && ·) (v / 2 ^ k % 18446744073709551616) 1 % 18446744073709551616 =
      if v.testBit k then 1 else 0 := by
  rw [PVM.bitwise_and_low _ 1 1 (by decide) (by decide), Nat.testBit_eq_decide_div_mod_eq]
  have : v / 2 ^ k < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  rw [Nat.mod_eq_of_lt this]
  split <;> simp_all <;> omega

/-- The code's clearing of the bits below k: `(v >> k) << k`. -/
theorem shr_shl {w k : Nat} (hw : w < 18446744073709551616) :
    w / 2 ^ k % 18446744073709551616 * 2 ^ k % 18446744073709551616 = w / 2 ^ k * 2 ^ k := by
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw)]

/-- `lowest_set_bit_after` is the trailing zero count of the word with the lower bits cleared. -/
theorem lowestAfter_tz {v i : Nat} (hv : v < 18446744073709551616) (h : v / 2 ^ i * 2 ^ i ≠ 0) :
    lowestAfter v i = some (Num.trailingZeros 64 (v / 2 ^ i * 2 ^ i)) := by
  have ha : v / 2 ^ i * 2 ^ i < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hv
  unfold lowestAfter Num.trailingZeros
  simp only [Nat.mod_eq_of_lt ha, h, ↓reduceIte, Num.bit_eq_testBit]
  generalize v / 2 ^ i * 2 ^ i = a at ha h
  cases hf : (List.range 64).find? (fun b => a.testBit b) with
  | some b => rfl
  | none =>
    exfalso; apply h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.zero_testBit]
    by_cases hj : j < 64
    · have := List.find?_eq_none.mp hf j (List.mem_range.mpr hj)
      simpa using this
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show 64 ≤ j by omega)
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (by simpa using this))

theorem tz_le (v : Nat) : Num.trailingZeros 64 v ≤ 64 := by
  unfold Num.trailingZeros
  cases hf : (List.range 64).find? _ with
  | none => simp
  | some b => have := List.mem_range.mp (List.mem_of_find?_eq_some hf); simp; omega

theorem lowestAfter_none {v i : Nat} (h : v / 2 ^ i * 2 ^ i = 0) : lowestAfter v i = none := by
  unfold lowestAfter; simp [h]

/-- 41297 … 41320: the rounded-up bin's word has its bit in the primary word. -/
theorem ff_head_set {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin pri : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (hsp : sp + 128 < 4294967296) (hf : rdN μ (sp + 120) 8 = 204984) (hp : rdN μ 206832 8 = pri) (hb : bin < 2432)
    (hbit : pri.testBit (bin / 64) = true) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41297 ω μ x 41320 ω' μ x 7 ∧
      ω'[5] = UInt64.ofNat pri ∧ ω'[3] = UInt64.ofNat 204984 ∧ ω'[11] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [3, 5, 6, 10, 11] → ω'[j] = ω[j] := by
  have hp64 : pri < 18446744073709551616 := by rw [← hp]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h2, h7, hf, hp, hr, bit_test hp64, hbit, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 41297 … 41346: its bit is clear. -/
theorem ff_head_clr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin pri : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (hsp : sp + 128 < 4294967296) (hf : rdN μ (sp + 120) 8 = 204984) (hp : rdN μ 206832 8 = pri) (hb : bin < 2432)
    (hbit : pri.testBit (bin / 64) = false) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41297 ω μ x 41346 ω' μ x 7 ∧
      ω'[5] = UInt64.ofNat pri ∧ ω'[3] = UInt64.ofNat 204984 ∧ ω'[11] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [3, 5, 6, 10, 11] → ω'[j] = ω[j] := by
  have hp64 : pri < 18446744073709551616 := by rw [← hp]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h2, h7, hf, hp, hr, bit_test hp64, hbit, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 41320 … 41378: the secondary word has a bin at or after `bin`'s: ω₆ its word, ω₂ its bit. -/
theorem ff_sec_found {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w : Nat) (h2 : ω[2] = UInt64.ofNat bin) (h3 : ω[3] = UInt64.ofNat 204984)
    (h11 : ω[11] = UInt64.ofNat (bin / 64)) (hb : bin < 2432)
    (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (hne : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) ≠ 0)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41320 ω μ x 41378 ω' μ x 10 ∧
      lowestAfter w (bin % 64) = some ω'[2].toNat ∧ ω'[6] = UInt64.ofNat (bin / 64) ∧ ∀ j : Fin 13, j.val ∉ [2, 6] → ω'[j] = ω[j] := by
  have hw64 : w < 18446744073709551616 := by rw [← hw]; exact rdN_lt64 μ _
  have hm : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) % 18446744073709551616 = w / 2 ^ (bin % 64) * 2 ^ (bin % 64) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h2, h3, h11, hw, shr_shl hw64, hm, hne, hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_frame⟩
    rw [lowestAfter_tz hw64 hne]
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
    have : Num.trailingZeros 64 (w / 2 ^ (bin % 64) * 2 ^ (bin % 64)) ≤ 64 := by
      unfold Num.trailingZeros
      cases hf : (List.range 64).find? _ with
      | none => simp
      | some b => have := List.mem_range.mp (List.mem_of_find?_eq_some hf); simp; omega
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show _ < 2 ^ 64 by
      rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega)]

/-- 41320 … 41346: no bin at or after `bin`'s in its word. -/
theorem ff_sec_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w : Nat) (h2 : ω[2] = UInt64.ofNat bin) (h3 : ω[3] = UInt64.ofNat 204984)
    (h11 : ω[11] = UInt64.ofNat (bin / 64)) (hb : bin < 2432)
    (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (he : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) = 0)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41320 ω μ x 41346 ω' μ x 9 ∧ ∀ j : Fin 13, j.val ∉ [6] → ω'[j] = ω[j] := by
  have hw64 : w < 18446744073709551616 := by rw [← hw]; exact rdN_lt64 μ _
  have hm : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) % 18446744073709551616 = w / 2 ^ (bin % 64) * 2 ^ (bin % 64) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h2, h3, h11, hw, shr_shl hw64, hm, he, hr, ↓rdN_fold, ↓loadI_fold]
  case post => reg_frame

theorem ff_next_found {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q pri : Nat) (h11 : ω[11] = UInt64.ofNat q) (h5 : ω[5] = UInt64.ofNat pri) (h3 : ω[3] = UInt64.ofNat 204984)
    (hq : q < 38) (hp64 : pri < 18446744073709551616)
    (hne : pri / 2 ^ (q + 1) * 2 ^ (q + 1) ≠ 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω' q', FreeStepsH p R 41346 ω μ x 41378 ω' μ x 12 ∧ lowestAfter pri (q + 1) = some q' ∧
      ω'[6] = UInt64.ofNat q' ∧ ω'[2] = UInt64.ofNat (Num.trailingZeros 64 (rdN μ (q' * 8 + 204984 + 1544) 8)) ∧
      ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j] := by
  have hm : pri / 2 ^ (q + 1) * 2 ^ (q + 1) % 18446744073709551616 = pri / 2 ^ (q + 1) * 2 ^ (q + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hp64)
  have htz := tz_le (pri / 2 ^ (q + 1) * 2 ^ (q + 1))
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', _, ?run, lowestAfter_tz hp64 hne, ?post⟩
  case run => pvm_go [h11, h5, h3, shr_shl hp64, hm, hne, hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_frame⟩
    have htz := tz_le (pri / 2 ^ (q + 1) * 2 ^ (q + 1))
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
    try rw [show (Num.trailingZeros 64 (pri / 2 ^ (q + 1) * 2 ^ (q + 1)) % 18446744073709551616 * 8 %
        18446744073709551616 + 204984) % 18446744073709551616 + 1544 =
        Num.trailingZeros 64 (pri / 2 ^ (q + 1) * 2 ^ (q + 1)) * 8 + 204984 + 1544 by omega]
    rw [Nat.mod_eq_of_lt (rdN_lt64 μ _)]

/-- 41346 … 41614: no non-empty word after the rounded-up bin's: on to the rounded-down bin. -/
theorem ff_next_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q pri : Nat) (h11 : ω[11] = UInt64.ofNat q) (h5 : ω[5] = UInt64.ofNat pri)
    (hq : q < 38) (hp64 : pri < 18446744073709551616)
    (he : pri / 2 ^ (q + 1) * 2 ^ (q + 1) = 0) :
    ∃ ω', FreeStepsH p R 41346 ω μ x 41614 ω' μ x 5 ∧ ∀ j : Fin 13, j.val ∉ [6, 11] → ω'[j] = ω[j] := by
  have hm : pri / 2 ^ (q + 1) * 2 ^ (q + 1) % 18446744073709551616 = pri / 2 ^ (q + 1) * 2 ^ (q + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hp64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h11, h5, shr_shl hp64, hm, he]
  case post => reg_frame

/-- 41359 … 41378: the next non-empty word `a` of the primary (bits below cleared): ω₆ its index,
    ω₂ the first bit of its secondary word. -/
theorem ff_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h11 : ω[11] = UInt64.ofNat a) (h3 : ω[3] = UInt64.ofNat 204984) (ha : a < 18446744073709551616)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41359 ω μ x 41378 ω' μ x 7 ∧ ω'[6] = UInt64.ofNat (Num.trailingZeros 64 a) ∧
      ω'[2] = UInt64.ofNat (Num.trailingZeros 64 (rdN μ (Num.trailingZeros 64 a * 8 + 204984 + 1544) 8)) ∧
      ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j] := by
  have htz := tz_le a
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h11, h3, Nat.mod_eq_of_lt ha, hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_frame⟩
    have htz := tz_le a
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff]
    try rw [show (Num.trailingZeros 64 a % 18446744073709551616 * 8 % 18446744073709551616 + 204984) %
        18446744073709551616 + 1544 = Num.trailingZeros 64 a * 8 + 204984 + 1544 by omega]
    rw [Nat.mod_eq_of_lt (rdN_lt64 μ _)]

/-- 41614 … 41626: the rounded-down bin's word has its bit in the primary. -/
theorem fb_head_set {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin pri : Nat) (h0 : ω[0] = UInt64.ofNat bin) (h5 : ω[5] = UInt64.ofNat pri) (hb : bin < 2432)
    (hp64 : pri < 18446744073709551616) (hbit : pri.testBit (bin / 64) = true) :
    ∃ ω', FreeStepsH p R 41614 ω μ x 41626 ω' μ x 4 ∧ ω'[6] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [6, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h5, bit_test hp64, hbit]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- 41614 … 41654: its bit is clear. -/
theorem fb_head_clr {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin pri : Nat) (h0 : ω[0] = UInt64.ofNat bin) (h5 : ω[5] = UInt64.ofNat pri) (hb : bin < 2432)
    (hp64 : pri < 18446744073709551616) (hbit : pri.testBit (bin / 64) = false) :
    ∃ ω', FreeStepsH p R 41614 ω μ x 41654 ω' μ x 4 ∧ ω'[6] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [6, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h5, bit_test hp64, hbit]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- 41626 … 41378: the rounded-down bin's word has a bin at or after it. -/
theorem fb_sec_found {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w : Nat) (h0 : ω[0] = UInt64.ofNat bin) (h3 : ω[3] = UInt64.ofNat 204984)
    (h6 : ω[6] = UInt64.ofNat (bin / 64)) (hb : bin < 2432)
    (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (hne : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) ≠ 0)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41626 ω μ x 41378 ω' μ x 12 ∧
      lowestAfter w (bin % 64) = some ω'[2].toNat ∧ ω'[6] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j] := by
  have hw64 : w < 18446744073709551616 := by rw [← hw]; exact rdN_lt64 μ _
  have hm : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) % 18446744073709551616 = w / 2 ^ (bin % 64) * 2 ^ (bin % 64) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h3, h6, hw, PVM.bitwise_and_low _ 63 6 (by decide) (by decide), shr_shl hw64, hm, hne,
    hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_frame⟩
    rw [lowestAfter_tz hw64 hne]
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
    have := tz_le (w / 2 ^ (bin % 64) * 2 ^ (bin % 64))
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show _ < 2 ^ 64 by
      rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; omega)]

/-- 41626 … 41654: no bin at or after it in its word. -/
theorem fb_sec_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w : Nat) (h0 : ω[0] = UInt64.ofNat bin) (h3 : ω[3] = UInt64.ofNat 204984)
    (h6 : ω[6] = UInt64.ofNat (bin / 64)) (hb : bin < 2432)
    (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (he : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) = 0)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41626 ω μ x 41654 ω' μ x 10 ∧ ω'[6] = UInt64.ofNat (bin / 64) ∧
      ∀ j : Fin 13, j.val ∉ [2, 6, 11] → ω'[j] = ω[j] := by
  have hw64 : w < 18446744073709551616 := by rw [← hw]; exact rdN_lt64 μ _
  have hm : w / 2 ^ (bin % 64) * 2 ^ (bin % 64) % 18446744073709551616 = w / 2 ^ (bin % 64) * 2 ^ (bin % 64) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hw64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h3, h6, hw, PVM.bitwise_and_low _ 63 6 (by decide) (by decide), shr_shl hw64, hm, he,
    hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- 41654 … 41359: a non-empty word after the rounded-down bin's. -/
theorem fb_next_found {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q pri : Nat) (h6 : ω[6] = UInt64.ofNat q) (h5 : ω[5] = UInt64.ofNat pri)
    (hq : q < 38) (hp64 : pri < 18446744073709551616) (hne : pri / 2 ^ (q + 1) * 2 ^ (q + 1) ≠ 0) :
    ∃ ω', FreeStepsH p R 41654 ω μ x 41359 ω' μ x 4 ∧
      ω'[11] = UInt64.ofNat (pri / 2 ^ (q + 1) * 2 ^ (q + 1)) ∧ ∀ j : Fin 13, j.val ∉ [6, 11] → ω'[j] = ω[j] := by
  have hm : pri / 2 ^ (q + 1) * 2 ^ (q + 1) % 18446744073709551616 = pri / 2 ^ (q + 1) * 2 ^ (q + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hp64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h6, h5, shr_shl hp64, hm, hne]
  case post => exact ⟨by reg_val, by reg_frame⟩

/-- 41654 … 41404: no non-empty bin at all: the allocation fails. -/
theorem fb_next_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q pri : Nat) (h6 : ω[6] = UInt64.ofNat q) (h5 : ω[5] = UInt64.ofNat pri)
    (hq : q < 38) (hp64 : pri < 18446744073709551616) (he : pri / 2 ^ (q + 1) * 2 ^ (q + 1) = 0) :
    ∃ ω', FreeStepsH p R 41654 ω μ x 41404 ω' μ x 6 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ∀ j : Fin 13, j.val ∉ [6, 11] → ω'[j] = ω[j] := by
  have hm : pri / 2 ^ (q + 1) * 2 ^ (q + 1) % 18446744073709551616 = pri / 2 ^ (q + 1) * 2 ^ (q + 1) :=
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hp64)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h6, h5, shr_shl hp64, hm, he]
  case post => exact ⟨by reg_val, by reg_frame⟩

theorem or_mul64 (a m : Nat) (hm : m < 64) : a * 64 ||| m = a * 64 + m := by
  have := Nat.two_pow_add_eq_or_of_lt (i := 6) (b := m) hm a
  rw [show (2 : Nat) ^ 6 = 64 by rfl, Nat.mul_comm 64 a] at this
  exact this.symm

/-- **41378**: the found bin's first chunk and its size against the minimum. -/
theorem al_pick {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (q b C w minSize : Nat) (h6 : ω[6] = UInt64.ofNat q) (h2 : ω[2] = UInt64.ofNat b)
    (h7 : ω[7] = UInt64.ofNat 196792) (h12 : ω[12] = UInt64.ofNat minSize)
    (hq : q < 38) (hb : b < 64) (hC : rdN μ (196792 + 4 * (q * 64 + b)) 4 = C)
    (hw : rdN μ (C + 4) 4 = w) (hC1 : C + 8 < 4294967296) (hm : minSize < 4294967296)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hCT : 196608 ≤ C ∧ C + 16 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41378 ω μ x 41398 ω' μ x 7 ∧ ω'[10] = UInt64.ofNat C ∧ ω'[11] = UInt64.ofNat (w / 2) ∧
      ω'[5] = UInt64.ofNat (196792 + 4 * (q * 64 + b)) ∧
      ∀ j : Fin 13, j.val ∉ [5, 10, 11] → ω'[j] = ω[j] := by
  have hor : Exec.bitwise (· || ·) (q * 64) b = q * 64 + b := by
    rw [bitwise_or_lor _ _ (by omega) (by omega), or_mul64 _ _ hb]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h6, h2, h7, h12, hor, show (q * 64 + b) * 4 = 4 * (q * 64 + b) by omega, hC,
    Nat.mod_eq_of_lt (show C < 18446744073709551616 by omega), hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, by reg_frame⟩ <;>
      try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff, hor,
        show (q * 64 + b) * 4 = 4 * (q * 64 + b) by omega, hC, hw, Nat.mod_eq_of_lt (show C < 18446744073709551616 by omega),
        Nat.mod_eq_of_lt (show w < 18446744073709551616 by rw [← hw]; exact Nat.lt_of_lt_of_le (rdN_lt μ _ 4) (by decide))]

/-- 41398: the chunk is large enough, to 41425. -/
theorem al_size_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sz minSize : Nat) (h11 : ω[11] = UInt64.ofNat sz) (h12 : ω[12] = UInt64.ofNat minSize)
    (hs : minSize ≤ sz) (hs1 : sz < 18446744073709551616) :
    FreeStepsH p R 41398 ω μ x 41425 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, h12, Nat.mod_eq_of_lt hs1, Nat.mod_eq_of_lt (show minSize < 18446744073709551616 by omega), hs]

/-- 41398: too small, to the failure at 41401. -/
theorem al_size_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sz minSize : Nat) (h11 : ω[11] = UInt64.ofNat sz) (h12 : ω[12] = UInt64.ofNat minSize)
    (hs : sz < minSize) (hm : minSize < 18446744073709551616) :
    FreeStepsH p R 41398 ω μ x 41401 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, h12, Nat.mod_eq_of_lt (show sz < 18446744073709551616 by omega), Nat.mod_eq_of_lt hm,
    show ¬ minSize ≤ sz by omega]

/-- **41401 / 41404 … 41423**: the failure: ω₇ = 0 (null), the frame popped; at the return. -/
theorem al_fail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41401 ω μ x 41423 ω' μ x 8 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 144) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

end Services.Bootstrap.Alloc
