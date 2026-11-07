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
    {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hpH : 196608 ≤ ptr - 32 ∧ ptr - 32 + 16 ≤ HT) (hS : S0 + 24 ≤ sp ∧ sp ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42327 ω μ x 42369 ω' μ' x 14 ∧
      ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[8] = UInt64.ofNat (ptr - 32) ∧ ω'[4] = UInt64.ofNat 204984 ∧
      ω'[5] = UInt64.ofNat base ∧ ω'[10] = UInt64.ofNat w ∧ ω'[3] = UInt64.ofNat pv ∧
      ω'[9] = UInt64.ofNat (ptr - 32 - base) ∧ ω'[11] = UInt64.ofNat 31 ∧ ω'[2] = UInt64.ofNat (w / 2) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [1, 2, 3, 4, 5, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
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
    (hX : Xa < 2147483648) (hw : rdN μ (Xa - 32 * pv + 4) 4 = pw) {HT S0 S1 : Nat}
    (hXH : 196608 ≤ Xa - 32 * pv ∧ Xa - 32 * pv + 16 ≤ HT) (hr : RdAt μ HT S0 S1) :
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

/-- 42396 … 42439, the chunk before (at Pa) free with 1 … 127 units (size word 2·psz): ω₅ = its
    bin, ω₆ = the bin's head slot, ω₁₂ = the bin's head, ω₃ = its own `prev`, ω₁₀ = psz. -/
theorem pv_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (psz Pa hd ppv : Nat) (h0 : ω[0] = UInt64.ofNat (2 * psz)) (h7 : ω[7] = UInt64.ofNat 196792)
    (h11 : ω[11] = UInt64.ofNat Pa) (hs1 : 1 ≤ psz) (hs2 : psz < 128)
    (hhd : rdN μ (196792 + (psz - 1) * 4) 4 = hd) (hhd1 : hd < 2147483648)
    (hpp : rdN μ Pa 4 = ppv) (hpp1 : ppv < 2147483648) (hPa : Pa < 2147483648)
    {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hPH : 196608 ≤ Pa ∧ Pa + 16 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 42396 ω μ x 42439 ω' μ x 13 ∧ ω'[10] = UInt64.ofNat psz ∧
      ω'[5] = UInt64.ofNat (psz - 1) ∧ ω'[6] = UInt64.ofNat (196792 + (psz - 1) * 4) ∧
      ω'[12] = UInt64.ofNat hd ∧ ω'[3] = UInt64.ofNat ppv ∧
      ∀ j : Fin 13, j.val ∉ [3, 5, 6, 10, 12] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hsx2 : sxw 4 ppv = ppv := sxw4_small hpp1
  have hsh : 2 * psz / 2 = psz := by omega
  have hb : (psz - 1) % 4294967296 = psz - 1 := by omega
  have hq : (psz - 1) * 4294967296 / 1073741824 = (psz - 1) * 4 := by omega
  have hq' : (psz - 1) * 4294967296 % 18446744073709551616 / 1073741824 = (psz - 1) * 4 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h7, h11, hhd, hpp, hr, hsx, hsx2, hsh, hb, hq, hq', ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 42396 … 42470, the chunk before free with 128 … 2²⁵ units (size word 2·psz): ω₅ = its bin,
    ω₁₀ = psz. -/
theorem pv_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (psz : Nat) (h0 : ω[0] = UInt64.ofNat (2 * psz)) (hs1 : 128 ≤ psz) (hs2 : psz ≤ 33554432) :
    ∃ ω', FreeStepsH p R 42396 ω μ x 42470 ω' μ x 15 ∧ ω'[10] = UInt64.ofNat psz ∧
      ω'[5] = UInt64.ofNat (binDown psz) ∧ ∀ j : Fin 13, j.val ∉ [5, 6, 10, 12] → ω'[j] = ω[j] := by
  have hsh : 2 * psz / 2 = psz := by omega
  have hc1 : ¬ 67108864 < 2 * psz := by omega
  have hc2 : 2 * psz ≠ 0 := by omega
  have hc3 : 256 ≤ 2 * psz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, hsh, hc1, hc2, hc3]
  case post =>
    refine ⟨by reg_val, ?_, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      Option.getD_some]
    congr 1
    rw [binDown_big hs1, show min psz 33554432 = psz by omega]
    have hy0 : psz ≠ 0 := by omega
    rw [clz32 hy0 (by omega)]
    have hL1 : 7 ≤ Nat.log2 psz := (Nat.le_log2 hy0).mpr (by simpa using hs1)
    have hL2 : Nat.log2 psz < 26 := (Nat.log2_lt hy0).mpr (by simpa using Nat.lt_of_le_of_lt hs2 (by decide))
    have hv : psz / 2 ^ (Nat.log2 psz - 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have := Nat.lt_log2_self (n := psz)
      calc psz < 2 ^ (Nat.log2 psz + 1) := this
        _ = 256 * 2 ^ (Nat.log2 psz - 7) := by
          rw [show Nat.log2 psz + 1 = 8 + (Nat.log2 psz - 7) by omega, Nat.pow_add]
    rw [show (18446744073709551640 - (31 - Nat.log2 psz) % 18446744073709551616) % 18446744073709551616 % 32 =
      Nat.log2 psz - 7 by omega]
    generalize psz / 2 ^ (Nat.log2 psz - 7) = v at *
    simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
      bitwise_and_m127]
    omega

/-- 42470 … 42483: ω₆ = the head slot of bin ω₅, ω₁₂ = the bin's head, ω₃ = the chunk's `prev`. -/
theorem pv_head_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin hd Pa ppv : Nat) (h5 : ω[5] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792)
    (h11 : ω[11] = UInt64.ofNat Pa) (hb : bin < 2432)
    (hhd : rdN μ (196792 + bin * 4) 4 = hd) (hhd1 : hd < 2147483648)
    (hpp : rdN μ Pa 4 = ppv) (hpp1 : ppv < 2147483648) (hPa : Pa < 2147483648)
    {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hPH : 196608 ≤ Pa ∧ Pa + 16 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 42470 ω μ x 42483 ω' μ x 5 ∧ ω'[6] = UInt64.ofNat (196792 + bin * 4) ∧
      ω'[12] = UInt64.ofNat hd ∧ ω'[3] = UInt64.ofNat ppv ∧
      ∀ j : Fin 13, j.val ∉ [3, 6, 12] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hsx2 : sxw 4 ppv = ppv := sxw4_small hpp1
  have hq : bin * 4294967296 % 18446744073709551616 / 1073741824 = bin * 4 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h7, h11, hhd, hpp, hr, hsx, hsx2, hq, ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- 42439 / 42483: the chunk before is its bin's head, to 42486. -/
theorem pv_br_head_s {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat a) :
    FreeStepsH p R 42439 ω μ x 42486 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12]

theorem pv_br_head_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat a) :
    FreeStepsH p R 42483 ω μ x 42486 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12]

/-- 42439 / 42483: the chunk before is inside its bin's list, to 42512. -/
theorem pv_br_mid_s {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat b) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42439 ω μ x 42512 ω μ x 2 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12, hab]

theorem pv_br_mid_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat b) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42483 ω μ x 42512 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h12, hab]

/-- 42486 … 42583, the chunk before (at Pa) its bin's head, with a successor `nxt`. -/
theorem pv_unlink_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (Pa slot nxt : Nat) (h11 : ω[11] = UInt64.ofNat Pa) (h6 : ω[6] = UInt64.ofNat slot)
    (hn : rdN μ (Pa + 8) 4 = nxt) (hPa : Pa + 16 < 4294967296) (hn0 : nxt ≠ 0)
    (hn1 : nxt + 16 < 4294967296) (hsl : slot + 4 ≤ 206864) (hna : 206864 ≤ nxt)
    {HT S0 S1 : Nat} (hsl0 : 196608 ≤ slot) (hPH : 196608 ≤ Pa ∧ Pa + 16 ≤ HT) (hnxH : nxt + 16 ≤ HT)
    (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42486 ω μ x 42583 ω' μ' x 6 ∧
      rdN μ' slot 4 = nxt ∧ rdN μ' (nxt + 12) 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < nxt + 12 ∨ nxt + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [9] → ω'[j] = ω[j] := by
  have hr := hw.rd
  have hn32 : nxt < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h11, h6, hn, hn0, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
    all_goals try (simp [Num.decodeLE]; done)
    all_goals try reg_frame

/-- 42486 … 42530, the chunk before its bin's head and last: the bin's head becomes 0. -/
theorem pv_unlink_head0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (Pa slot : Nat) (h11 : ω[11] = UInt64.ofNat Pa) (h6 : ω[6] = UInt64.ofNat slot)
    (hn : rdN μ (Pa + 8) 4 = 0) (hPa : Pa + 16 < 4294967296) (hsl : slot + 4 ≤ 206864)
    {HT S0 S1 : Nat} (hsl0 : 196608 ≤ slot) (hH : 206864 ≤ HT) (hPH : 196608 ≤ Pa ∧ Pa + 16 ≤ HT)
    (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42486 ω μ x 42530 ω' μ' x 4 ∧ rdN μ' slot 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [9] → ω'[j] = ω[j] := by
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h11, h6, hn, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, fun a ha h1 => ?_, fun a => ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
    all_goals try (simp [Num.decodeLE]; done)
    all_goals try reg_frame

/-- 42512 … 42583, the chunk before inside its bin's list, between `prv` and `nxt` (0 if last). -/
theorem pv_unlink_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (Pa prv nxt : Nat) (h11 : ω[11] = UInt64.ofNat Pa)
    (hn : rdN μ (Pa + 8) 4 = nxt) (hp : rdN μ (Pa + 12) 4 = prv) (hPa : Pa + 16 < 4294967296)
    (hn1 : nxt + 16 < 4294967296) (hp1 : prv + 16 < 4294967296)
    (hna : nxt ≠ 0 → (nxt + 16 ≤ prv ∨ prv + 16 ≤ nxt)) {HT S0 S1 : Nat} (hPH : 196608 ≤ Pa ∧ Pa + 16 ≤ HT)
    (hpvH : 196608 ≤ prv ∧ prv + 16 ≤ HT) (hnxH : nxt ≠ 0 → 196608 ≤ nxt ∧ nxt + 16 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42512 ω μ x 42583 ω' μ' x 7 ∧
      rdN μ' (prv + 8) 4 = nxt ∧ (nxt ≠ 0 → rdN μ' (nxt + 12) 4 = prv) ∧
      (∀ a, a < 4294967296 → (a < prv + 8 ∨ prv + 12 ≤ a) → (nxt = 0 ∨ a < nxt + 12 ∨ nxt + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [9, 11] → ω'[j] = ω[j] := by
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn0 : nxt = 0
  · subst hn0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h11, hn, hp, hw, hr, ↓rdN_fold]
    case post =>
      refine ⟨?_, fun h => absurd rfl h, fun a ha h1 h2 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_frame
  · have hd := hna hn0
    have hnx := hnxH hn0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h11, hn, hp, hn0, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨?_, fun _ => ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_frame

/-- 42583 … 42597: ω₅ = the base, ω₂ = psz + size, ω₈ = the merged chunk Xa − 16·pw. -/
theorem pv_join {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (base psz size pw Xa : Nat) (h4 : ω[4] = UInt64.ofNat 204984) (h10 : ω[10] = UInt64.ofNat psz)
    (h2 : ω[2] = UInt64.ofNat size) (h0 : ω[0] = UInt64.ofNat pw) (h8 : ω[8] = UInt64.ofNat Xa)
    (hb : rdN μ 206520 8 = base) (hss : psz + size < 2147483648) (hpw : 16 * pw ≤ Xa)
    (hX : Xa < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 42583 ω μ x 42597 ω' μ x 5 ∧ ω'[5] = UInt64.ofNat base ∧
      ω'[2] = UInt64.ofNat (psz + size) ∧ ω'[8] = UInt64.ofNat (Xa - 16 * pw) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 5, 8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h4, h10, h2, h0, h8, hb, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **42530 … 42583** (the chunk before), the bin's list now empty: its bit is cleared in its secondary word w, and if
    that leaves the word 0, the word's bit in the primary word -/
theorem pv_clear {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w pri : Nat) (h5 : ω[5] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792)
    (h4 : ω[4] = UInt64.ofNat 204984) (hb : bin < 2432) (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (hp : rdN μ 206832 8 = pri)
    {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42530 ω μ x 42583 ω' μ' x 18 ∧
      rdN μ' (bin / 64 * 8 + 204984 + 1544) 8 = w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) ∧
      rdN μ' 206832 8 = (if w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 then
        pri &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else pri) ∧
      (∀ a, a < 4294967296 → (a < bin / 64 * 8 + 204984 + 1544 ∨ bin / 64 * 8 + 204984 + 1552 ≤ a) →
        (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 9, 11, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
  have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
  have hc1 := clear_word (bin % 64) w (Nat.mod_lt _ (by decide)) hw64
  have hc2 := clear_word (bin / 64) pri (by omega) hp64
  have hl1 := clear_lt (bin % 64) w hw64
  have hl2 := clear_lt (bin / 64) pri hp64
  rw [← hw] at hc1 hl1
  rw [← hp] at hc2 hl2
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0
  · have hz' : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h5, h7, h4, hwr, hr, bitwise_and_m63, hc1, hc2, hz', ↓rdN_fold]
    case post =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [hwr, hz, hc2, hw, hp]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try reg_frame
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try exact hp
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [clear_word _ _ (by omega) hp64]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (clear_lt _ _ hp64)]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)
  · have hz' : ¬ rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h5, h7, h4, hwr, hr, bitwise_and_m63, hc1, hz', ↓rdN_fold]
    case post' =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try reg_frame
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try exact hp
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [clear_word _ _ (by omega) hp64]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (clear_lt _ _ hp64)]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)

/-- **42948 … the return's `jumpInd` (42978)**: the chunk after the merged one (M, `total`
    units), if below the heap's end, records `total` as its `prev`; ω₀ (the caller's return
    address `ret`), ω₅, ω₆ and sp come back from the frame. -/
theorem free_epi {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp M total en v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat (sp - 24)) (h2 : ω[2] = UInt64.ofNat total)
    (h8 : ω[8] = UInt64.ofNat M) (h12 : ω[12] = UInt64.ofNat en) (hsp : 2147483700 ≤ sp)
    (hsp1 : sp < 4294967296) (hMt : M + 32 * total < 2147483648) (hen : en < 2147483648)
    (ht : total < 4294967296)
    {ret : Nat} (s0 : μ.readN (sp - 8) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (sp - 16) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (sp - 24) 8 = Num.encodeLE 8 v6) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hret : ret < 18446744073709551616) {HT S0 S1 : Nat} (hS : S0 + 24 ≤ sp ∧ sp ≤ S1)
    (hMH : M + 32 * total < en → 196608 ≤ M + 32 * total ∧ M + 32 * total + 4 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42948 ω μ x 42978 ω' μ' x 13 ∧
      (M + 32 * total < en → rdN μ' (M + 32 * total) 4 = total) ∧
      (∀ a, a < 4294967296 → (en ≤ M + 32 * total ∨ a < M + 32 * total ∨ M + 32 * total + 4 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7] → ω'[j] = ω[j] := by
  have hr := hw.rd
  have r0 : rdN μ (sp - 24 + 16) 8 = ret := by
    rw [show sp - 24 + 16 = sp - 8 by omega]; exact rdN_of' s0 hret
  have r5 : rdN μ (sp - 24 + 8) 8 = v5 := by
    rw [show sp - 24 + 8 = sp - 16 by omega]; exact rdN_of' s5 hv5
  have r6 : rdN μ (sp - 24) 8 = v6 := rdN_of' s6 hv6
  rw [show ω = regsNF ω [] from rfl]
  by_cases hlt : M + 32 * total < en
  · have hlt' : ¬ en ≤ total * 32 + M := by omega
    have hMH' := hMH hlt
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h2, h8, h12, r0, r5, r6, hlt', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨fun _ => ?_, fun a ha h1 => ?_, fun a => ?_, by reg_val, by reg_val, by reg_val, ?_, by reg_frame⟩
      · rw [show M + 32 * total = total * 32 + M by omega]; rd_simp []
        simp only [Nat.reducePow, Nat.reduceMul]; omega
      · rd_simp []
      · rd_simp [hw]
      · reg_val
  · have hge : en ≤ total * 32 + M := by omega
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h2, h8, h12, r0, r5, r6, hge, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨fun h => absurd h hlt, fun a ha h1 => rfl, fun a => rfl, by reg_val, by reg_val, by reg_val,
        by reg_val, by reg_frame⟩

end Services.Bootstrap.Alloc
