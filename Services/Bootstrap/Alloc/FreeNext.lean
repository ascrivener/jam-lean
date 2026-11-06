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

/-- 42630 … 42718, a free chunk of 128 … 2²⁵ units (size word 2·sz): ω₅ = its bin. -/
theorem nx_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sz : Nat) (h5 : ω[5] = UInt64.ofNat (2 * sz)) (hs1 : 128 ≤ sz) (hs2 : sz ≤ 33554432) :
    ∃ ω', FreeStepsH p R 42630 ω μ x 42718 ω' μ x 16 ∧ ω'[0] = UInt64.ofNat sz ∧
      ω'[5] = UInt64.ofNat (binDown sz) ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 6, 10] → ω'[j] = ω[j] := by
  have hsh : 2 * sz / 2 = sz := by omega
  have hc1 : ¬ 67108864 < 2 * sz := by omega
  have hc2 : 2 * sz ≠ 0 := by omega
  have hc3 : 256 ≤ 2 * sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, hsh, hc1, hc2, hc3]
  case post =>
    refine ⟨by reg_val, ?_, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      Option.getD_some]
    congr 1
    rw [binDown_big hs1, show min sz 33554432 = sz by omega]
    have hy0 : sz ≠ 0 := by omega
    rw [clz32 hy0 (by omega)]
    have hL1 : 7 ≤ Nat.log2 sz := (Nat.le_log2 hy0).mpr (by simpa using hs1)
    have hL2 : Nat.log2 sz < 26 := (Nat.log2_lt hy0).mpr (by simpa using Nat.lt_of_le_of_lt hs2 (by decide))
    have hv : sz / 2 ^ (Nat.log2 sz - 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have := Nat.lt_log2_self (n := sz)
      calc sz < 2 ^ (Nat.log2 sz + 1) := this
        _ = 256 * 2 ^ (Nat.log2 sz - 7) := by
          rw [show Nat.log2 sz + 1 = 8 + (Nat.log2 sz - 7) by omega, Nat.pow_add]
    rw [show (18446744073709551640 - (31 - Nat.log2 sz) % 18446744073709551616) % 18446744073709551616 % 32 =
      Nat.log2 sz - 7 by omega]
    generalize sz / 2 ^ (Nat.log2 sz - 7) = v at *
    simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
      bitwise_and_m127]
    omega

/-- 42718 … 42729: ω₆ = the head slot of bin ω₅, ω₁₀ = the bin's head `hd`. -/
theorem nx_head_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin hd : Nat) (h5 : ω[5] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792) (hb : bin < 2432)
    (hhd : rdN μ (196792 + bin * 4) 4 = hd) (hhd1 : hd < 2147483648) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42718 ω μ x 42729 ω' μ x 4 ∧ ω'[6] = UInt64.ofNat (196792 + bin * 4) ∧
      ω'[10] = UInt64.ofNat hd ∧ ∀ j : Fin 13, j.val ∉ [6, 10] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hq : bin * 4294967296 % 18446744073709551616 / 1073741824 = bin * 4 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h7, hhd, hr, hsx, hq, ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_frame⟩

/-- 42672 / 42729: the chunk is its bin's head, to 42675. -/
theorem nx_br_head_s {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h10 : ω[10] = UInt64.ofNat a) :
    FreeStepsH p R 42672 ω μ x 42675 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h10]

theorem nx_br_head_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h9 : ω[9] = UInt64.ofNat a) (h10 : ω[10] = UInt64.ofNat a) :
    FreeStepsH p R 42729 ω μ x 42675 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h10]

/-- 42672 / 42729: the chunk is not its bin's head, to 42732. -/
theorem nx_br_mid_s {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h10 : ω[10] = UInt64.ofNat b) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42672 ω μ x 42732 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h10, hab]

theorem nx_br_mid_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h9 : ω[9] = UInt64.ofNat a) (h10 : ω[10] = UInt64.ofNat b) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 42729 ω μ x 42732 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h9, h10, hab]

/-- 42675 … 42814, the chunk nc its bin's head, with a successor `nxt`: the bin's head becomes
    `nxt`, whose back link is cleared; ω₂ = size + sz. -/
theorem nx_unlink_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc slot nxt size sz : Nat) (h11 : ω[11] = UInt64.ofNat nc) (h6 : ω[6] = UInt64.ofNat slot)
    (h0 : ω[0] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size) (hn : rdN μ (nc + 8) 4 = nxt)
    (hnc : nc + 16 < 4294967296) (hn0 : nxt ≠ 0) (hn1 : nxt + 16 < 4294967296) (hsl : slot + 4 ≤ 206864) (hna : 206864 ≤ nxt)
    (hss : size + sz < 2147483648) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42675 ω μ x 42814 ω' μ' x 7 ∧
      rdN μ' slot 4 = nxt ∧ rdN μ' (nxt + 12) 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < nxt + 12 ∨ nxt + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧
      ∀ j : Fin 13, j.val ∉ [2, 9] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  have hn32 : nxt < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h11, h6, h0, h2, hn, hn0, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish
    all_goals try reg_val
    all_goals try reg_frame

/-- 42675 … 42753, the chunk its bin's head and last: the bin's head becomes 0. -/
theorem nx_unlink_head0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc slot : Nat) (h11 : ω[11] = UInt64.ofNat nc) (h6 : ω[6] = UInt64.ofNat slot)
    (hn : rdN μ (nc + 8) 4 = 0) (hnc : nc + 16 < 4294967296) (hsl : slot + 4 ≤ 206864)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42675 ω μ x 42753 ω' μ' x 4 ∧ rdN μ' slot 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [9] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h11, h6, hn, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, fun a ha h1 => ?_, fun a => ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish
    all_goals try reg_frame

/-- 42732 … 42814, the chunk nc inside its bin's list, between `prv` and `nxt` (0 if last):
    `prv`'s next becomes `nxt`, and `nxt`'s back link `prv`; ω₂ = size + sz. -/
theorem nx_unlink_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc prv nxt size sz : Nat) (h11 : ω[11] = UInt64.ofNat nc) (h0 : ω[0] = UInt64.ofNat sz)
    (h2 : ω[2] = UInt64.ofNat size) (hn : rdN μ (nc + 8) 4 = nxt) (hp : rdN μ (nc + 12) 4 = prv)
    (hnc : nc + 16 < 4294967296)
    (hn1 : nxt + 16 < 4294967296) (hp1 : prv + 16 < 4294967296) (hna : nxt ≠ 0 → (nxt + 16 ≤ prv ∨ prv + 16 ≤ nxt))
    (hss : size + sz < 2147483648) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42732 ω μ x 42814 ω' μ' x 8 ∧
      rdN μ' (prv + 8) 4 = nxt ∧ (nxt ≠ 0 → rdN μ' (nxt + 12) 4 = prv) ∧
      (∀ a, a < 4294967296 → (a < prv + 8 ∨ prv + 12 ≤ a) → (nxt = 0 ∨ a < nxt + 12 ∨ nxt + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧
      ∀ j : Fin 13, j.val ∉ [2, 9, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn0 : nxt = 0
  · subst hn0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h11, h0, h2, hn, hp, hw, hr, ↓rdN_fold]
    case post =>
      refine ⟨?_, fun h => absurd rfl h, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish
      all_goals try reg_val
      all_goals try reg_frame
  · have hd := hna hn0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h11, h0, h2, hn, hp, hn0, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨?_, fun _ => ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish
      all_goals try reg_val
      all_goals try reg_frame

theorem clear_word (k w : Nat) (hk : k < 64) (hw : w < 2 ^ 64) :
    Exec.bitwise (· && ·) (Num.rotl 64 18446744073709551614 k % 18446744073709551616) (w % 18446744073709551616) =
      w &&& ((2 ^ 64 - 1) ^^^ 2 ^ k) := by
  have hm : (2 ^ 64 - 1) ^^^ 2 ^ k < 2 ^ 64 :=
    Nat.xor_lt_two_pow (by decide) (Nat.pow_lt_pow_right (by decide) hk)
  rw [rotl_clear k hk, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hw, bitwise_and_land _ _ hw, Nat.and_comm]

theorem clear_lt (k w : Nat) (hw : w < 2 ^ 64) : w &&& ((2 ^ 64 - 1) ^^^ 2 ^ k) < 2 ^ 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_left hw

/-- **42753 … 42814**, the bin's list now empty: its bit is cleared in its secondary word w, and if
    that leaves the word 0, the word's bit in the primary word; ω₂ = size + sz. -/
theorem nx_clear {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin w pri size sz : Nat) (h5 : ω[5] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792)
    (h4 : ω[4] = UInt64.ofNat 204984) (h0 : ω[0] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size)
    (hb : bin < 2432) (hw : rdN μ (204984 + bin / 64 * 8 + 1544) 8 = w) (hp : rdN μ 206832 8 = pri)
    (hss : size + sz < 2147483648) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42753 ω μ x 42814 ω' μ' x 19 ∧
      rdN μ' (204984 + bin / 64 * 8 + 1544) 8 = w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) ∧
      rdN μ' 206832 8 = (if w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 then
        pri &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else pri) ∧
      (∀ a, a < 4294967296 → (a < 204984 + bin / 64 * 8 + 1544 ∨ 204984 + bin / 64 * 8 + 1552 ≤ a) →
        (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
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
  · have hz' : rdN μ (204984 + bin / 64 * 8 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h5, h7, h4, h0, h2, hwr, hr, bitwise_and_m63, hc1, hc2, hz', ↓rdN_fold]
    case post =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_⟩
      all_goals try rd_simp [hwr, hz, hc2, hw, hp]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try reg_val
      all_goals try reg_frame
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try exact hp
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (204984 + bin / 64 * 8 + 1544) 8) = w from hw]
      all_goals try rw [clear_word _ _ (by omega) hp64]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (clear_lt _ _ hp64)]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)
  · have hz' : ¬ rdN μ (204984 + bin / 64 * 8 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h5, h7, h4, h0, h2, hwr, hr, bitwise_and_m63, hc1, hz', ↓rdN_fold]
    case post' =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      all_goals try reg_val
      all_goals try reg_frame
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try exact hp
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (204984 + bin / 64 * 8 + 1544) 8) = w from hw]
      all_goals try rw [clear_word _ _ (by omega) hp64]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (clear_lt _ _ hp64)]
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hp64)
      all_goals try exact Nat.mod_eq_of_lt (clear_lt _ _ hw64)

end Services.Bootstrap.Alloc
