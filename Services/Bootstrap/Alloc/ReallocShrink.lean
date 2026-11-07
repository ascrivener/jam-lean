import Services.Bootstrap.Alloc.ReallocEntry

/-!
# The binary's `shrink_inplace`: the merge with the next chunk

`realloc_impl`'s inlined `shrink_inplace` (43101 … 43677), its copy of `free`'s merge with the
next chunk: the old next chunk nc (ω₆), free with `sz` units, leaves its bin's list. ω₇ = the
allocator, ω₁₂ = nc, the new size `n` is saved at sp + 112 and the allocator + 8192 at sp + 120.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43101 … 43549**, a free chunk of 1 … 127 units (size word 2·sz in ω₁₁): ω₃ = its bin
    sz − 1, ω₁₀ = sz; ω₅ (n) saved at sp + 112. -/
theorem rs_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n sz : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (h11 : ω[11] = UInt64.ofNat (2 * sz)) (hs1 : 1 ≤ sz) (hs2 : sz < 128) (hn : n < 4294967296)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43101 ω μ x 43549 ω' μ' x 9 ∧ ω'[3] = UInt64.ofNat (sz - 1) ∧
      ω'[10] = UInt64.ofNat sz ∧ rdN μ' (sp + 112) 8 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 112 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [3, 9, 10] → ω'[j] = ω[j] := by
  have hsh : 2 * sz / 2 = sz := by omega
  have hc1 : ¬ 67108864 < 2 * sz := by omega
  have hc2 : 2 * sz ≠ 0 := by omega
  have hc3 : ¬ 256 ≤ 2 * sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h11, hsh, hc1, hc2, hc3, hwr]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- **43101 … 43549**, a free chunk of 128 … 2²⁵ units (size word 2·sz in ω₁₁): ω₃ = its bin,
    ω₁₀ = sz; ω₅ (n) saved at sp + 112. -/
theorem rs_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n sz : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (h11 : ω[11] = UInt64.ofNat (2 * sz)) (hs1 : 128 ≤ sz) (hs2 : sz ≤ 33554432) (hn : n < 4294967296)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43101 ω μ x 43549 ω' μ' x 16 ∧ ω'[3] = UInt64.ofNat (binDown sz) ∧
      ω'[10] = UInt64.ofNat sz ∧ rdN μ' (sp + 112) 8 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 112 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [3, 5, 9, 10, 11] → ω'[j] = ω[j] := by
  have hsh : 2 * sz / 2 = sz := by omega
  have hc1 : ¬ 67108864 < 2 * sz := by omega
  have hc2 : 2 * sz ≠ 0 := by omega
  have hc3 : 256 ≤ 2 * sz := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h11, hsh, hc1, hc2, hc3, hwr]
  case post =>
    refine ⟨?_, by reg_val, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
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
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- **43549 … 43560**: ω₉ = the head slot of bin ω₃, ω₁₁ = the bin's head `hd`. -/
theorem rs_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin hd : Nat) (h3 : ω[3] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792) (hb : bin < 2432)
    (hhd : rdN μ (196792 + bin * 4) 4 = hd) (hhd1 : hd < 2147483648) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 43549 ω μ x 43560 ω' μ x 4 ∧ ω'[9] = UInt64.ofNat (196792 + bin * 4) ∧
      ω'[11] = UInt64.ofNat hd ∧ ∀ j : Fin 13, j.val ∉ [9, 11] → ω'[j] = ω[j] := by
  have hsx : sxw 4 hd = hd := sxw4_small hhd1
  have hq : bin * 4294967296 % 18446744073709551616 / 1073741824 = bin * 4 := by omega
  have hhd' : rdN μ (bin * 4 + 196792) 4 = hd := by rw [Nat.add_comm]; exact hhd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h3, h7, hhd', hr, hsx, hq, ↓rdN_fold, ↓loadI_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_frame⟩

/-- 43560: the chunk is its bin's head, to 43563. -/
theorem rs_br_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a : Nat) (h11 : ω[11] = UInt64.ofNat a) (h12 : ω[12] = UInt64.ofNat a) :
    FreeStepsH p R 43560 ω μ x 43563 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, h12]

/-- 43560: the chunk is not its bin's head, to 43583. -/
theorem rs_br_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (a b : Nat) (h11 : ω[11] = UInt64.ofNat b) (h12 : ω[12] = UInt64.ofNat a) (hab : b ≠ a)
    (ha : a < 2147483648) (hb : b < 2147483648) :
    FreeStepsH p R 43560 ω μ x 43583 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, h12, hab]

/-- **43563 … 43677**, the chunk nc its bin's head, with a successor `nxt`: the bin's head becomes
    `nxt`, whose back link is cleared; ω₂ = size + sz, ω₅ = n (from sp + 112). -/
theorem rs_unlink_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc slot nxt size sz n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat nc)
    (h9 : ω[9] = UInt64.ofNat slot) (h10 : ω[10] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size)
    (hn : rdN μ (nc + 8) 4 = nxt) (h112 : rdN μ (sp + 112) 8 = n)
    (hnc : nc + 16 < 4294967296) (hn0 : nxt ≠ 0) (hn1 : nxt + 16 < 2147483648) (hsl : slot + 4 ≤ 206864)
    (hna : 206864 ≤ nxt) (hss : size + sz < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43563 ω μ x 43677 ω' μ' x 8 ∧
      rdN μ' slot 4 = nxt ∧ rdN μ' (nxt + 12) 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → (a < nxt + 12 ∨ nxt + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  have hn32 : nxt < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h9, h10, h2, hn, hn0, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish
    all_goals try reg_val
    all_goals try reg_frame
    all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]

/-- **43563 … 43607**, the chunk its bin's head and last: the bin's head becomes 0. -/
theorem rs_unlink_head0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc slot : Nat) (h6 : ω[6] = UInt64.ofNat nc) (h9 : ω[9] = UInt64.ofNat slot)
    (hn : rdN μ (nc + 8) 4 = 0) (hnc : nc + 16 < 4294967296) (hsl : slot + 4 ≤ 206864)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43563 ω μ x 43607 ω' μ' x 4 ∧ rdN μ' slot 4 = 0 ∧
      (∀ a, a < 4294967296 → (a < slot ∨ slot + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h6, h9, hn, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, fun a ha h1 => ?_, fun a => ?_, ?_⟩
    all_goals try rd_simp [hw]
    all_goals try rd_finish
    all_goals try reg_frame

/-- **43583 … 43677**, the chunk nc inside its bin's list, between `prv` and `nxt` (0 if last):
    `prv`'s next becomes `nxt`, and `nxt`'s back link `prv`; ω₂ = size + sz, ω₅ = n. -/
theorem rs_unlink_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp nc prv nxt size sz n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat nc)
    (h10 : ω[10] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size)
    (hn : rdN μ (nc + 8) 4 = nxt) (hp : rdN μ (nc + 12) 4 = prv) (h112 : rdN μ (sp + 112) 8 = n)
    (hnc : nc + 16 < 4294967296)
    (hn1 : nxt + 16 < 2147483648) (hp1 : prv + 16 < 2147483648) (hna : nxt ≠ 0 → (nxt + 16 ≤ prv ∨ prv + 16 ≤ nxt))
    (hss : size + sz < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43583 ω μ x 43677 ω' μ' x 9 ∧
      rdN μ' (prv + 8) 4 = nxt ∧ (nxt ≠ 0 → rdN μ' (nxt + 12) 4 = prv) ∧
      (∀ a, a < 4294967296 → (a < prv + 8 ∨ prv + 12 ≤ a) → (nxt = 0 ∨ a < nxt + 12 ∨ nxt + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn0 : nxt = 0
  · subst hn0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h6, h10, h2, hn, hp, hw, hr, ↓rdN_fold]
    case post =>
      refine ⟨?_, fun h => absurd rfl h, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish
      all_goals try reg_val
      all_goals try reg_frame
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]
  · have hd := hna hn0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h6, h10, h2, hn, hp, hn0, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨?_, fun _ => ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, ?_⟩
      all_goals try rd_simp [hw]
      all_goals try rd_finish
      all_goals try reg_val
      all_goals try reg_frame
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]

/-- **43607 … 43677**, the bin's list now empty: its bit is cleared in its secondary word w, and if
    that leaves the word 0, the word's bit in the primary word; ω₂ = size + sz, ω₅ = n. -/
theorem rs_clear {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin w pri size sz n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h3 : ω[3] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (h10 : ω[10] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size)
    (hb : bin < 2432) (hw : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 = w) (hp : rdN μ 206832 8 = pri)
    (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = n)
    (hss : size + sz < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43607 ω μ x 43677 ω' μ' x 21 ∧
      rdN μ' (bin / 64 * 8 + 204984 + 1544) 8 = w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) ∧
      rdN μ' 206832 8 = (if w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 then
        pri &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else pri) ∧
      (∀ a, a < 4294967296 → (a < bin / 64 * 8 + 204984 + 1544 ∨ bin / 64 * 8 + 204984 + 1552 ≤ a) →
        (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[2] = UInt64.ofNat (size + sz) ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 9, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
  have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
  have hc1 := clear_word' (bin % 64) w (Nat.mod_lt _ (by decide)) hw64
  have hc2 := clear_word (bin / 64) pri (by omega) hp64
  rw [← hw] at hc1
  rw [← hp, rdN_mod64] at hc2
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : w &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0
  · have hz' : rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h3, h7, h10, h2, h120, hwr, hr, bitwise_and_m63, rdN_mod64, hc1, hc2, hz',
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_val
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hw64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hw64)]
  · have hz' : ¬ rdN μ (bin / 64 * 8 + 204984 + 1544) 8 &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64)) = 0 := by
      rw [hw]; exact hz
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h3, h7, h10, h2, h120, hwr, hr, bitwise_and_m63, rdN_mod64, hc1, hz',
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post' =>
      refine ⟨?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, ?_, ?_, by reg_frame⟩
      all_goals try rd_simp [hwr, hz, hw, hp]
      all_goals try (simp [Num.decodeLE]; done)
      all_goals try reg_val
      all_goals try rw [show Num.decodeLE (μ.readN (sp + 112) 8) = n from h112]
      all_goals try rw [show Num.decodeLE (μ.readN 206832 8) = pri from hp]
      all_goals try rw [show Num.decodeLE (μ.readN (bin / 64 * 8 + 204984 + 1544) 8) = w from hw]
      all_goals try rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 18446744073709551616 from clear_lt _ _ hw64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hp64)]
      all_goals try rw [Nat.mod_eq_of_lt (show _ < 2 ^ (8 * 8) from clear_lt _ _ hw64)]

end Services.Bootstrap.Alloc
