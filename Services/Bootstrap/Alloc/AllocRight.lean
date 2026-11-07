import Services.Bootstrap.Alloc.AllocWrite

/-!
# The binary's `alloc_impl`: the free space on the right

41910 … 42054: when the chunk had more than the allocation needs, the rest — `rhs` units at the
next chunk N, after the allocated `req + 1` — is registered free, first in its bin (the model's
`register s N (req + 1) rhs`).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `or_word` with the operands the other way round. -/
theorem or_word' (w k : Nat) (hw : w < 2 ^ 64) (hk : k < 64) :
    Exec.bitwise (· || ·) (2 ^ k % 18446744073709551616) (w % 18446744073709551616) % 18446744073709551616 %
      2 ^ (8 * 8) = w ||| 2 ^ k := by
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (show 2 ^ k < 18446744073709551616 from hp),
    bitwise_or_lor _ _ hp hw, Nat.or_comm]
  have := Nat.or_lt_two_pow hw hp
  rw [Nat.mod_eq_of_lt (show w ||| 2 ^ k < 18446744073709551616 from this),
    Nat.mod_eq_of_lt (show w ||| 2 ^ k < 2 ^ (8 * 8) from this)]

/-- **41958 … 42054**: ω₆ = bin + 1; N's header (pv, rhs units free, the bin's old head, 0), the
    bin's head N, the old head's back link N, and the bin's bits set. -/
theorem ar_write {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin N pv rhs old : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat (bin + 1))
    (h8 : ω[8] = UInt64.ofNat N) (h3 : ω[3] = UInt64.ofNat pv) (h12 : ω[12] = UInt64.ofNat rhs)
    (h7 : ω[7] = UInt64.ofNat 196792) (h88 : rdN μ (sp + 88) 8 = 204984) (h120 : rdN μ (sp + 120) 8 = 204984)
    (h104 : rdN μ (sp + 104) 8 = rhs)
    (hb : bin < 2432) (hN : N < 2147483648) (hNa : 206864 ≤ N) (hpv : pv < 4294967296)
    (hsz : 2 * rhs < 4294967296)
    (hold : rdN μ (196792 + bin * 4) 4 = old) (hold1 : old < 2147483648)
    (holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ N ∨ N + 16 ≤ old))
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hNT : N + 16 ≤ HT) (holdT : old ≠ 0 → old + 16 ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41958 ω μ x 42054 ω' μ' x 40 ∧
      rdN μ' (196792 + bin * 4) 4 = N ∧ rdN μ' N 4 = pv ∧ rdN μ' (N + 4) 4 = 2 * rhs ∧
      rdN μ' (N + 8) 4 = old ∧ rdN μ' (N + 12) 4 = 0 ∧ (old ≠ 0 → rdN μ' (old + 12) 4 = N) ∧
      rdN μ' (bin / 64 * 8 + 204984 + 1544) 8 = rdN μ (bin / 64 * 8 + 204984 + 1544) 8 ||| 2 ^ (bin % 64) ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (bin / 64) ∧
      (∀ a, a < 4294967296 → (a < 196792 + bin * 4 ∨ 196792 + bin * 4 + 4 ≤ a) → (a < N ∨ N + 16 ≤ a) →
        (old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a) →
        (a < bin / 64 * 8 + 204984 + 1544 ∨ bin / 64 * 8 + 204984 + 1552 ≤ a) → (a < 206832 ∨ 206840 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ω'[3] = UInt64.ofNat rhs ∧ ω'[10] = ω[10] ∧ ω'[12] = UInt64.ofNat rhs ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 6, 7, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hbin : (bin + 1 + 18446744073709551615) % 4294967296 = bin := by omega
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : old = 0
  · subst h0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h6, h8, h3, h12, h7, h88, h120, h104, hbin, hold, hw, hr, rdN_writeN_disjoint,
      ↓rdN_fold, ↓loadI_fold]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_val, by reg_val; rfl, by reg_val,
        by reg_frame⟩
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · intro h; exact absurd rfl h
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; rw [show bin % 64 % 18446744073709551616 % 64 = bin % 64 by omega]; exact or_word _ _ (decodeLE_readN8_lt _ _) (Nat.mod_lt _ (by decide))
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (by omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]
  · obtain ⟨ho1, ho2⟩ := holda h0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h6, h8, h3, h12, h7, h88, h120, h104, hbin, hold, hw, hr, rdN_writeN_disjoint,
      ↓rdN_fold, ↓loadI_fold]
    case post' =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_val,
        by reg_val; rfl, by reg_val, by reg_frame⟩
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp [Num.decodeLE])
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; (simp only [Nat.reducePow, Nat.reduceMul]; omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; rw [show bin % 64 % 18446744073709551616 % 64 = bin % 64 by omega]; exact or_word _ _ (decodeLE_readN8_lt _ _) (Nat.mod_lt _ (by decide))
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]; exact or_word' _ _ (decodeLE_readN8_lt _ _) (by omega)
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]
      · rd_simp [bitwise_and_m63, rdN_mod64, hw]

/-- 41910: nothing left on the right, to 42054. -/
theorem ar_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h12 : ω[12] = UInt64.ofNat 0) : FreeStepsH p R 41910 ω μ x 42054 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h12]

/-- **41910 … 41958**, 1 … 127 units on the right: ω₆ = its bin + 1. -/
theorem ar_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (rhs : Nat) (h12 : ω[12] = UInt64.ofNat rhs) (h1 : 1 ≤ rhs) (h2 : rhs ≤ 127) :
    ∃ ω', FreeStepsH p R 41910 ω μ x 41958 ω' μ x 3 ∧ ω'[6] = UInt64.ofNat (binDown rhs + 1) ∧
      ∀ j : Fin 13, j.val ∉ [6] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h12, show rhs ≠ 0 by omega, h2]
  case post =>
    refine ⟨?_, by reg_frame⟩
    rw [binDown_small h1 h2]; reg_val

/-- **41910 … 41958**, 128 units or more on the right: ω₆ = its bin + 1, ω₁₂ reloaded. -/
theorem ar_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp rhs : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h12 : ω[12] = UInt64.ofNat rhs)
    (h104 : rdN μ (sp + 104) 8 = rhs) (hs : 128 ≤ rhs) (hs32 : rhs < 4294967296) (hsp : sp + 152 < 4294967296)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 41910 ω μ x 41958 ω' μ x 16 ∧ ω'[6] = UInt64.ofNat (binDown rhs + 1) ∧
      ω'[12] = UInt64.ofNat rhs ∧ ∀ j : Fin 13, j.val ∉ [6, 9, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h12, h104, show rhs ≠ 0 by omega, show ¬ rhs ≤ 127 by omega, hr, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_frame⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
    congr 1
    have hy : (if rhs ≤ 33554432 then rhs else 33554432) % 18446744073709551616 % 4294967296 =
        min rhs 33554432 := by split <;> omega
    rw [hy, binDown_big hs]
    have hy0 : min rhs 33554432 ≠ 0 := by omega
    have hy1 : 128 ≤ min rhs 33554432 := by omega
    have hy2 : min rhs 33554432 ≤ 33554432 := by omega
    clear hy
    generalize min rhs 33554432 = y at *
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

end Services.Bootstrap.Alloc
