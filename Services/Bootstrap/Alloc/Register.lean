import Services.Bootstrap.Alloc.Arith
import Services.Bootstrap.Code
import PVM.Logic.Go

/-!
# `register_free_space` in the binary

The free path's inlined `register_free_space` (42814 … 42948): the bin of the merged size
(42814 … 42862), then the chunk's header, the bin's head, the old head's back link and the
bitmap (42862 … 42948).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}


/-- 42814 … 42862, a size of 1 … 127 units: ω₉ = the size. -/
theorem reg_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (size : Nat) (h2 : ω[2] = UInt64.ofNat size) (h0 : size ≠ 0) (hs : size ≤ 127) :
    ∃ ω', FreeStepsH p R 42814 ω μ x 42862 ω' μ x 3 ∧ ω'[9] = UInt64.ofNat size ∧
      ∀ j : Fin 13, j.val ≠ 9 → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h2]
  case post =>
    refine ⟨by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some'], fun j hj => ?_⟩
    simp only [Fin.getElem_fin]
    rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
    simp [PVM.lookup_cons_nat, hj]

/-- 42814 … 42862, a size of 128 units or more: ω₉ = the bin of the size, plus one. -/
theorem reg_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (size : Nat) (h2 : ω[2] = UInt64.ofNat size) (hs : 128 ≤ size) (hs32 : size < 4294967296) :
    ∃ ω', FreeStepsH p R 42814 ω μ x 42862 ω' μ x 15 ∧ ω'[9] = UInt64.ofNat (binDown size + 1) ∧
      ∀ j : Fin 13, j.val ∉ [9, 10, 11] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h2]
  case post =>
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
      congr 1
      have hy : (if size ≤ 33554432 then size else 33554432) % 18446744073709551616 % 4294967296 =
          min size 33554432 := by split <;> omega
      rw [hy, binDown_big hs]
      have hy0 : min size 33554432 ≠ 0 := by omega
      have hy1 : 128 ≤ min size 33554432 := by omega
      have hy2 : min size 33554432 ≤ 33554432 := by omega
      clear hy
      generalize min size 33554432 = y at *
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
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3]


theorem or_word (w k : Nat) (hw : w < 2 ^ 64) (hk : k < 64) :
    Exec.bitwise (· || ·) (w % 18446744073709551616) (2 ^ k % 18446744073709551616) % 18446744073709551616 %
      2 ^ (8 * 8) = w ||| 2 ^ k := by
  have hp : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have hw' : w % 18446744073709551616 = w := Nat.mod_eq_of_lt hw
  have hp' : 2 ^ k % 18446744073709551616 = 2 ^ k := Nat.mod_eq_of_lt hp
  rw [hw', hp', bitwise_or_lor _ _ hw hp]
  have := Nat.or_lt_two_pow hw hp
  rw [Nat.mod_eq_of_lt this, show 2 ^ (8 * 8) = 2 ^ 64 by rfl, Nat.mod_eq_of_lt this]

theorem decodeLE_readN8_lt (μ : Memory) (a : Nat) : Num.decodeLE (μ.readN a 8) < 2 ^ 64 := by
  have := decodeLE_lt (μ.readN a 8)
  rwa [Memory.length_readN] at this

/-- Close the side goals of a block's read-back facts. -/
macro "rd_finish" : tactic => `(tactic| first
  | (simp only [Nat.reducePow, Nat.reduceMul]; omega)
  | (simp [Num.decodeLE]; done)
  | (intro h; exact absurd rfl h)
  | (rw [show ∀ b : Nat, b % 64 % 18446744073709551616 % 64 = b % 64 from fun b => by omega];
     exact or_word _ _ (decodeLE_readN8_lt _ _) (Nat.mod_lt _ (by decide)))
  | (exact or_word _ _ (decodeLE_readN8_lt _ _) (by omega)))

/-- Close a register-frame goal `∀ j ∉ l, ω'[j] = ω[j]` after `pvm_go`. -/
macro "reg_frame" : tactic => `(tactic| (
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp only [Fin.getElem_fin]
  rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
  simp [PVM.lookup_cons_nat, hj]))

/-- Close a register-value goal `ω'[j] = UInt64.ofNat v` after `pvm_go`. -/
macro "reg_val" : tactic => `(tactic| (
  simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
    Option.getD_some]
  try (congr 1; omega)))

/-- The memory facts `simp` uses to read back through the writes. -/
macro "rd_simp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
    PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
    PVM.Num.length_encodeLE, PVM.Num.decodeLE_encodeLE, List.length_cons, List.length_nil, PVM.two32, $hs,*])

/-- **42862 … 42948**, ω₉ = bin + 1: the chunk M becomes the bin's first, with header (pv, 2·size,
    old, 0) where `old` was the bin's head; the old head, if any, points back to M; the bin's bits
    are set in the secondary and primary words. Nothing else in memory changes. -/
theorem reg_write {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (bin M pv size old : Nat) (h9 : ω[9] = UInt64.ofNat (bin + 1)) (h2 : ω[2] = UInt64.ofNat size)
    (h8 : ω[8] = UInt64.ofNat M) (h3 : ω[3] = UInt64.ofNat pv) (h7 : ω[7] = UInt64.ofNat 196792)
    (h4 : ω[4] = UInt64.ofNat 204984) (hb : bin < 2432) (hM : M < 2147483648) (hMa : 206864 ≤ M)
    (hpv : pv < 4294967296) (hsz : 2 * size < 4294967296)
    (hold : rdN μ (bin * 4 + 196792) 4 = old) (hold1 : old < 2147483648)
    (holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ M ∨ M + 16 ≤ old))
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42862 ω μ x 42948 ω' μ' x 30 ∧
      rdN μ' (bin * 4 + 196792) 4 = M ∧ rdN μ' M 4 = pv ∧ rdN μ' (M + 4) 4 = 2 * size ∧
      rdN μ' (M + 8) 4 = old ∧ rdN μ' (M + 12) 4 = 0 ∧ (old ≠ 0 → rdN μ' (old + 12) 4 = M) ∧
      rdN μ' (204984 + bin / 64 * 8 + 1544) 8 = rdN μ (204984 + bin / 64 * 8 + 1544) 8 ||| 2 ^ (bin % 64) ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (bin / 64) ∧
      (∀ a, a < 4294967296 → (a < bin * 4 + 196792 ∨ bin * 4 + 196796 ≤ a) → (a < M ∨ M + 16 ≤ a) →
        (old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a) →
        (a < 204984 + bin / 64 * 8 + 1544 ∨ 204984 + bin / 64 * 8 + 1552 ≤ a) → (a < 206832 ∨ 206840 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 7, 9, 10, 11] → ω'[j] = ω[j] := by
  have hbin : (bin + 1 + 18446744073709551615) % 4294967296 = bin := by omega
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : old = 0
  · subst h0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h9, h2, h8, h3, h7, h4, hbin, hold, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals first | rd_finish | reg_frame
  · obtain ⟨ho1, ho2⟩ := holda h0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h9, h2, h8, h3, h7, h4, hbin, hold, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post' =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, ?_⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals first | rd_finish | reg_frame

end Services.Bootstrap.Alloc
