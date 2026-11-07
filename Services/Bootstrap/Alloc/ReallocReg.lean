import Services.Bootstrap.Alloc.ReallocEntry

/-!
# The binary's `shrink_inplace`: the free tail

`realloc_impl`'s inlined registration of the free tail (43677 … 43834), its copy of `free`'s
`register_free_space`, and the return (43834 … 40805): the chunk N = X + 32·n (ω₃) of `size`
units with `prev` n becomes its bin's first, and the chunk after it records `size`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43677 … 43736**, a tail of `size` ≥ 1 units: ω₉ = its bin + 1, ω₃ = X + 32·n (with X in ω₀
    and n in ω₅), ω₄ = n; the heap's end (ω₄) saved at sp + 112. -/
theorem rs_reg_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp X0 n size en : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h0 : ω[0] = UInt64.ofNat X0)
    (h5 : ω[5] = UInt64.ofNat n) (h2 : ω[2] = UInt64.ofNat size) (h4 : ω[4] = UInt64.ofNat en)
    (hs1 : 1 ≤ size) (hs32 : size < 4294967296) (hX : X0 + 32 * n < 2147483648) (hen : en < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43677 ω μ x 43736 ω' μ' x 20 ∧ ω'[9] = UInt64.ofNat (binDown size + 1) ∧
      ω'[3] = UInt64.ofNat (X0 + 32 * n) ∧ ω'[4] = UInt64.ofNat n ∧ rdN μ' (sp + 112) 8 = en ∧
      (∀ a, a < 4294967296 → (a < sp + 112 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [3, 4, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hz : size ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  by_cases hs : size ≤ 127
  · refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h0, h5, h2, h4, hz, hs, hwr]
    case post =>
      refine ⟨?_, ?_, by reg_val, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
      · reg_get; rw [binDown_small (by omega) hs]; congr 1; omega
      · reg_get; congr 1; omega
      · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
      · rd_simp []
      · rd_simp [hwr]
  · refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h0, h5, h2, h4, hz, hs, hwr]
    case post' =>
      refine ⟨?_, ?_, by reg_val, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
      · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
        congr 1
        have hy : (if size ≤ 33554432 then size else 33554432) % 18446744073709551616 % 4294967296 =
            min size 33554432 := by split <;> omega
        rw [hy, binDown_big (by omega)]
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
      · reg_get; congr 1; omega
      · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
      · rd_simp []
      · rd_simp [hwr]

/-- **43736 … 43834**, ω₉ = bin + 1: the chunk M (ω₃) becomes the bin's first, with header
    (pv, 2·size, old, 0) where `old` was the bin's head; the old head, if any, points back to M; the
    bin's bits are set in the secondary and primary words; ω₅ = pv, ω₄ = the heap's end `en` (from
    sp + 112). Nothing else in memory changes. -/
theorem rs_reg_write {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin M pv size old en : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h9 : ω[9] = UInt64.ofNat (bin + 1))
    (h2 : ω[2] = UInt64.ofNat size) (h3 : ω[3] = UInt64.ofNat M) (h4 : ω[4] = UInt64.ofNat pv)
    (h7 : ω[7] = UInt64.ofNat 196792) (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = en)
    (hb : bin < 2432) (hM : M < 2147483648) (hMa : 206864 ≤ M)
    (hpv : pv < 4294967296) (hsz : 2 * size < 4294967296)
    (hold : rdN μ (bin * 4 + 196792) 4 = old) (hold1 : old < 2147483648)
    (holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ M ∨ M + 16 ≤ old))
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43736 ω μ x 43834 ω' μ' x 36 ∧
      rdN μ' (bin * 4 + 196792) 4 = M ∧ rdN μ' M 4 = pv ∧ rdN μ' (M + 4) 4 = 2 * size ∧
      rdN μ' (M + 8) 4 = old ∧ rdN μ' (M + 12) 4 = 0 ∧ (old ≠ 0 → rdN μ' (old + 12) 4 = M) ∧
      rdN μ' (204984 + bin / 64 * 8 + 1544) 8 = rdN μ (204984 + bin / 64 * 8 + 1544) 8 ||| 2 ^ (bin % 64) ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (bin / 64) ∧
      (∀ a, a < 4294967296 → (a < bin * 4 + 196792 ∨ bin * 4 + 196796 ≤ a) → (a < M ∨ M + 16 ≤ a) →
        (old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a) →
        (a < 204984 + bin / 64 * 8 + 1544 ∨ 204984 + bin / 64 * 8 + 1552 ≤ a) → (a < 206832 ∨ 206840 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[5] = UInt64.ofNat pv ∧ ω'[4] = UInt64.ofNat en ∧
      ∀ j : Fin 13, j.val ∉ [4, 5, 6, 7, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hbin : (bin + 1 + 18446744073709551615) % 4294967296 = bin := by omega
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  have hen : en < 18446744073709551616 := by rw [← h112]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : old = 0
  · subst h0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h9, h2, h3, h4, h7, hbin, hold, h120, h112, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_val, by reg_val,
        by reg_frame⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals rd_finish
  · obtain ⟨ho1, ho2⟩ := holda h0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h9, h2, h3, h4, h7, hbin, hold, h0, h120, h112, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post' =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 => ?_, fun a => ?_, by reg_val,
        by reg_val, by reg_frame⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals rd_finish

/-- **43834 … the return to `realloc` (40805)**: the chunk after the tail (X + 32·(n + size)), if
    below the heap's end `en`, records `size` as its `prev`; ω₇ = ptr; ω₀, ω₅, ω₆ and sp come back
    from the frame. -/
theorem rs_epi {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp X0 n size en ptr v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat size)
    (h5 : ω[5] = UInt64.ofNat n) (h0 : ω[0] = UInt64.ofNat X0) (h4 : ω[4] = UInt64.ofNat en)
    (h8 : ω[8] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (hXt : X0 + 32 * (n + size) < 2147483648) (hen : en < 2147483648) (hs : size < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43834 ω μ x 40805 ω' μ' x 14 ∧
      (X0 + 32 * (n + size) < en → rdN μ' (X0 + 32 * (n + size)) 4 = size) ∧
      (∀ a, a < 4294967296 → (en ≤ X0 + 32 * (n + size) ∨ a < X0 + 32 * (n + size) ∨
        X0 + 32 * (n + size) + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ∀ j : Fin 13, j.val ∉ [0, 1, 2, 5, 6, 7] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  have ha : (size + n) * 32 % 18446744073709551616 + X0 = X0 + 32 * (n + size) := by omega
  rw [show ω = regsNF ω [] from rfl]
  by_cases hlt : X0 + 32 * (n + size) < en
  · have hlt' : ¬ en ≤ X0 + 32 * (n + size) := by omega
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h2, h5, h0, h4, h8, ha, s0, s5, s6, hlt', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨fun _ => ?_, fun a ha h1 => ?_, fun a => ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
        by reg_frame⟩
      · rw [show X0 + 32 * (n + size) = (size + n) * 32 + X0 by omega]; rd_simp []
        simp only [Nat.reducePow, Nat.reduceMul]; omega
      · rd_simp []
      · rd_simp [hw]
  · have hge : en ≤ X0 + 32 * (n + size) := by omega
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h2, h5, h0, h4, h8, ha, s0, s5, s6, hge, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨fun h => absurd h hlt, fun a ha h1 => rfl, fun a => hw a, by reg_val, by reg_val, by reg_val,
        by reg_val, by reg_val, by reg_frame⟩

end Services.Bootstrap.Alloc
