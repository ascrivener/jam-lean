import Services.Bootstrap.Alloc.ReallocGrow

/-!
# The binary's `grow_inplace`: the new size and the free tail

44030 … 40805: the chunk X takes n units (its size word 2·n + 1); a tail of `rem` = avail − n units
at N = X + 32·n (ω₂), if any, is registered free with `prev` n; the chunk after (X + 32·avail)
records the tail's size (or n, without a tail); the return into `realloc`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **44030 … 44042**: X's size word (X at sp + 88) becomes 2·n + 1 (n in ω₅). -/
theorem rg_size {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Xc n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (h88 : rdN μ (sp + 88) 8 = Xc) (hX : Xc + 8 < 2147483648) (hn : 2 * n + 1 < 4294967296)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hXH : 196608 ≤ Xc ∧ Xc + 8 ≤ HT) (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 44030 ω μ x 44042 ω' μ' x 4 ∧ rdN μ' (Xc + 4) 4 = 2 * n + 1 ∧
      (∀ a, a < 4294967296 → (a < Xc + 4 ∨ Xc + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [9, 10] → ω'[j] = ω[j] := by
  have hr := hw.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h88, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hw]

/-- 44042, no tail: to 44192, then ω₇ = avail (sp + 72), to 44196. -/
theorem rg_notail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp avail : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat 0)
    (h72 : rdN μ (sp + 72) 8 = avail) (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 44042 ω μ x 44196 ω' μ x 3 ∧ ω'[7] = UInt64.ofNat avail ∧
      ∀ j : Fin 13, j.val ∉ [7] → ω'[j] = ω[j] := by
  have ha : avail < 18446744073709551616 := by rw [← h72]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h6, h72, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_frame⟩

/-- **44042 … 44090**, a tail of `rem` ≥ 1 units (ω₆): ω₁₀ = its bin + 1. -/
theorem rg_reg_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (rem : Nat) (h6 : ω[6] = UInt64.ofNat rem) (hs1 : 1 ≤ rem) (hs32 : rem < 4294967296) :
    ∃ ω', FreeStepsH p R 44042 ω μ x 44090 ω' μ x 16 ∧ ω'[10] = UInt64.ofNat (binDown rem + 1) ∧
      ∀ j : Fin 13, j.val ∉ [9, 10, 11] → ω'[j] = ω[j] := by
  have hz : rem ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  by_cases hs : rem ≤ 127
  · refine ⟨?ω', ?run, ?post⟩
    case run => pvm_go [h6, hz, hs]
    case post =>
      refine ⟨?_, by reg_frame⟩
      reg_get; rw [binDown_small (by omega) hs]; congr 1; omega
  · refine ⟨?ω'', ?run', ?post'⟩
    case run' => pvm_go [h6, hz, hs]
    case post' =>
      refine ⟨?_, by reg_frame⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      congr 1
      have hy : (if rem ≤ 33554432 then rem else 33554432) % 18446744073709551616 % 4294967296 =
          min rem 33554432 := by split <;> omega
      rw [hy, binDown_big (by omega)]
      have hy0 : min rem 33554432 ≠ 0 := by omega
      have hy1 : 128 ≤ min rem 33554432 := by omega
      have hy2 : min rem 33554432 ≤ 33554432 := by omega
      clear hy
      generalize min rem 33554432 = y at *
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

/-- **44090 … 44196**, ω₁₀ = bin + 1: the tail M (ω₂) of `size` (ω₆) units becomes the bin's first,
    with header (pv, 2·size, old, 0) where pv is at sp + 112 and `old` was the bin's head; the old
    head, if any, points back to M; the bin's bits are set; ω₇ = avail (sp + 72), ω₅ = size (saved
    at sp + 104). -/
theorem rg_reg_write {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp bin M pv size old avail : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat (bin + 1))
    (h6 : ω[6] = UInt64.ofNat size) (h2 : ω[2] = UInt64.ofNat M) (h7 : ω[7] = UInt64.ofNat 196792)
    (h3 : ω[3] = UInt64.ofNat 204984) (h112 : rdN μ (sp + 112) 8 = pv) (h72 : rdN μ (sp + 72) 8 = avail)
    (hb : bin < 2432) (hM : M < 2147483648) (hMa : 206864 ≤ M)
    (hpv : pv < 4294967296) (hsz : 2 * size < 4294967296)
    (hold : rdN μ (bin * 4 + 196792) 4 = old) (hold1 : old < 2147483648)
    (holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ M ∨ M + 16 ≤ old))
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hMH : M + 16 ≤ HT) (holdH : old ≠ 0 → old + 16 ≤ HT) (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 44090 ω μ x 44196 ω' μ' x 36 ∧
      rdN μ' (bin * 4 + 196792) 4 = M ∧ rdN μ' M 4 = pv ∧ rdN μ' (M + 4) 4 = 2 * size ∧
      rdN μ' (M + 8) 4 = old ∧ rdN μ' (M + 12) 4 = 0 ∧ (old ≠ 0 → rdN μ' (old + 12) 4 = M) ∧
      rdN μ' (204984 + bin / 64 * 8 + 1544) 8 = rdN μ (204984 + bin / 64 * 8 + 1544) 8 ||| 2 ^ (bin % 64) ∧
      rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (bin / 64) ∧
      (∀ a, a < 4294967296 → (a < bin * 4 + 196792 ∨ bin * 4 + 196796 ≤ a) → (a < M ∨ M + 16 ≤ a) →
        (old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a) →
        (a < 204984 + bin / 64 * 8 + 1544 ∨ 204984 + bin / 64 * 8 + 1552 ≤ a) → (a < 206832 ∨ 206840 ≤ a) →
        (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ω'[7] = UInt64.ofNat avail ∧ ω'[5] = UInt64.ofNat size ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 7, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hbin : (bin + 1 + 18446744073709551615) % 4294967296 = bin := by omega
  have hr := hw.rd
  have hav : avail < 18446744073709551616 := by rw [← h72]; exact rdN_lt64 μ _
  have hp' : rdN μ (204984 + 1848) 8 = rdN μ 206832 8 := rfl
  rw [show ω = regsNF ω [] from rfl]
  by_cases h0 : old = 0
  · subst h0
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h10, h6, h2, h7, h3, hbin, hold, h112, h72, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 h6 => ?_, fun a => ?_, by reg_val,
        by reg_get; rw [show rdN (μ.writeN (sp + 104) (Num.encodeLE 8 size)) (sp + 104) 8 = size by
          rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega],
        by reg_frame⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals rd_finish
  · obtain ⟨ho1, ho2⟩ := holda h0
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h10, h6, h2, h7, h3, hbin, hold, h0, h112, h72, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post' =>
      refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => ?_, ?_, ?_, fun a ha h1 h2 h3 h4 h5 h6 => ?_, fun a => ?_, by reg_val,
        by reg_get; rw [show rdN (μ.writeN (sp + 104) (Num.encodeLE 8 size)) (sp + 104) 8 = size by
          rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega],
        by reg_frame⟩
      all_goals try rd_simp [bitwise_and_m63, rdN_mod64, hw]
      all_goals rd_finish

/-- **44196 … the return to `realloc` (40805)**: the chunk after the grown allocation
    (X + 32·avail, X at sp + 120), if below the heap's end `en` (sp + 96), records v (ω₅) as its
    `prev`; ω₇ = ptr; ω₀, ω₅, ω₆ and sp come back from the frame. -/
theorem rg_epi {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Xc avail v en ptr v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat avail)
    (h5 : ω[5] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (h120 : rdN μ (sp + 120) 8 = Xc) (h96 : rdN μ (sp + 96) 8 = en)
    (hXt : Xc + 32 * avail < 2147483648) (hen : en < 2147483648) (hv : v < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hXH : Xc + 32 * avail < en → 196608 ≤ Xc + 32 * avail ∧ Xc + 32 * avail + 4 ≤ HT) (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 44196 ω μ x 40805 ω' μ' x 16 ∧
      (Xc + 32 * avail < en → rdN μ' (Xc + 32 * avail) 4 = v) ∧
      (∀ a, a < 4294967296 → (en ≤ Xc + 32 * avail ∨ a < Xc + 32 * avail ∨ Xc + 32 * avail + 4 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have hr := hw.rd
  have ha : (Xc + avail * 32 % 18446744073709551616) % 4294967296 = Xc + 32 * avail := by omega
  rw [show ω = regsNF ω [] from rfl]
  by_cases hlt : Xc + 32 * avail < en
  · have hlt' : ¬ en ≤ Xc + 32 * avail := by omega
    have hXH' := hXH hlt
    refine ⟨?ω', ?μ', ?run, ?post⟩
    case run => pvm_go [h1, h7, h5, h8, h120, h96, ha, s0, s5, s6, hlt', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    case post =>
      refine ⟨fun _ => ?_, fun a ha h1 => ?_, fun a => ?_, by reg_val, by reg_val, by reg_val, by reg_val,
        by reg_val⟩
      · rw [show Xc + 32 * avail = avail * 32 + Xc by omega]; rd_simp []
        simp only [Nat.reducePow, Nat.reduceMul]; omega
      · rd_simp []
      · rd_simp [hw]
  · have hge : en ≤ Xc + 32 * avail := by omega
    refine ⟨?ω'', ?μ'', ?run', ?post'⟩
    case run' => pvm_go [h1, h7, h5, h8, h120, h96, ha, s0, s5, s6, hge, hw, hr, ↓rdN_fold]
    case post' =>
      refine ⟨fun h => absurd h hlt, fun a ha h1 => rfl, fun a => rfl, by reg_val, by reg_val, by reg_val,
        by reg_val, by reg_val⟩

end Services.Bootstrap.Alloc
