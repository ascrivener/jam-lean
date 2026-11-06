import Services.Bootstrap.Alloc.Dealloc

/-!
# The binary's `alloc_impl`: entry

`alloc_impl` (41177, called by `alloc` with ω₀ = 1984): ω₇ the allocator, ω₈ the alignment and ω₉
the request, both in units, ω₁₀ whether to zero. The prologue saves the frame, checks that the
alignment is a power of two, and reads the heap's base (0 before the first use).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A power of two below 2^32 has one bit set. -/
theorem popcount_pow {k : Nat} (hk : k < 32) :
    Num.popcount 32 (2 ^ k % 18446744073709551616 % 4294967296) % 18446744073709551616 = 1 := by
  have : ∀ k, k < 32 → Num.popcount 32 (2 ^ k % 18446744073709551616 % 4294967296) % 18446744073709551616 = 1 := by
    decide
  exact this k hk

/-- `and` with the inverse of the mask of bits s … 63 keeps the low s bits. -/
theorem andInv_low {a s : Nat} (hs : s < 64) :
    Exec.bitwise (fun x y => x && !y) a (2 ^ 64 - 2 ^ s) = a % 2 ^ s := by
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h2 : 2 ^ s - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hs; omega
  rw [show 2 ^ 64 - 2 ^ s = 2 ^ 64 - (2 ^ s - 1 + 1) by omega]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_succ h2, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · by_cases his : i < s
    · simp [hi, his]
    · simp [hi, his]
  · have : ¬ i < s := by omega
    simp [hi, this]

/-- **`binUp`** of 128 units or more: `binDown`, plus one if any bit below the top eight is set. -/
theorem binUp_big {x : Nat} (h1 : 128 ≤ x) :
    binUp x = binDown x + (if (min x 33554432) % 2 ^ (Nat.log2 (min x 33554432) - 7) = 0 then 0 else 1) := by
  rw [binDown_big h1]
  unfold binUp toBin
  rw [maxSize_val]
  generalize hy : min x 33554432 = y
  have hy1 : 128 ≤ y := by omega
  have hy0 : y ≠ 0 := by omega
  have hl : 7 ≤ Nat.log2 y := (Nat.le_log2 hy0).mpr (by simpa using hy1)
  simp only [hy0, ↓reduceIte, mantissaBits, show ¬ y < 2 ^ 7 by simp; omega, log2, Bool.true_and]
  rw [show (2 : Nat) ^ 7 = 128 by rfl, show Nat.log2 y - 6 = Nat.log2 y - 7 + 1 by omega]
  have hm := Nat.mod_lt (y / 2 ^ (Nat.log2 y - 7)) (show 0 < 128 by decide)
  split <;> split <;> simp_all <;> omega

/-- **41177 … 41217**: the frame, the alignment's one set bit, and the heap's base in ω₁₁. -/
theorem al_pro {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp k base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792)
    (h8 : ω[8] = UInt64.ofNat (2 ^ k)) (hk : k < 32)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb : rdN μ 206520 8 = base) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41177 ω μ x 41217 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[11] = UInt64.ofNat base ∧ ω'[12] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 40) 8 = Num.encodeLE 8 ω[10].toNat ∧
      rdN μ' (sp - 32) 8 = 204984 ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [1, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  have hb64 : base < 18446744073709551616 := by rw [← hb]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, popcount_pow hk, hb, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rw [rdN_frame (μ := μ) (a := 206520) (n := 8) (fun j hj => by rd_simp []), hb]
    · rw [show sp - 8 = sp - 152 + 144 by omega]; rd_simp []; rfl
    · rw [show sp - 16 = sp - 152 + 136 by omega]; rd_simp []; rfl
    · rw [show sp - 24 = sp - 152 + 128 by omega]; rd_simp []; rfl
    · rw [show sp - 40 = sp - 152 + 112 by omega]; rd_simp []; rfl
    · rw [show sp - 32 = sp - 152 + 120 by omega]; rd_simp []; simp [Num.decodeLE]
    · rd_simp []
    · rd_simp [hwr]

/-- 41217: the heap is in use (base ≠ 0), to 41221. -/
theorem al_br_used {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (base : Nat) (h11 : ω[11] = UInt64.ofNat base) (hb0 : base ≠ 0) (hb1 : base < 18446744073709551616) :
    FreeStepsH p R 41217 ω μ x 41221 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11, hb0, Nat.mod_eq_of_lt hb1]

/-- 41217: the first use (base = 0), to the call of `initialize` at 42131. -/
theorem al_br_init {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h11 : ω[11] = UInt64.ofNat 0) :
    FreeStepsH p R 41217 ω μ x 42131 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h11]

/-- **41221 … 41297**, a minimum size `req + align` below 128 units: both bins are `minSize − 1`. -/
theorem al_bin_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req al : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat 1) (hal : 1 ≤ al) (hs : req + al < 128) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41297 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat (req + al - 1) ∧ ω'[2] = UInt64.ofNat (req + al - 1) ∧
      ω'[12] = UInt64.ofNat (req + al) ∧ ω'[4] = UInt64.ofNat (req + 1) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 4, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, h8, h12]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **41221 … 41297**, a minimum size `req + align` of 128 … 2²⁵ units: ω₀ its bin rounded down,
    ω₂ rounded up. -/
theorem al_bin_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (req al : Nat) (h9 : ω[9] = UInt64.ofNat req) (h8 : ω[8] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat 1) (hal : 1 ≤ al) (hal1 : al < 4294967296) (hs : 128 ≤ req + al)
    (hs1 : req + al ≤ 33554432) :
    ∃ ω', FreeStepsH p R 41221 ω μ x 41297 ω' μ x 30 ∧
      ω'[0] = UInt64.ofNat (binDown (req + al)) ∧ ω'[2] = UInt64.ofNat (binUp (req + al)) ∧
      ω'[4] = UInt64.ofNat (req + 1) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h9, h8, h12]
  case post =>
    have hy0 : req + al ≠ 0 := by omega
    have hL1 : 7 ≤ Nat.log2 (req + al) := (Nat.le_log2 hy0).mpr (by simpa using hs)
    have hL2 : Nat.log2 (req + al) < 26 :=
      (Nat.log2_lt hy0).mpr (by simpa using Nat.lt_of_le_of_lt hs1 (by decide))
    have hv : (req + al) / 2 ^ (Nat.log2 (req + al) - 7) < 256 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have := Nat.lt_log2_self (n := req + al)
      calc req + al < 2 ^ (Nat.log2 (req + al) + 1) := this
        _ = 256 * 2 ^ (Nat.log2 (req + al) - 7) := by
          rw [show Nat.log2 (req + al) + 1 = 8 + (Nat.log2 (req + al) - 7) by omega, Nat.pow_add]
    have ht : 2 ^ (Nat.log2 (req + al) - 7) ≤ 262144 :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega : Nat.log2 (req + al) - 7 ≤ 18)) (by decide)
    have ht1 : 1 ≤ 2 ^ (Nat.log2 (req + al) - 7) := Nat.one_le_two_pow
    have hmin : min (req + al) 33554432 = req + al := by omega
    rw [binUp_big hs, binDown_big hs, hmin]
    rw [clz32 hy0 (by omega)]
    rw [show (18446744073709551640 - (31 - Nat.log2 (req + al)) % 18446744073709551616) % 18446744073709551616 % 32 =
      Nat.log2 (req + al) - 7 by omega]
    have hmask : (18446744073709551615 * 2 ^ (Nat.log2 (req + al) - 7) % 4294967296 +
        18446744073709551615 * 2 ^ (Nat.log2 (req + al) - 7) % 4294967296 / 2147483648 * 18446744069414584320) %
          18446744073709551616 = 18446744073709551616 - 2 ^ (Nat.log2 (req + al) - 7) := by
      have key : ∀ t : Nat, 1 ≤ t → t ≤ 262144 → (18446744073709551615 * t % 4294967296 +
          18446744073709551615 * t % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616 =
          18446744073709551616 - t := fun t h1 h2 => by
        have e1 : 18446744073709551615 * t % 4294967296 = 4294967296 - t := by
          rw [Nat.mul_mod]; rw [show 18446744073709551615 % 4294967296 = 4294967295 from rfl]; omega
        rw [e1, show (4294967296 - t) / 2147483648 = 1 by omega]; omega
      exact key _ ht1 ht
    have hlow := andInv_low (a := req + al) (s := Nat.log2 (req + al) - 7) (by omega)
    rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at hlow
    have hlt : (req + al) % 2 ^ (Nat.log2 (req + al) - 7) < 2 ^ 18 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
    generalize (req + al) / 2 ^ (Nat.log2 (req + al) - 7) = v at *
    refine ⟨?_, ?_, by reg_val, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
      refine congrArg UInt64.ofNat ?_
      simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
        bitwise_and_m127]
      omega
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
      refine congrArg UInt64.ofNat ?_
      simp only [show v % 4294967296 = v by omega, show v / 2147483648 = 0 by omega, Nat.zero_mul, Nat.add_zero,
        bitwise_and_m127, hmask, hlow]
      split <;> split <;> omega

end Services.Bootstrap.Alloc
