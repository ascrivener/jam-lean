import Services.Bootstrap.Acc.Wrappers.ReadHost
import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The SDK's `get` (47857): a value of this service's storage

`get(key)` (the SDK's storage read) reads in two phases, as `fetch_vec` does (GP v0.8.0 Appendix B,
Ω_R):
- `read` (4) with an empty buffer gives the value's length L, or NONE;
- NONE stores `None` (−1) at out; L = 0 stores the empty `Vec { 0, 1, 0 }`;
- otherwise a zeroed block of ⌈L/32⌉ units is allocated under the allocator's lock (41177, return
  2132 → 48047), a second `read` writes the value into it, and `Some(Vec { L, ptr, L })` is stored
  at out.
The frame is 48 octets (s = sp − 48): ω₀, ω₅, ω₆ at s + 40, + 32, + 24, out at s + 16, the key's
length at s + 8. The key's address stays in ω₅.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **47857 … 47886**: the frame s = sp − 48 (ω₀, ω₅, ω₆, out = ω₇ and the key's length ω₉ saved),
    ω₅ = the key's address ω₈, and the first `read`'s registers: ω₇ = NONE, ω₁₀ = ω₁₁ = ω₁₂ = 0. -/
theorem gr_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47857 ω μ x 47886 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat (sp - 48) ∧ ω'[5] = ω[8] ∧ ω'[7] = UInt64.ofNat 18446744073709551615 ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat 0 ∧ ω'[12] = UInt64.ofNat 0 ∧
      rdN μ' (sp - 48 + 40) 8 = ω[0].toNat ∧ rdN μ' (sp - 48 + 32) 8 = ω[5].toNat ∧
      rdN μ' (sp - 48 + 24) 8 = ω[6].toNat ∧ rdN μ' (sp - 48 + 16) 8 = ω[7].toNat ∧
      rdN μ' (sp - 48 + 8) 8 = ω[9].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 48 + 8 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [1, 5, 7, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 48 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> rfl), by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **47888 … 47927**, NONE: `None` (the niche −1 in the capacity word) stored at out, ω₀, ω₅, ω₆
    restored and the frame popped, at the return's `jumpInd`. -/
theorem gr_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 48 < 4294967296) (hout : 65536 ≤ out ∧ out + 8 < 4294967296)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 out)
    (m24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 r6) (m32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r5)
    (m40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 48 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 8 → μ.writable a = true) (dos : out + 8 ≤ sp ∨ sp + 48 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 47888 ω μ x 47927 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 48) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 8 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, m16, m24, m32, m40, hrf, hwo, hro]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, h7, PVM.Memory.readN_writeN_disjoint, m24, m32, m40]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same]; decide)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **47888 … 47957**, an empty value: `Some(Vec { 0, 1, 0 })` (capacity 0, the dangling pointer 1,
    length 0) stored at out, ω₀, ω₅, ω₆ restored and the frame popped, at the return's `jumpInd`. -/
theorem gr_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat 0)
    (hsp : 65536 ≤ sp ∧ sp + 48 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 out)
    (m24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 r6) (m32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r5)
    (m40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 48 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) (dos : out + 24 ≤ sp ∨ sp + 48 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 47888 ω μ x 47957 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 48) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 0 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, m16, m24, m32, m40, hrf, hwo, hro]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, h7, PVM.Memory.readN_writeN_disjoint, m24, m32, m40]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; decide)
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; rfl)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **47888 … 47974**, a value of length 0 < L < 2⁶³: L moved to ω₆, ω₇ = 2³⁷ − 32 (picoalloc's
    largest request) for the size check at 47974; ω₀ = 2130. -/
theorem gr_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (L : Nat) (h7 : ω[7] = UInt64.ofNat L) (hL0 : 0 < L) (hL : L < 9223372036854775808) :
    ∃ ω', FreeStepsH p R 47888 ω μ x 47974 ω' μ x 10 ∧
      ω'[6] = UInt64.ofNat L ∧ ω'[7] = UInt64.ofNat 137438953440 ∧ ω'[0] = UInt64.ofNat 2130 ∧
      ∀ j : Fin 13, j.val ∉ [0, 6, 7] → ω'[j] = ω[j] := by
  have hm : L % 18446744073709551616 = L := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h7, hm]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- **47974 … 41177**, 0 < L, L + 31 < 2³⁶ (so ⌈L/32⌉ < 2³¹ survives the 32-bit add): the allocator's lock taken (the word at 206848, the scratch at
    196608 … 196616 used), 196792 saved at sp, and the call of `alloc_impl` for ⌈L/32⌉ units of
    alignment 1 with the zero flag set: ω₇ = 196792, ω₈ = 1, ω₉ = ⌈L/32⌉, ω₁₀ = 1, return address
    2132. -/
theorem gr_lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat L)
    (h7 : ω[7] = UInt64.ofNat 137438953440) (hL : L + 31 < 68719476736)
    (hsp : 65536 ≤ sp ∧ sp + 8 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 8 → μ.writable a = true)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (dsp : 206852 ≤ sp) :
    ∃ ω' μ', FreeStepsH p R 47974 ω μ x 41177 ω' μ' x 30 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat ((L + 31) / 32) ∧ ω'[10] = UInt64.ofNat 1 ∧ ω'[0] = UInt64.ofNat 2132 ∧
      ω'[6] = ω[6] ∧ ω'[5] = ω[5] ∧ ω'[1] = ω[1] ∧ ω'[4] = ω[4] ∧
      μ'.readN sp 8 = Num.encodeLE 8 196792 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → (a < sp ∨ sp + 8 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 4, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hrf : ∀ a, sp ≤ a → a < sp + 8 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, hand, show 137438953440 ≥ L by omega, hwr, hr, hwf, hrf, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_,
      ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same]; decide
    · rd_simp []
    · rd_simp [hwr]
    · rd_simp [hwr]

/-- **48047 … 48077**, after `alloc_impl` returned a block `ptr` ≠ 0: the allocator's lock byte
    (206848) cleared, and the second `read`'s registers: ω₇ = NONE (this service), the key at ω₈ = ω₅
    (ω₉ = its length, from sp + 8), the buffer ω₁₀ = ptr, offset ω₁₁ = 0, length ω₁₂ = L; ptr also in
    ω₅. -/
theorem gr_unlock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr kZ : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296) (hkZ : kZ < 18446744073709551616)
    (hsp : 65536 ≤ sp ∧ sp + 16 < 4294967296)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 196792) (m8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 kZ)
    (hrf : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true) (hwl : μ.writable 206848 = true)
    (dl : 206848 < sp) :
    ∃ ω' μ', FreeStepsH p R 48047 ω μ x 48077 ω' μ' x 20 ∧
      ω'[7] = UInt64.ofNat 18446744073709551615 ∧ ω'[8] = ω[5] ∧ ω'[9] = UInt64.ofNat kZ ∧
      ω'[10] = UInt64.ofNat ptr ∧ ω'[11] = UInt64.ofNat 0 ∧ ω'[12] = ω[6] ∧ ω'[5] = UInt64.ofNat ptr ∧
      μ' = μ.writeN 206848 [0] ∧
      ∀ j : Fin 13, j.val ∉ [5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  have r0 : rdN μ sp 8 = 196792 := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]
  have r8 : rdN μ (sp + 8) 8 = kZ := by
    unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hkZ
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, r0, r8, hrf, hwl, hrl, hp0', Nat.mod_eq_of_lt hkZ, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> rfl), (by reg_val), by reg_val, by reg_val,
      (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_val, rfl, by reg_frame⟩

/-- **48079 … 48102**, after the second `read`: `Some(Vec { L, ptr, L })` stored at out (from sp + 16),
    ω₀, ω₅, ω₆ restored and the frame popped, at the return's `jumpInd`. -/
theorem gr_store {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out ptr L r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h5 : ω[5] = UInt64.ofNat ptr) (h6 : ω[6] = UInt64.ofNat L)
    (hL : L < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (hsp : 65536 ≤ sp ∧ sp + 48 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (m16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 out)
    (m24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 r6) (m32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r5)
    (m40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 48 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) (dos : out + 24 ≤ sp ∨ sp + 48 ≤ out)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω' μ', FreeStepsH p R 48079 ω μ x 48102 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 48) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN out 8 = Num.encodeLE 8 L ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, m16, m24, m32, m40, hrf, hwo, hro, Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hptr]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', Option.getD_none, h1, PVM.Memory.readN_writeN_disjoint, m24, m32, m40]
    all_goals try rw [Nat.mod_eq_of_lt (by assumption)]
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]; done)
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

end Services.Bootstrap.Acc
