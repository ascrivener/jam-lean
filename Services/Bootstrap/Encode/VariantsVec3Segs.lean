import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `Bless` (11)'s arm

`Bless`'s arm (18163 … 18366): the tag 11, the four `u32`s at S + 32, S + 36, S + 40, S + 44 (each
loaded into the scratch word sp + 24 and appended), the `Vec<(u32, u64)>`'s length n (S + 24, checked
against 2^32: the code traps at 20397 otherwise) and its length prefix, then a loop over the n 16-octet
elements from q (S + 16) to q + 16 n (kept at sp + 8), appending each element's `u32` (at + 0) and
`u64` (at + 8) through the scratch word; the end is the function's end at 20118. One theorem per piece,
proved by symbolic execution (`pvm_go`), as in `Encode.VecSegs`.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 18163 … 18179 (`Bless`, tag 11), 18429 … 18445 (`Assign`, tag 12): the tag octet at sp + 24 and
    the call for it (return r), with S (ω₁₁) in ω₅ and the writer v (ω₁₀) in ω₆. -/
theorem seg_tagB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e tag r sp v S : Nat) (he : (e = 18163 ∧ tag = 11 ∧ r = 728) ∨ (e = 18429 ∧ tag = 12 ∧ r = 752))
    (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat tag] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h10, h11, hsp, hw]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
        Nat.mod_eq_of_lt hS]
      post_simp
      all_goals try assumption

/-- 18186 … 18263 (`Bless`'s four `u32`s): from e, the `u32` at S + off (ω₅ = S) to sp + 24 and the call
    appending its 4 octets with return address r, the writer from ω₆. -/
theorem seg_u32B {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e r off sp v S : Nat)
    (he : (e = 18186 ∧ r = 730 ∧ off = 32) ∨ (e = 18207 ∧ r = 732 ∧ off = 36) ∨
      (e = 18228 ∧ r = 734 ∧ off = 40) ∨ (e = 18249 ∧ r = 736 ∧ off = 44))
    (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ a, S + off ≤ a → a < S + off + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + off) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + off) 4)) = μ.readN (S + off) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
      post_simp
      all_goals try assumption
      all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 18270 … 18292 (`Bless`): the `Vec`'s length n < 2^32 (S + 24) as a 32-bit word to sp + 24 and its
    pointer q (S + 16) in ω₅; the call of the length prefix with ω₇ = sp + 24, the writer (from
    sp + 16) in ω₈ and n in ω₆ (return 738 → 18298). -/
theorem seg_18270 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18270 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 738 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have rv := rd8 hv v16
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hw, hr, hrS, r16, r24, rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 18298 (`Bless`, no elements): n = 0, on to the end at 20118. -/
theorem seg_18298_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h6 : ω[6] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 18298 ω μ x 20118 ω' μ x 1 ∧ ω' = ω := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h6]
  · rfl

/-- 18298 … 18314 (`Bless`, n > 0 elements): the end q + 16 n of the elements to sp + 8, the writer
    (from sp + 16) in ω₆, ω₅ = q; on to the loop at 18315. -/
theorem seg_18298_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hq : q + 16 * n < 18446744073709551616) (hn : 0 < n)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat q) (h6 : ω[6] = UInt64.ofNat n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hw : ∀ a, sp + 8 ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18298 ω μ x 18315 ω' μ' x 7 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[6] = UInt64.ofNat v ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 (q + 16 * n) ∧
      (∀ a, a < 4294967296 → (a < sp + 8 ∨ sp + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv := rd8 hv v16
  have hn0 : ¬ n = 0 := by omega
  have hr : ∀ a, sp + 8 ≤ a → a < sp + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsh : n <<< 4 % 18446744073709551616 = 16 * n := by
    rw [Nat.shiftLeft_eq]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hw, hr, rv, hn0, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show q < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption

/-- 18315 … 18329 (`Bless`, one element at a = ω₅): the element's `u32` (at a) to sp + 24 and the call
    appending its 4 octets (return 740 → 18336), the writer from ω₆. -/
theorem seg_18315 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a : Nat) (hsp : sp + 32 ≤ 4294967296) (ha : a + 4 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ b, a ≤ b → b < a + 4 → μ.readable b = true)
    (hw : ∀ b, sp + 24 ≤ b → b < sp + 24 + 4 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 18315 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 740 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN a 4 ∧
      (∀ b, b < 4294967296 → (b < sp + 24 ∨ sp + 24 + 4 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ a 4)) = μ.readN a 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, ha, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 18336 … 18350 (`Bless`, one element at a = ω₅): the element's `u64` (at a + 8) to sp + 24 and the
    call appending its 8 octets (return 742 → 18357), the writer from ω₆. -/
theorem seg_18336 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a : Nat) (hsp : sp + 32 ≤ 4294967296) (ha : a + 16 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ b, a + 8 ≤ b → b < a + 16 → μ.readable b = true)
    (hw : ∀ b, sp + 24 ≤ b → b < sp + 24 + 8 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 18336 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 742 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (a + 8) 8 ∧
      (∀ b, b < 4294967296 → (b < sp + 24 ∨ sp + 24 + 8 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, ha, hr, hw, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

/-- 18357 … 18363 (`Bless`, after an element at a, more left): ω₅ = a + 16 is not the end (sp + 8); back
    to 18315. -/
theorem seg_18357_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp a z : Nat) (hsp : sp + 32 ≤ 4294967296) (ha : a + 16 < 18446744073709551616)
    (hz : z < 18446744073709551616) (hne : a + 16 ≠ z)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 z)
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 18357 ω μ x 18315 ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (a + 16) ∧ ω'[6] = ω[6] := by
  have r8 := rd8 hz s8
  have hne' : ¬ (a + 16) % 18446744073709551616 = z := by rw [Nat.mod_eq_of_lt ha]; exact hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hrd, r8, hne', ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    all_goals try (congr 1; omega)

/-- 18357 … 18366 (`Bless`, after the last element at a): ω₅ = a + 16 is the end (sp + 8); on to the
    end at 20118. -/
theorem seg_18357_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp a : Nat) (hsp : sp + 32 ≤ 4294967296) (ha : a + 16 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 (a + 16))
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 18357 ω μ x 20118 ω' μ x 4 ∧ ω'[1] = ω[1] := by
  have r8 := rd8 ha s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hrd, r8, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Encode.Enc
