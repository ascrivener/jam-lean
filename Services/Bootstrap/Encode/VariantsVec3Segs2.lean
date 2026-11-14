import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `Assign` (12) and `Designate` (13)

* `Assign`'s arm (18429 … 18516, 18752 … 18774): the tag 12, the `u16` core at S + 36, S parked at sp,
  then the queue's n = (S + 24) hashes from q (S + 16), 32 octets each straight from the heap, counted
  down in ω₅ = 32 i; then the `u32` assigner at S + 32 (its call returns to 20383, the function's end).
  No length prefix: the queue is a fixed-length sequence (GP v0.8.0 Appendix C).
* `Designate`'s arm (19322 … 19471): the tag 13, the `Vec`'s length n (S + 24, checked against 2^32:
  the code traps at 20397 otherwise) and its length prefix, then a loop over the n 336-octet keys from
  q (S + 16), each appended in four calls straight from the heap: its octets 128 … 160, 160 … 192,
  192 … 336 and 0 … 128 (the paper's order of a key whose in-memory layout is rotated); the octets
  left 336 i at sp + 8 and the next key at sp. The end is 20118.

One theorem per piece, proved by symbolic execution (`pvm_go`), as in `Encode.VecSegs`.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-! ## `Assign` -/

/-- 18452 … 18466 (`Assign`): the `u16` core at S + 36 (ω₅ = S) to sp + 24 and the call appending its
    2 octets (return 754 → 18473), the writer from ω₆. -/
theorem seg_18452 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (hr : ∀ a, S + 36 ≤ a → a < S + 36 + 2 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 2 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18452 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 754 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (sp + 24) 2 = μ.readN (S + 36) 2 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 2 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 2 (sxw 2 (rdN μ (S + 36) 2)) = μ.readN (S + 36) 2 := by
    rw [encodeLE_sxw 2 _ (Or.inl rfl) (rdN_lt μ _ 2), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 65536 = w % 256 ^ 2 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 18473 … 18478 (`Assign`, an empty queue): S parked at sp; the length (S + 24) is 0: on to 18752. -/
theorem seg_18473_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 32 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 0)
    (hrS : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 8 → μ.writable a = true) (hSs : S + 32 ≤ sp ∨ sp + 8 ≤ S + 24) :
    ∃ ω' μ', FreeStepsH p R 18473 ω μ x 18752 ω' μ' x 3 ∧
      ω'[1] = ω[1] ∧ μ'.readN sp 8 = Num.encodeLE 8 S ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r24 := rd8 (by decide) s24
  have r24' : rdN (μ.writeN sp (Num.encodeLE 8 S)) (S + 24) 8 = 0 := by
    rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]; exact r24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hw, hrS, r24, r24', ↓rdN_fold]
  · refine ⟨?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5,
      Nat.mod_eq_of_lt (show S < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption

/-- 18473 … 18491 (`Assign`, n > 0 hashes): S parked at sp; the length n (S + 24) is not 0; ω₈ = q
    (S + 16), ω₅ = 32 n; on to the loop at 18492. -/
theorem seg_18473_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 32 ≤ 4294967296)
    (hq : q < 18446744073709551616) (hn : 0 < n ∧ 32 * n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 8 → μ.writable a = true) (hSs : S + 32 ≤ sp ∨ sp + 8 ≤ S + 16) :
    ∃ ω' μ', FreeStepsH p R 18473 ω μ x 18492 ω' μ' x 8 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * n) ∧ ω'[8] = UInt64.ofNat q ∧
      μ'.readN sp 8 = Num.encodeLE 8 S ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r24 := rd8 (by omega) s24
  have r16 := rd8 hq s16
  have hS64 : S < 18446744073709551616 := by omega
  have r24' : rdN (μ.writeN sp (Num.encodeLE 8 S)) (S + 24) 8 = n := by
    rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]; exact r24
  have r16' : rdN (μ.writeN sp (Num.encodeLE 8 S)) (S + 16) 8 = q := by
    rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]; exact r16
  have r0 : rdN (μ.writeN sp (Num.encodeLE 8 S)) sp 8 = S := by
    show Num.decodeLE _ = _
    rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE]
    exact Nat.mod_eq_of_lt hS64
  have hn0 : ¬ n = 0 := by omega
  have hsh : n <<< 5 % 18446744073709551616 = 32 * n := by rw [Nat.shiftLeft_eq]; omega
  have hr : ∀ a, sp ≤ a → a < sp + 8 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hw, hr, hrS, r24', r16', r0, hn0, hsh, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hS64,
      Nat.mod_eq_of_lt hq]
    post_simp
    all_goals try assumption

/-- 18492 … 18501 (`Assign`, one hash at a = ω₈): ω₆ = a + 32 and the call appending the 32 octets at a
    (return 756 → 18508), the writer from sp + 16. -/
theorem seg_18492 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (ha : a + 32 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat a)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ b, sp + 16 ≤ b → b < sp + 24 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 18492 ω μ x 58508 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 756 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat (a + 32) ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat a ∧ ω'[9] = UInt64.ofNat 32 := by
  have rv := rd8 hv v16
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h8, hsp, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h8, Nat.mod_eq_of_lt hv]
    all_goals try (congr 1; omega)

/-- 18508 … 18513 (`Assign`, after a hash, more left): ω₅ = 32 i less 32 is not 0; ω₈ = ω₆; back to
    18492. -/
theorem seg_18508_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (i b : Nat) (hi : 2 ≤ i ∧ 32 * i < 18446744073709551616) (hb : b < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat (32 * i)) (h6 : ω[6] = UInt64.ofNat b) :
    ∃ ω', FreeStepsH p R 18508 ω μ x 18492 ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * (i - 1)) ∧ ω'[8] = UInt64.ofNat b := by
  have hne : ¬ (32 * i + 18446744073709551584) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hne]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hb]
    all_goals try (congr 1; omega)

/-- 18508 … 18516 (`Assign`, after the last hash): ω₅ = 32 less 32 is 0; on to 18752. -/
theorem seg_18508_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 32) :
    ∃ ω', FreeStepsH p R 18508 ω μ x 18752 ω' μ x 4 ∧ ω'[1] = ω[1] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']

/-- 18752 … 18774 (`Assign`, the assigner): S from sp, the `u32` at S + 32 to sp + 24 and the call
    appending its 4 octets (return 918 → 20383), the writer from sp + 16. -/
theorem seg_18752 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, S + 32 ≤ a → a < S + 32 + 4 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18752 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 918 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 32) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 32) 4)) = μ.readN (S + 32) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have rv := rd8 hv v16
  have hrs : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hr, hw, hrs, r0, rv, ↓rdN_fold, ↓loadI_fold, rdN_mod64, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

end Services.Bootstrap.Encode.Enc
