import Services.Bootstrap.Encode.Dispatch

/-!
# `Instruction::encode_to`: the arms' straight-line pieces, one theorem each

Each piece of a fixed-width variant's arm, from its start to the call of
`Vec<u8>::extend_from_slice` (58508): the tag pieces (`tagSeg_e`) put the tag octet in the scratch word
at sp + 24; the field pieces (`fieldSeg_e`) load a field of 1, 4 or 8 octets from the value into it; the
direct pieces (`directSeg_e`) point the call at octets of the value. `Encode.Fixed` gathers them
(`tagSeg`, `fieldSeg`, `directSeg`). They are separate theorems to keep each elaboration small.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem tagSeg_18890 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18890 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 792 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 3] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_19088 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19088 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 816 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 20] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_18369 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18369 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 746 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 4] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_18925 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18925 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 798 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_18778 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18778 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 780 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 2] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_19789 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19789 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 876 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 8] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_19256 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19256 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 830 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 21] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_19474 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19474 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 850 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 6] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem tagSeg_18919 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18919 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 850 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 7] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

theorem fieldSeg_18913 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 8 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18913 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 8) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 8) 4)) = μ.readN (S + 8) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
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

theorem fieldSeg_19111 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 8 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19111 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 8) 4)) = μ.readN (S + 8) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_19515 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 40 ≤ a → a < S + 40 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19515 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 40) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 40) 4)) = μ.readN (S + 40) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_18392 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 40 ≤ a → a < S + 40 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18392 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 748 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 40) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 40) 4)) = μ.readN (S + 40) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
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

theorem fieldSeg_18963 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 40 ≤ a → a < S + 40 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18963 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 802 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 40) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 40) 4)) = μ.readN (S + 40) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_18984 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 48 ≤ a → a < S + 48 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18984 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 48) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 48) 4)) = μ.readN (S + 48) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_18801 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 152 ≤ a → a < S + 152 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18801 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 782 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 152) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 152) 4)) = μ.readN (S + 152) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
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

theorem fieldSeg_18823 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 136 ≤ a → a < S + 136 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18823 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 784 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 136) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 136) 4)) = μ.readN (S + 136) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_18845 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 144 ≤ a → a < S + 144 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18845 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 786 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 144) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 144) 4)) = μ.readN (S + 144) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_19812 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 8 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19812 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 878 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 8) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 8) 4)) = μ.readN (S + 8) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
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

theorem fieldSeg_19848 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 44 ≤ a → a < S + 44 + 1 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19848 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = μ.readN (S + 44) 1 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 1 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 44) 4)) = μ.readN (S + 44) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [hm1, encodeLE_mod, encodeLE_rdN])

theorem fieldSeg_19279 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 8 ≤ a → a < S + 8 + 8 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19279 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 832 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 8) 4)) = μ.readN (S + 8) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem fieldSeg_19300 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 16 ≤ a → a < S + 16 + 1 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19300 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = μ.readN (S + 16) 1 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 1 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 16) 4)) = μ.readN (S + 16) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  have hm1 : ∀ w : Nat, w % 18446744073709551616 % 256 = w % 256 ^ 1 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hr, hw, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [hm1, encodeLE_mod, encodeLE_rdN])

theorem directSeg_19500 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v S : Nat) (hS : S + 232 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 19500 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 852 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]
    all_goals try (congr 1; omega)

theorem directSeg_18413 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v S : Nat) (hS : S + 232 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 18413 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]
    all_goals try (congr 1; omega)

theorem directSeg_18948 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v S : Nat) (hS : S + 232 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 18948 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 800 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]
    all_goals try (congr 1; omega)

theorem directSeg_19833 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v S : Nat) (hS : S + 232 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 19833 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 880 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + 12) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]
    all_goals try (congr 1; omega)

theorem directSeg_18867 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v S : Nat) (hS : S + 232 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 18867 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6]
    all_goals try (congr 1; omega)

end Services.Bootstrap.Encode.Enc
