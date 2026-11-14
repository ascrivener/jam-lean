import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `AssignForGasCost` (dispatch index 24)

`AssignForGasCost { core: u16, queue: Vec<Hash>, assigner: u32 }` (arm 18639 … 18774): the tag octet
24, the core's 2 octets (S + 36), the queue's count ℰ(n) (S + 16, S + 24), a loop (18722 … 18749)
appending each 32-octet hash straight from the heap, the assigner's 4 octets (S + 32), and the end
20383. S is parked at sp. The code traps (20397) on a length of 2^32 or more.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 18639 … 18655 (`AssignForGasCost`, tag 24): the tag octet at sp + 24, S (ω₁₁) to sp, and the call
    for the tag (return 770 → 18662), with the writer v (ω₁₀) in ω₅. -/
theorem seg_18639 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18639 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 770 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 24] ∧ μ'.readN sp 8 = Num.encodeLE 8 S ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 8 ≤ a) → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 18662 … 18678 (`AssignForGasCost`): the core's 2 octets at S + 36 (S from sp) to sp + 24 and the
    call for them (return 772 → 18685), the writer from ω₅. -/
theorem seg_18662 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S)
    (hr : ∀ a, S + 36 ≤ a → a < S + 36 + 2 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18662 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 772 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (sp + 24) 2 = μ.readN (S + 36) 2 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 2 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsx : Num.encodeLE 2 (sxw 2 (rdN μ (S + 36) 2)) = μ.readN (S + 36) 2 := by
    rw [encodeLE_sxw 2 _ (Or.inl rfl) (rdN_lt μ _ 2), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 65536 = w % 256 ^ 2 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hr, hw, hr', r0, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])

/-- 18685 … 18709 (`AssignForGasCost`): the queue's length n < 2^32 (S + 24, S from sp) as a 32-bit word
    to sp + 24 and its pointer q (S + 16) in ω₆; the call of the length prefix with ω₇ = sp + 24, the
    writer (from sp + 16) in ω₈, n in ω₅ (return 774 → 18715). -/
theorem seg_18685 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18685 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 774 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hw, hr', hrS, r0, r16, r24, rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 18715 (`AssignForGasCost`, no hashes): n = 0, on to the assigner at 18752. -/
theorem seg_18715_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 18715 ω μ x 18752 ω' μ x 1 ∧ ω' = ω := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · rfl

/-- 18715 … 18721 (`AssignForGasCost`, n > 0 hashes): ω₅ = 32 n, the octets of the hashes left; on to
    the loop at 18722. -/
theorem seg_18715_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (n : Nat) (hn : 0 < n ∧ n < 4294967296) (h5 : ω[5] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 18715 ω μ x 18722 ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * n) ∧ ω'[6] = ω[6] := by
  have hn0 : ¬ n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, hn0]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]
    all_goals try (congr 1; omega)

/-- 18722 … 18736 (`AssignForGasCost`, one hash): ω₆ = s the hash's address; s + 32 to sp + 8 and the
    call appending the 32 octets at s, the writer from sp + 16 (return 776 → 18743). -/
theorem seg_18722 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v s : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hs : s + 32 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat s)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hw : ∀ b, sp + 8 ≤ b → b < sp + 24 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 18722 ω μ x 58508 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 776 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat s ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 (s + 32) ∧
      (∀ b, b < 4294967296 → (b < sp + 8 ∨ sp + 16 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have rv := rd8 hv v16
  have hr : ∀ b, sp + 8 ≤ b → b < sp + 24 → μ.readable b = true :=
    fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hsp, hw, hr, rv, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (show s < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption

/-- 18743 … 18749 (`AssignForGasCost`, after a hash, more left): the octets left r ≥ 64 less 32, ω₆ the
    next hash's address (from sp + 8); back to 18722. -/
theorem seg_18743_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp s r : Nat) (hsp : sp + 32 ≤ 4294967296) (hs : s < 18446744073709551616)
    (hr : 64 ≤ r ∧ r < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat r)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 s)
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 18743 ω μ x 18722 ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (r - 32) ∧ ω'[6] = UInt64.ofNat s := by
  have r8 := rd8 hs s8
  have hne : ¬ (r + 18446744073709551584) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hrd, r8, hne, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hs]
    all_goals try (congr 1; omega)

/-- 18743 … 18749 (`AssignForGasCost`, after the last hash): r = 32, on to the assigner at 18752. -/
theorem seg_18743_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp s : Nat) (hsp : sp + 32 ≤ 4294967296) (hs : s < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 32)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 s)
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 18743 ω μ x 18752 ω' μ x 3 ∧ ω'[1] = ω[1] := by
  have r8 := rd8 hs s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hrd, r8, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 18752 … 18774 (`AssignForGasCost`): the assigner's 4 octets at S + 32 (S from sp) to sp + 24 and the
    call for them (return 918 → 20383), the writer from sp + 16. -/
theorem seg_18752 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
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
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 32) 4)) = μ.readN (S + 32) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hr, hw, hr', r0, rv, ↓rdN_fold, ↓loadI_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [← hsx, hm, encodeLE_mod])
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])

end Services.Bootstrap.Encode.Enc
