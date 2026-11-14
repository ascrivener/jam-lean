import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the pieces of `CreateService`'s arm (17905 … 18135, 20218 … 20322)

One theorem per piece from one call to the next (see `Encode.VariantsVec2CSSegs` for the arm's
outline). S is parked at sp by the first piece and reloaded from there; the writer is reloaded from
sp + 16 (where the dispatch saved it) or kept in ω₅ after the `Option<Vec<u8>>`'s tag.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 17905 … 17918 (`CreateService`, tag 0): the tag octet at sp + 24, S (ω₁₁) to sp, and the call for
    the tag (return 704 → 17925), the writer v (ω₁₀) in ω₇; ω₅, ω₆ kept. -/
theorem seg_17905 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17905 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 704 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧ μ'.readN sp 8 = Num.encodeLE 8 S ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 8 ≤ a) → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- The pieces of `CreateService`'s arm that call `extend_from_slice` for n octets straight from the
    value at S + off (S from sp, the writer from sp + 16): the piece's start e and its return r. -/
def CSDirect (e r off n : Nat) : Prop :=
  (e = 17925 ∧ r = 706 ∧ off = 32 ∧ n = 32) ∨ (e = 18039 ∧ r = 716 ∧ off = 96 ∧ n = 128)

/-- 17925 … 17936 and 18039 … 18051 (`CreateService`): the call appending the n octets at S + off (the
    hash, n = 32 at 32; the array, n = 128 at 96), S from sp, the writer from sp + 16 (return r). -/
theorem seg_csDirect {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e r off n sp v S : Nat) (hc : CSDirect e r off n) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R e ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (S + off) ∧ ω'[9] = UInt64.ofNat n := by
  have r0 := rd8 (by omega) s0
  have rv := rd8 hv v16
  rw [show ω = regsNF ω [] from rfl]
  unfold CSDirect at hc
  rcases hc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hsp, hr, r0, rv, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
      all_goals try (congr 1; omega)

/-- The pieces of `CreateService`'s arm that put the `u64` at S + off into the scratch word: the
    piece's start e and its return r. -/
def CSWord (e r off : Nat) : Prop :=
  (e = 17943 ∧ r = 708 ∧ off = 64) ∨ (e = 17967 ∧ r = 710 ∧ off = 72) ∨ (e = 17991 ∧ r = 712 ∧ off = 80) ∨
    (e = 18015 ∧ r = 714 ∧ off = 88)

/-- 17943 … 18032 (`CreateService`): the `u64` at S + off (S from sp) to sp + 24 and the call for its 8
    octets (return r), the writer from sp + 16; one theorem per piece, `seg_csWord` the four. -/
theorem seg_17943 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 64 ≤ a → a < S + 64 + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17943 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 708 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 64) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hrS, hw, hr', r0, rv, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem seg_17967 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 72 ≤ a → a < S + 72 + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17967 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 710 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 72) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hrS, hw, hr', r0, rv, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem seg_17991 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 80 ≤ a → a < S + 80 + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17991 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 712 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 80) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hrS, hw, hr', r0, rv, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

theorem seg_18015 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 88 ≤ a → a < S + 88 + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18015 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 714 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 88) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have rv := rd8 hv v16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hS, hrS, hw, hr', r0, rv, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

/-- The four `u64` pieces of `CreateService`'s arm (`CSWord`). -/
theorem seg_csWord {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e r off sp v S : Nat) (hc : CSWord e r off) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + off ≤ a → a < S + off + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + off) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  unfold CSWord at hc
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact seg_17943 (p := p) (P := P) (R := R) x ω μ sp v S hsp hS hv h1 s0 v16 hrS hw
  · exact seg_17967 (p := p) (P := P) (R := R) x ω μ sp v S hsp hS hv h1 s0 v16 hrS hw
  · exact seg_17991 (p := p) (P := P) (R := R) x ω μ sp v S hsp hS hv h1 s0 v16 hrS hw
  · exact seg_18015 (p := p) (P := P) (R := R) x ω μ sp v S hsp hS hv h1 s0 v16 hrS hw

/-- 18058, 20218 … 20232 (`CreateService`, `Option<Vec<u8>>` = `None`): the first word ω₆ is the niche
    ω₅ = 2^64 − 1; the octet 0 at sp + 24 and the call for it (return 910 → 20239), the writer (from
    sp + 16) in ω₅ and ω₇. -/
theorem seg_18058_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615)
    (h6 : ω[6] = UInt64.ofNat 18446744073709551615)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18058 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 910 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv := rd8 hv v16
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hw, hr, rv, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])

/-- 18058 … 18077 (`CreateService`, `Option<Vec<u8>>` = `Some(_)`): the first word w (ω₆, the `Vec`'s
    capacity) is not the niche ω₅ = 2^64 − 1; the octet 1 at sp + 24 and the call for it (return 718 →
    18084), the writer (from sp + 16) in ω₅ and ω₇. -/
theorem seg_18058_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v w : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hw64 : w < 18446744073709551615)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat 18446744073709551615) (h6 : ω[6] = UInt64.ofNat w)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18058 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 718 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv := rd8 hv v16
  have hne : ¬ w = 18446744073709551615 := by omega
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 25 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hw, hr, rv, hne, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption
    all_goals try (rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega)
      (by simp [two32] <;> omega), rv])

/-- 18084 … 18111 (`CreateService`, `Some(_)`): S from sp; the `Vec`'s pointer q (S + 8) to sp + 8 and
    its length n < 2^32 (S + 16) as a 32-bit word to sp + 24; the call of the length prefix with ω₇ =
    sp + 24 and the writer (ω₅) in ω₈, n in ω₆ (return 720 → 18117). -/
theorem seg_18084 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 q) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n)
    (hrS : ∀ a, S + 8 ≤ a → a < S + 24 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18084 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 720 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 q ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 8 ∨ sp + 16 ≤ a) → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have r8 := rd8 hq s8
  have r16 := rd8 (by omega) s16
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hw, hr', hrS, r0, r8, r16, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 18117 … 18128 (`CreateService`, `Some(_)`): the call appending the n octets (ω₆) at q (from sp + 8),
    the writer from ω₅ (return 910 → 20239). -/
theorem seg_18117 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hq : q < 18446744073709551616)
    (hv : v < 18446744073709551616) (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat n)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 q)
    (hr : ∀ a, sp + 8 ≤ a → a < sp + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 18117 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 910 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat n := by
  have r8 := rd8 hq s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hsp, hr, r8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hq,
      Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn]
    all_goals try (congr 1; omega)

/-- 20239 … 20256 (`CreateService`): S from sp into ω₆; the `u64` at S + 224 to sp + 24 and the call for
    its 8 octets (return 912 → 20263), the writer from ω₅. -/
theorem seg_20239 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 S)
    (hrS : ∀ a, S + 224 ≤ a → a < S + 224 + 8 → μ.readable a = true)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20239 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 912 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (sp + 24) 8 = μ.readN (S + 224) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have hr' : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hrS, hw, hr', r0, ↓rdN_fold, rdN_mod64]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show S < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try exact encodeLE_rdN μ _ 8

/-- 20263, 20311 … 20322 (`CreateService`, `Option<u32>` = `None`): the tag word at S + 24 (ω₆ = S) is
    0; the octet 0 at sp + 24 and the call for it (return 916 → 20329), the writer from ω₅. -/
theorem seg_20263_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (s24 : rdN μ (S + 24) 4 = 0)
    (hrS : ∀ a, S + 24 ≤ a → a < S + 28 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20263 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 0] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : sxw 4 0 = 0 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hrS, hw, s24, hsx, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 20263 … 20281 (`CreateService`, `Option<u32>` = `Some(_)`): the tag word at S + 24 (ω₆ = S) is 1;
    the octet 1 at sp + 24 and the call for it (return 914 → 20288), the writer from ω₅. -/
theorem seg_20263_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (s24 : rdN μ (S + 24) 4 = 1)
    (hrS : ∀ a, S + 24 ≤ a → a < S + 28 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20263 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 914 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 1] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : sxw 4 1 = 1 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hrS, hw, s24, hsx, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 20288 … 20307 (`CreateService`, `Option<u32>` = `Some(_)`): the 4 octets at S + 28 (ω₆ = S) to
    sp + 24 and the call for them (return 916 → 20329), the writer from ω₅. -/
theorem seg_20288 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hS : S + 232 ≤ 4294967296)
    (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S)
    (hr : ∀ a, S + 28 ≤ a → a < S + 28 + 4 → μ.readable a = true)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 24 + 4 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20288 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 916 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (sp + 24) 4 = μ.readN (S + 28) 4 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 24 + 4 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsx : Num.encodeLE 4 (sxw 4 (rdN μ (S + 28) 4)) = μ.readN (S + 28) 4 := by
    rw [encodeLE_sxw 4 _ (Or.inr rfl) (rdN_lt μ _ 4), encodeLE_rdN]
  have hm : ∀ w : Nat, w % 18446744073709551616 % 4294967296 = w % 256 ^ 4 := fun w => by omega
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

end Services.Bootstrap.Encode.Enc
