import Services.Bootstrap.Refine.DropVecH
import Services.Bootstrap.CodeT1CAll

/-!
# Refine's exit: the single-buffer drop arms

`drop_in_place::<[Instruction]>` (29188) reads an element's first word D and dispatches on the index D − (2^63 − 1) when
D is one of the tag words 2^63 … 2^63 + 23, else on index 0: indices up to 23 go through the table at 67760, index 24
(`AssignForGasCost`, past the table) branches at 29221 straight to 29153, the arm it shares with `Assign` (index 12, jump
entry 676). The arms here each free at most one buffer (`ArmOk`):
- index 0, `CreateService` (entry 687 → 29581): D is the capacity of its `Option<Vec<u8>>` (2^64 − 1 = `None`), ptr at
  el + 8, `dealloc(ptr, D, 1)`;
- 11, `Bless` (678 → 29241): capacity at el + 8, ptr at el + 16, `dealloc(ptr, 16 c, 8)`;
- 12 and 24, `Assign` / `AssignForGasCost` (676 → 29153): `dealloc(ptr, 32 c, 1)`;
- 13, `Designate` (688 → 29609): `dealloc(ptr, 336 c, 1)`;
- 17, `Provide` (681 → 29338): the octet at el + 8 (0: by hash), capacity at el + 16, ptr at el + 24, `dealloc(ptr, c, 1)`;
- 22, `RandomStorageAccumulate` (689 → 29640): capacity at el + 8 (2^64 − 1 = `Err`), then `Assign`'s tail (29162).
Each `dealloc` returns through jump entry 1356 to 29181, the next element. The code facts are tiers T1B and T1C (jump
entry 676 and the arm at 29153). GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.DropArms

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B Services.Bootstrap.CodeT1C
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.DropOut Services.Bootstrap.Refine.DropOutH
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Picoalloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 29188 … 29581: element k at E + 232 k whose first word D is no tag word (index 0, `CreateService`, whose
    `Option<Vec<u8>>` capacity is that word) dispatches through the table at 67760 (entry 687) to its arm, ω₈ = D. -/
theorem dd0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k D : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 D) (hD1 : D < 18446744073709551616)
    (hD2 : D < 9223372036854775808 ∨ 9223372036854775832 ≤ D)
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29581 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[8] = UInt64.ofNat D ∧
      μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 hD1 hD
  have rD : rdN μ (k * 232 + E) 8 = D := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67760 4 = 4294900912 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67760 : Nat) = 67760 + 4 * 0 from rfl, dtable_entry tab 0 (by decide)]; rfl
  have hrt' : ∀ a, 67760 ≤ a → a < 67764 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900912 = 18446744069414584320 + 4294900912 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1, hD1, hD2,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp


/-- 29188 … 29241: element k at E + 232 k of index 11 (`Bless`) dispatches through the table at 67760 to its arm. -/
theorem dd11 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 11))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29241 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 11 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67804 4 = 4294900894 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67804 : Nat) = 67760 + 4 * 11 from rfl, dtable_entry tab 11 (by decide)]; rfl
  have hrt' : ∀ a, 67804 ≤ a → a < 67808 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900894 = 18446744069414584320 + 4294900894 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29188 … 29153: element k at E + 232 k of index 12 (`Assign`) dispatches through the table at 67760 to its arm. -/
theorem dd12 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 12))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29153 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 12 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67808 4 = 4294900890 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67808 : Nat) = 67760 + 4 * 12 from rfl, dtable_entry tab 12 (by decide)]; rfl
  have hrt' : ∀ a, 67808 ≤ a → a < 67812 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900890 = 18446744069414584320 + 4294900890 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29188 … 29609: element k at E + 232 k of index 13 (`Designate`) dispatches through the table at 67760 to its arm. -/
theorem dd13 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 13))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29609 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 13 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67812 4 = 4294900914 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67812 : Nat) = 67760 + 4 * 13 from rfl, dtable_entry tab 13 (by decide)]; rfl
  have hrt' : ∀ a, 67812 ≤ a → a < 67816 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900914 = 18446744069414584320 + 4294900914 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29188 … 29338: element k at E + 232 k of index 17 (`Provide`) dispatches through the table at 67760 to its arm. -/
theorem dd17 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 17))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29338 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 17 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67828 4 = 4294900900 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67828 : Nat) = 67760 + 4 * 17 from rfl, dtable_entry tab 17 (by decide)]; rfl
  have hrt' : ∀ a, 67828 ≤ a → a < 67832 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900900 = 18446744069414584320 + 4294900900 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29188 … 29640: element k at E + 232 k of index 22 (`RandomStorageAccumulate`) dispatches through the table at 67760 to its arm. -/
theorem dd22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 22))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29640 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 22 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  have rt : rdN μ 67848 4 = 4294900916 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67848 : Nat) = 67760 + 4 * 22 from rfl, dtable_entry tab 22 (by decide)]; rfl
  have hrt' : ∀ a, 67848 ≤ a → a < 67852 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
  have sx : sxw 4 4294900916 = 18446744069414584320 + 4294900916 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29241 … 29181: `Bless`'s arm (its `Vec<(u32, u64)>`, 16 octets an item, align 8); the capacity (word 1 of `el`) is 0: nothing to free. -/
theorem aB0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29241 ω μ x 29181 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rc := rd8 (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29241 … 40613: `Bless`'s arm (its `Vec<(u32, u64)>`, 16 octets an item, align 8); the capacity c ≠ 0: `dealloc(ptr, …)` (ptr word 2; return address 1356 → 29181). -/
theorem aB1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29241 ω μ x 40613 ω' μ x 10 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rc := rd8 hc1 s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hc1, hr, hr2, re, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29153 … 29181: the arm of `Assign` and `AssignForGasCost` (32 octets an item, align 1); the capacity (word 1 of `el`) is 0: nothing to free. -/
theorem aA0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29153 ω μ x 29181 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rc := rd8 (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29153 … 40613: the arm of `Assign` and `AssignForGasCost` (32 octets an item, align 1); the capacity c ≠ 0: `dealloc(ptr, …)` (ptr word 2; return address 1356 → 29181). -/
theorem aA1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29153 ω μ x 40613 ω' μ x 9 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rc := rd8 hc1 s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hc1, hr, hr2, re, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29609 … 29181: `Designate`'s arm (336 octets an item, align 1); the capacity (word 1 of `el`) is 0: nothing to free. -/
theorem aD0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29609 ω μ x 29181 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rc := rd8 (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29609 … 40613: `Designate`'s arm (336 octets an item, align 1); the capacity c ≠ 0: `dealloc(ptr, …)` (ptr word 2; return address 1356 → 29181). -/
theorem aD1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29609 ω μ x 40613 ω' μ x 10 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rc := rd8 hc1 s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hc1, hr, hr2, re, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29188 … 29153: element k at E + 232 k of tag word 2^63 − 1 + 24 (`AssignForGasCost`): its index 24 is past the
    table's 24 entries, so the dispatch branches (29221) straight to the arm it shares with `Assign` (29153). -/
theorem dd24 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P]
    (x : X) (ω : Regs) (μ : Memory) (F E k : Nat)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 24))
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x 29153 ω' μ' x 13 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  have rD0 := rd8 (by decide) hD
  have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 24 := by
    rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, rD, e1,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
    post_simp

/-- 29581 … 29181: `CreateService`'s arm, its capacity D (ω₈, the element's first word) is 2^64 − 1 (`None`) or 0. -/
theorem aC0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (D : Nat) (μ : Memory) (hv : D = 18446744073709551615 ∨ D = 0) (h8 : ω[8] = UInt64.ofNat D) :
    ∃ ω' N, FreeStepsH p R 29581 ω μ x 29181 ω' μ x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with rfl | rfl
  · refine ⟨?_, 2, ?_, ?_⟩
    rotate_left
    · pvm_go [h8]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']
  · refine ⟨?_, 3, ?_, ?_⟩
    rotate_left
    · pvm_go [h8]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']

/-- 29581 … 40613: `CreateService`'s arm, D (ω₈) neither 2^64 − 1 nor 0: `dealloc(ptr, D, 1)` (ptr word 1). -/
theorem aC1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el D ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (hD0 : D ≠ 0) (hD1 : D < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat D) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29581 ω μ x 40613 ω' μ x 9 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rp := rd8 hptr s8
  have hc0 : ¬ D = 0 := hD0
  have hcm : ¬ D = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h8, hF, hel, hc0, hcm, hD1, hr, hr2, re, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

theorem rd1 {μ : Memory} {a b : Nat} (hb : b < 256) (h : μ.readN a 1 = Num.encodeLE 1 b) : rdN μ a 1 = b := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]

/-- 29338 … 29181: `Provide`'s arm, the octet b at el + 8 is 0 (by hash), or its capacity c at el + 16 is 0. -/
theorem aP0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el b c : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hb : b < 256) (hv : b = 0 ∨ c = 0)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 1 = Num.encodeLE 1 b) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 c)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω' N, FreeStepsH p R 29338 ω μ x 29181 ω' μ x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rb := rd1 hb s8
  rw [show ω = regsNF ω [] from rfl]
  by_cases hb0 : b = 0
  · subst hb0
    refine ⟨?_, 3, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rb, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
  · have hc : c = 0 := by omega
    subst hc
    have rc := rd8 (by decide) s16
    refine ⟨?_, 7, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rb, rc, hb0, hb, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29338 … 40613: `Provide`'s arm, b ≠ 0 and c ≠ 0: `dealloc(ptr, c, 1)` (ptr word 3). -/
theorem aP1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el b c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 32 ≤ 4294967296)
    (hb : b < 256) (hb0 : b ≠ 0) (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 1 = Num.encodeLE 1 b) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 c)
    (s24 : μ.readN (el + 24) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 32 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29338 ω μ x 40613 ω' μ x 13 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rb := rd1 hb s8
  have rc := rd8 hc1 s16
  have rp := rd8 hptr s24
  have hb0' : ¬ b = 0 := hb0
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hb, hb0', hc0, hc1, hr, hr2, re, rb, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29640 … 29181: `RandomStorageAccumulate`'s arm, its capacity c at el + 8 is 2^64 − 1 (`Err`) or 0. -/
theorem aR0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 16 ≤ 4294967296)
    (hv : c = 18446744073709551615 ∨ c = 0)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω' N, FreeStepsH p R 29640 ω μ x 29181 ω' μ x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with rfl | rfl
  · have rc := rd8 (by decide) s8
    refine ⟨?_, 4, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
  · have rc := rd8 (by decide) s8
    refine ⟨?_, 6, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29640 … 40613: `RandomStorageAccumulate`'s arm, c neither 2^64 − 1 nor 0: through `Assign`'s tail (29162),
    `dealloc(ptr, 32 c, 1)` (ptr word 2). -/
theorem aR1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P] (x : X)
    (ω : Regs) (μ : Memory) (F el c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 24 ≤ 4294967296)
    (hc : c ≠ 0) (hc1 : c < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29640 ω μ x 40613 ω' μ x 11 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rc := rd8 (by omega) s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  have hcm : ¬ c = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hcm, hc1, hr, hr2, re, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- **The single-buffer drop arms**: what the drop of an element at el reads, and whether it frees a buffer
    (`fr`) at ptr. The four shapes, by the element's first word:
    - not a tag word (index 0, `CreateService`): the word D is the capacity of its `Option<Vec<u8>>`, ptr at el + 8;
      freed unless D is 2^64 − 1 (`None`) or 0;
    - tag 11, 12, 13 or 24 (`Bless`, `Assign`, `Designate`, `AssignForGasCost`): capacity c at el + 8, ptr at el + 16,
      freed unless c = 0;
    - tag 17 (`Provide`): the octet b at el + 8 (0: by hash), capacity c at el + 16, ptr at el + 24, freed unless b = 0
      or c = 0;
    - tag 22 (`RandomStorageAccumulate`): capacity c at el + 8, ptr at el + 16, freed unless c is 2^64 − 1 (`Err`)
      or 0. -/
def ArmOk (μ : Memory) (el : Nat) (fr : Bool) (ptr : Nat) : Prop :=
  (∃ D, D < 18446744073709551616 ∧ (D < 9223372036854775808 ∨ 9223372036854775832 ≤ D) ∧
    μ.readN el 8 = Num.encodeLE 8 D ∧ μ.readN (el + 8) 8 = Num.encodeLE 8 ptr ∧
    (fr = true ↔ (D ≠ 18446744073709551615 ∧ D ≠ 0))) ∨
  (∃ t c, (t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 24) ∧ c < 18446744073709551616 ∧
    μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + t) ∧ μ.readN (el + 8) 8 = Num.encodeLE 8 c ∧
    μ.readN (el + 16) 8 = Num.encodeLE 8 ptr ∧ (fr = true ↔ c ≠ 0)) ∨
  (∃ b c, b < 256 ∧ c < 18446744073709551616 ∧
    μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + 17) ∧ μ.readN (el + 8) 1 = Num.encodeLE 1 b ∧
    μ.readN (el + 16) 8 = Num.encodeLE 8 c ∧ μ.readN (el + 24) 8 = Num.encodeLE 8 ptr ∧
    (fr = true ↔ (b ≠ 0 ∧ c ≠ 0))) ∨
  (∃ c, c < 18446744073709551616 ∧
    μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + 22) ∧ μ.readN (el + 8) 8 = Num.encodeLE 8 c ∧
    μ.readN (el + 16) 8 = Num.encodeLE 8 ptr ∧ (fr = true ↔ (c ≠ 0 ∧ c ≠ 18446744073709551615)))

/-- `ArmOk` reads only the element's 32 octets. -/
theorem ArmOk.congr {μ μ' : Memory} {el : Nat} {fr : Bool} {ptr : Nat} (h : ArmOk μ el fr ptr)
    (k : ∀ a, el ≤ a → a < el + 32 → μ'.read a = μ.read a) : ArmOk μ' el fr ptr := by
  have rc : ∀ a l, el ≤ a → a + l ≤ el + 32 → μ'.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  rcases h with ⟨D, h1, h2, e0, e8, hf⟩ | ⟨t, c, ht, hc, e0, e8, e16, hf⟩ | ⟨b, c, hb, hc, e0, e8, e16, e24, hf⟩ |
    ⟨c, hc, e0, e8, e16, hf⟩
  · exact Or.inl ⟨D, h1, h2, by rw [rc _ _ (by omega) (by omega)]; exact e0,
      by rw [rc _ _ (by omega) (by omega)]; exact e8, hf⟩
  · exact Or.inr (Or.inl ⟨t, c, ht, hc, by rw [rc _ _ (by omega) (by omega)]; exact e0,
      by rw [rc _ _ (by omega) (by omega)]; exact e8, by rw [rc _ _ (by omega) (by omega)]; exact e16, hf⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b, c, hb, hc, by rw [rc _ _ (by omega) (by omega)]; exact e0,
      by rw [rc _ _ (by omega) (by omega)]; exact e8, by rw [rc _ _ (by omega) (by omega)]; exact e16,
      by rw [rc _ _ (by omega) (by omega)]; exact e24, hf⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨c, hc, by rw [rc _ _ (by omega) (by omega)]; exact e0,
      by rw [rc _ _ (by omega) (by omega)]; exact e8, by rw [rc _ _ (by omega) (by omega)]; exact e16, hf⟩))

/-- What the dispatch and a single-buffer arm achieve from 29188: to 29181 when nothing is freed (`fr` false), else
    to `dealloc` (40613) with ω₀ = 1356 (→ 29181) and ω₇ = ptr; ω₁, ω₅, ω₆ kept; memory changes only at F + 48. -/
def BufRun {p : ByteArray} (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (F : Nat) (fr : Bool) (ptr : Nat) :
    Prop :=
  ∃ ω' μ' N, FreeStepsH p R 29188 ω μ x (if fr = true then 40613 else 29181) ω' μ' x N ∧
    ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
    (fr = true → ω'[0] = UInt64.ofNat 1356 ∧ ω'[7] = UInt64.ofNat ptr) ∧
    (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

theorem glue0 {p : ByteArray} {x : X} {ω ω1 ω2 : Regs} {μ μ1 : Memory} {F A N1 N2 ptr : Nat}
    (run1 : FreeStepsH p R 29188 ω μ x A ω1 μ1 x N1) (a1 : ω1[1] = ω[1]) (a5 : ω1[5] = ω[5]) (a6 : ω1[6] = ω[6])
    (afr : ∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ1.read a = μ.read a)
    (ard : ∀ a, μ1.readable a = μ.readable a) (awr : ∀ a, μ1.writable a = μ.writable a)
    (run2 : FreeStepsH p R A ω1 μ1 x 29181 ω2 μ1 x N2) (b1 : ω2[1] = ω1[1]) (b5 : ω2[5] = ω1[5])
    (b6 : ω2[6] = ω1[6]) : BufRun (p := p) R x ω μ F false ptr :=
  ⟨ω2, μ1, N1 + N2, run1.trans run2, by rw [b1, a1], by rw [b5, a5], by rw [b6, a6],
    fun h => absurd h (by decide), afr, ard, awr⟩

theorem glue1 {p : ByteArray} {x : X} {ω ω1 ω2 : Regs} {μ μ1 : Memory} {F A N1 N2 ptr : Nat}
    (run1 : FreeStepsH p R 29188 ω μ x A ω1 μ1 x N1) (a1 : ω1[1] = ω[1]) (a5 : ω1[5] = ω[5]) (a6 : ω1[6] = ω[6])
    (afr : ∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ1.read a = μ.read a)
    (ard : ∀ a, μ1.readable a = μ.readable a) (awr : ∀ a, μ1.writable a = μ.writable a)
    (run2 : FreeStepsH p R A ω1 μ1 x 40613 ω2 μ1 x N2) (b0 : ω2[0] = UInt64.ofNat 1356) (b1 : ω2[1] = ω1[1])
    (b5 : ω2[5] = ω1[5]) (b6 : ω2[6] = ω1[6]) (b7 : ω2[7] = UInt64.ofNat ptr) :
    BufRun (p := p) R x ω μ F true ptr :=
  ⟨ω2, μ1, N1 + N2, run1.trans run2, by rw [b1, a1], by rw [b5, a5], by rw [b6, a6],
    fun _ => ⟨b0, b7⟩, afr, ard, awr⟩

/-- **The dispatch and a single-buffer arm** (29188 → 29181 or `dealloc`), element k at E + 232 k satisfying
    `ArmOk`. -/
theorem run_buf {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    [HasCodeT1C p P] (x : X) (ω : Regs) (μ : Memory) (F E k ptr : Nat) (fr : Bool)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0) (hEF : E + 232 * k + 32 ≤ F)
    (hptr : ptr < 18446744073709551616) (hA : ArmOk μ (E + 232 * k) fr ptr)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    BufRun (p := p) R x ω μ F fr ptr := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hr8 : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true := fun a h h' => hrE a h (by omega)
  have post : ∀ (μ1 : Memory), (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ1.read a = μ.read a) →
      (∀ a, μ1.readable a = μ.readable a) →
      (∀ a l, a + l ≤ F + 48 → μ1.readN a l = μ.readN a l) ∧
      (∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ1.readable a = true) ∧
      (∀ a, F + 48 ≤ a → a < F + 56 → μ1.readable a = true) := fun μ1 hfr hrd =>
    ⟨fun a l h => Memory.readN_congr (fun j hj => hfr _ (by omega) (Or.inl (by omega))),
     fun a h h' => by rw [hrd]; exact hrE a h h',
     fun a h h' => by rw [hrd]; exact Memory.readable_of_writable (hw a (by omega) (by omega))⟩
  have hF' : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0 := ⟨hF0, hF1, hF8⟩
  rcases hA with ⟨D, hD1, hD2, e0, e8, hf⟩ | ⟨t, c, ht, hc, e0, e8, e16, hf⟩ | ⟨b, c, hb, hc, e0, e8, e16, e24, hf⟩ |
    ⟨c, hc, e0, e8, e16, hf⟩
  · obtain ⟨ω1, μ1, run1, a1, a5, a6, a8, a48, afr, ard, awr⟩ := dd0 (p := p) (P := P) (R := R) x ω μ F E k D
      hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 hD1 hD2 tab hrt hr8 hw
    obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
    cases fr
    · have hv : D = 18446744073709551615 ∨ D = 0 := by
        by_cases h : D ≠ 18446744073709551615 ∧ D ≠ 0
        · exact absurd (hf.2 h) (by decide)
        · omega
      obtain ⟨ω2, N2, run2, b1, b5, b6⟩ := aC0 (p := p) (P := P) (R := R) x ω1 D μ1 hv a8
      exact ⟨ω2, μ1, 20 + N2, run1.trans run2, by rw [b1, a1], by rw [b5, a5], by rw [b6, a6],
        fun h => absurd h (by decide), afr, ard, awr⟩
    · obtain ⟨hn1, hn0⟩ := hf.1 rfl
      obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aC1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) D ptr
        (by omega) (by omega) hn0 (by omega) hptr (a1.trans h1) a8 a48 (by rw [k1 _ _ (by omega)]; exact e8)
        (fun a h h' => rd1' a (by omega) (by omega)) rd48
      exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
  · have hc0 : fr = false → c = 0 := fun h => by
      by_cases h' : c = 0
      · exact h'
      · have := hf.2 h'; rw [h] at this; exact absurd this (by decide)
    rcases ht with rfl | rfl | rfl | rfl
    · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd11 (p := p) (P := P) (R := R) x ω μ F E k
        hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 tab hrt hr8 hw
      obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
      cases fr
      · obtain ⟨ω2, run2, b1, b5, b6⟩ := aB0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) (by omega)
          (by omega) (a1.trans h1) a48 (by rw [k1 _ _ (by omega), ← hc0 rfl]; exact e8)
          (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
      · obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aB1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr
          (by omega) (by omega) (hf.1 rfl) hc hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
          (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
    · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd12 (p := p) (P := P) (R := R) x ω μ F E k
        hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 tab hrt hr8 hw
      obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
      cases fr
      · obtain ⟨ω2, run2, b1, b5, b6⟩ := aA0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) (by omega)
          (by omega) (a1.trans h1) a48 (by rw [k1 _ _ (by omega), ← hc0 rfl]; exact e8)
          (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
      · obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aA1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr
          (by omega) (by omega) (hf.1 rfl) hc hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
          (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
    · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd13 (p := p) (P := P) (R := R) x ω μ F E k
        hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 tab hrt hr8 hw
      obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
      cases fr
      · obtain ⟨ω2, run2, b1, b5, b6⟩ := aD0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) (by omega)
          (by omega) (a1.trans h1) a48 (by rw [k1 _ _ (by omega), ← hc0 rfl]; exact e8)
          (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
      · obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aD1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr
          (by omega) (by omega) (hf.1 rfl) hc hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
          (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
    · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd24 (p := p) (P := P) (R := R) x ω μ F E k
        hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 e0 hr8 hw
      obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
      cases fr
      · obtain ⟨ω2, run2, b1, b5, b6⟩ := aA0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) (by omega)
          (by omega) (a1.trans h1) a48 (by rw [k1 _ _ (by omega), ← hc0 rfl]; exact e8)
          (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
      · obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aA1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr
          (by omega) (by omega) (hf.1 rfl) hc hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
          (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
        exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
  · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd17 (p := p) (P := P) (R := R) x ω μ F E k
      hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 tab hrt hr8 hw
    obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
    cases fr
    · have hv : b = 0 ∨ c = 0 := by
        by_cases h : b ≠ 0 ∧ c ≠ 0
        · exact absurd (hf.2 h) (by decide)
        · omega
      obtain ⟨ω2, N2, run2, b1, b5, b6⟩ := aP0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) b c (by omega)
        (by omega) hb hv (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
        (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
      exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
    · obtain ⟨hb0, hc0⟩ := hf.1 rfl
      obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aP1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) b c ptr
        (by omega) (by omega) hb hb0 hc0 hc hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
        (by rw [k1 _ _ (by omega)]; exact e16) (by rw [k1 _ _ (by omega)]; exact e24)
        (fun a h h' => rd1' a (by omega) (by omega)) rd48
      exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7
  · obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := dd22 (p := p) (P := P) (R := R) x ω μ F E k
      hF' (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 e0 tab hrt hr8 hw
    obtain ⟨k1, rd1', rd48⟩ := post μ1 afr ard
    cases fr
    · have hv : c = 18446744073709551615 ∨ c = 0 := by
        by_cases h : c ≠ 0 ∧ c ≠ 18446744073709551615
        · exact absurd (hf.2 h) (by decide)
        · omega
      obtain ⟨ω2, N2, run2, b1, b5, b6⟩ := aR0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c (by omega)
        (by omega) hv (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
        (fun a h h' => rd1' a (by omega) (by omega)) rd48
      exact glue0 run1 a1 a5 a6 afr ard awr run2 b1 b5 b6
    · obtain ⟨hc0, hcm⟩ := hf.1 rfl
      obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := aR1 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) c ptr
        (by omega) (by omega) hc0 (by omega) hptr (a1.trans h1) a48 (by rw [k1 _ _ (by omega)]; exact e8)
        (by rw [k1 _ _ (by omega)]; exact e16) (fun a h h' => rd1' a (by omega) (by omega)) rd48
      exact glue1 run1 a1 a5 a6 afr ard awr run2 b0 b1 b5 b6 b7

/-- **One single-buffer element dropped** (29188 … 29181): element k at el = E + 232 k satisfying `ArmOk` (μ, `fr`,
    ptr); when `fr`, the buffer at ptr is the data of the allocated chunk `ch`, which is freed. The element lies in the data
    of an allocated chunk `cb` other than `ch`. The heap context holds after; every other allocated chunk stays with its
    data; the frame from F up is kept but for F + 48 … F + 56; the pages and the read-only bytes are kept. -/
theorem drop_buf {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    [HasCodeT1C p P] (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (F E k ptr : Nat) (fr : Bool) (ch cb : Chunk)
    (hF : 2147483716 ≤ F ∧ S0 + 40 ≤ F ∧ F + 80 ≤ S1 ∧ F % 8 = 0)
    (hel : E + 232 * k + 32 ≤ 2147483648) (hptr : ptr < 18446744073709551616)
    (hA : ArmOk μ (E + 232 * k) fr ptr)
    (hch : fr = true → ch ∈ chunks s ∧ ch.used = true ∧ ch.addr + 32 = ptr)
    (hcbD : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → InData cb a)
    (hcbch : fr = true → cb ≠ ch)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k) (H : HeapCtx env pb S0 S1 μ s)
    (cbm : cb ∈ chunks s) (cbu : cb.used = true)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    ∃ ω' μ' s' N, FreeStepsH p R 29188 ω μ x 29181 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ HeapCtx env pb S0 S1 μ' s' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (fr = true → d ≠ ch) →
        d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
  obtain ⟨hF0, hF1, hF2, hF8⟩ := hF
  have hS := H.hS1
  have hwF : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have rdcb : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H cbm cbu (hcbD a h1 h2))
  obtain ⟨ω1, μ1, N1, run1, a1, a5, a6, a07, afr, ard, awr⟩ := run_buf (p := p) (P := P) (R := R) x ω μ F E k ptr fr
    ⟨by omega, by omega, hF8⟩ (by omega) hptr hA h1 h6 s40 s32 s24 s16 tab hrt rdcb hwF
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
  have ro1 : ∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b := fun b hb hwb => by
    refine afr b (by unfold two32 at hb; omega) ?_
    by_cases h : F + 48 ≤ b ∧ b < F + 56
    · have := hwF b (by omega) (by omega); rw [hwb] at this; exact absurd this (by decide)
    · omega
  have fr1 : ∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) →
      μ1.read a = μ.read a := fun a h0 _ _ h => afr a h0 h
  cases fr
  · exact ⟨ω1, μ1, s, N1, run1, a1, a5, a6, H1, fr1,
      fun d hd hu _ => ⟨hd, fun a ha => afr a (by have := data_lo H hd hu ha; omega)
        (Or.inl (by have := data_lo H hd hu ha; omega))⟩, ard, awr, ro1⟩
  · obtain ⟨hchm, hchu, hcha⟩ := hch rfl
    obtain ⟨b0, b7⟩ := a07 rfl
    obtain ⟨ω3, μ3, run3, H3, -, pg3, ro3, stk3, -, keep3, d0, d1, d5, d6⟩ :=
      Decode.DeallocCall.dealloc_call (R := R) (p := p) (P := P) env pb S0 S1 x ω1 μ1 s F ptr 1356 29181 ch H1 hchm
        hchu hcha b0 (by rw [a1]; exact h1) b7 (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_677]) bs_29181 hF0 ⟨hF1, by omega⟩
    refine ⟨ω3, μ3, free s ptr, N1 + 249, run1.trans run3, by rw [d1, a1], by rw [d5, a5],
      by rw [d6, a6], H3, fun a h0 hF h2 h3 => by rw [stk3 a h0 hF, fr1 a h0 hF h2 h3],
      fun d hd hu hne => ?_,
      fun a => by unfold Memory.readable; rw [pg3]; exact ard a,
      fun a => by unfold Memory.writable; rw [pg3]; exact awr a,
      fun b hb hwb => by rw [ro3 b hb (by rw [awr]; exact hwb), ro1 b hb hwb]⟩
    obtain ⟨hd3, kd3⟩ := keep3 d hd hu (hne rfl)
    exact ⟨hd3, fun a ha => by rw [kd3 a ha, afr a (by have := data_lo H hd hu ha; omega)
      (Or.inl (by have := data_lo H hd hu ha; omega))]⟩

end Services.Bootstrap.Refine.DropArms
