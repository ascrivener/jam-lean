import Services.Picoalloc.Invariant

/-!
# The bins' bitmap

`find_first` returns a marked bin: one whose bit is set, so (by the invariant) a non-empty bin.
-/

namespace Picoalloc

theorem testBit_div_mul_pow {v i k : Nat} (h : (v / 2 ^ i * 2 ^ i).testBit k = true) :
    i ≤ k ∧ v.testBit k = true := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.testBit_shiftRight, show i + (k - i) = k by omega] at h2
  exact ⟨h1, h2⟩

/-- `lowest_set_bit_after` finds a set bit at or after `i`, below 64. -/
theorem lowestAfter_some {v i k : Nat} (h : lowestAfter v i = some k) :
    k < 64 ∧ i ≤ k ∧ v.testBit k = true := by
  unfold lowestAfter at h
  dsimp only at h
  split at h
  · simp at h
  · have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [List.mem_range] at hm
    obtain ⟨h1, h2⟩ := testBit_div_mul_pow hp
    exact ⟨hm, h1, h2⟩

/-- **`find_first` returns a marked bin** below 2432, when the primary word marks only the 38
    secondary words. -/
theorem findFirst_some {s : State} {b r : Nat} (hb : b < binCount) (hp : s.primary < 2 ^ 38)
    (h : findFirst s b = some r) : r < binCount ∧ (s.secondary (r / 64)).testBit (r % 64) = true := by
  unfold findFirst at h
  simp only at h
  split at h
  · rename_i k hk
    split at hk
    · obtain ⟨hk1, -, hk3⟩ := lowestAfter_some hk
      simp only [Option.some.injEq] at h
      subst h
      unfold binCount at hb ⊢
      refine ⟨by omega, ?_⟩
      rw [show (b / 64 * 64 + k) / 64 = b / 64 by omega, show (b / 64 * 64 + k) % 64 = k by omega]
      exact hk3
    · simp at hk
  · split at h
    · simp at h
    · rename_i p' hp'
      obtain ⟨hp1, -, hp3⟩ := lowestAfter_some hp'
      have hp38 : p' < 38 := by
        rcases Nat.lt_or_ge p' 38 with hc | hc
        · exact hc
        · exfalso
          have : s.primary < 2 ^ p' := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by decide) hc)
          rw [Nat.testBit_lt_two_pow this] at hp3
          simp at hp3
      cases hk : lowestAfter (s.secondary p') 0 with
      | none => simp [hk] at h
      | some k =>
        simp only [hk, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨hk1, -, hk3⟩ := lowestAfter_some hk
        unfold binCount
        refine ⟨by omega, ?_⟩
        rw [show (p' * 64 + k) / 64 = p' by omega, show (p' * 64 + k) % 64 = k by omega]
        exact hk3

end Picoalloc


namespace Picoalloc

/-- The bitmap's part of the invariant, against the heads `hs`. -/
def BitsOk (sec : Nat → Nat) (pri : Nat) (hs : Nat → Nat) : Prop :=
  (∀ b, b < binCount → ((sec (b / 64)).testBit (b % 64) ↔ hs b ≠ 0)) ∧
  (∀ p, p < 38 → (pri.testBit p ↔ sec p % 2 ^ 64 ≠ 0)) ∧ (∀ p, p < 38 → sec p < 2 ^ 64) ∧ pri < 2 ^ 38

theorem ne_zero_iff_testBit {x : Nat} (hx : x < 2 ^ 64) : x ≠ 0 ↔ ∃ j, j < 64 ∧ x.testBit j = true := by
  constructor
  · intro h
    rcases Classical.em (∃ j, j < 64 ∧ x.testBit j = true) with e | e
    · exact e
    · exfalso
      apply h
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge j 64 with h1 | h1
      · cases hb : x.testBit j
        · rfl
        · exact absurd ⟨j, h1, hb⟩ e
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h1))
  · rintro ⟨j, _, hj⟩ h; subst h; simp at hj

theorem testBit_clear {k j : Nat} (hk : k < 64) :
    ((2 ^ 64 - 1) ^^^ 2 ^ k).testBit j = (decide (j < 64) && decide (j ≠ k)) := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h1 : j < 64 <;> by_cases h2 : j = k <;> simp [h1, h2] <;> omega

/-- **Setting a bin's bit** when the bin becomes non-empty keeps the bitmap consistent. -/
theorem setBit_ok {s : State} {hs : Nat → Nat} {b : Nat} (hb : b < binCount)
    (h : BitsOk s.secondary s.primary s.heads) (hother : ∀ b', b' ≠ b → hs b' = s.heads b') (hne : hs b ≠ 0) :
    BitsOk (setBit s b).secondary (setBit s b).primary hs := by
  obtain ⟨hbits, hprim, hw, hpw⟩ := h
  unfold binCount at hb
  have hb64 : b % 64 < 64 := Nat.mod_lt _ (by decide)
  have hp38 : b / 64 < 38 := by omega
  unfold setBit
  dsimp only
  refine ⟨fun b' hb' => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
  · by_cases hq : b' / 64 = b / 64
    · rw [hq, upd_self, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hr : b' = b
      · subst hr; simp [hne]
      · have : b % 64 ≠ b' % 64 := fun h => hr (by unfold binCount at hb'; omega)
        simp only [this, decide_false, Bool.or_false]
        rw [← hq]
        exact (hbits b' hb').trans (by rw [hother b' hr])
    · rw [upd_ne _ _ hq, hother b' (fun h => hq (by rw [h]))]
      exact hbits b' hb'
  · by_cases hq : p = b / 64
    · subst hq
      rw [upd_self, Nat.testBit_or, Nat.testBit_two_pow]
      simp only [decide_true, Bool.or_true, true_iff]
      rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow (hw _ hp) (Nat.pow_lt_pow_right (by decide) hb64))]
      exact (ne_zero_iff_testBit (Nat.or_lt_two_pow (hw _ hp) (Nat.pow_lt_pow_right (by decide) hb64))).mpr
        ⟨b % 64, hb64, by rw [Nat.testBit_or, Nat.testBit_two_pow]; simp⟩
    · rw [upd_ne _ _ hq, Nat.testBit_or, Nat.testBit_two_pow]
      have : b / 64 ≠ p := fun h => hq h.symm
      simp only [this, decide_false, Bool.or_false]
      exact hprim p hp
  · by_cases hq : p = b / 64
    · subst hq; rw [upd_self]
      exact Nat.or_lt_two_pow (hw _ hp) (Nat.pow_lt_pow_right (by decide) hb64)
    · rw [upd_ne _ _ hq]; exact hw p hp
  · exact Nat.or_lt_two_pow hpw (Nat.pow_lt_pow_right (by decide) hp38)


/-- **Clearing a bin's bit** when the bin becomes empty keeps the bitmap consistent. -/
theorem unsetBit_ok {s : State} {hs : Nat → Nat} {b : Nat} (hb : b < binCount)
    (h : BitsOk s.secondary s.primary s.heads) (hother : ∀ b', b' ≠ b → hs b' = s.heads b') (he : hs b = 0) :
    BitsOk (unsetBit s b).secondary (unsetBit s b).primary hs := by
  obtain ⟨hbits, hprim, hw, hpw⟩ := h
  unfold binCount at hb
  have hb64 : b % 64 < 64 := Nat.mod_lt _ (by decide)
  have hp38 : b / 64 < 38 := by omega
  have hp64 : b / 64 < 64 := by omega
  unfold unsetBit
  dsimp only
  generalize hwdef : s.secondary (b / 64) &&& ((2 ^ 64 - 1) ^^^ 2 ^ (b % 64)) = w
  have hwlt : w < 2 ^ 64 := by rw [← hwdef]; exact Nat.lt_of_le_of_lt Nat.and_le_left (hw _ hp38)
  have hwbit : ∀ j, w.testBit j = (decide (j < 64) && decide (j ≠ b % 64) && (s.secondary (b / 64)).testBit j) := by
    intro j; rw [← hwdef, Nat.testBit_and, testBit_clear hb64]; cases (s.secondary (b / 64)).testBit j <;> simp
  refine ⟨fun b' hb' => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
  · unfold binCount at hb'
    by_cases hq : b' / 64 = b / 64
    · rw [hq, upd_self, hwbit]
      by_cases hr : b' = b
      · subst hr; simp [he]
      · have : b' % 64 ≠ b % 64 := fun h => hr (by omega)
        simp only [Nat.mod_lt _ (show 64 > 0 by decide), decide_true, this, ne_eq, not_false_eq_true,
          Bool.true_and]
        rw [← hq]
        exact (hbits b' (by unfold binCount; omega)).trans (by rw [hother b' hr])
    · rw [upd_ne _ _ hq, hother b' (fun h => hq (by rw [h]))]
      exact hbits b' (by unfold binCount; omega)
  · by_cases hq : p = b / 64
    · subst hq
      rw [upd_self, Nat.mod_eq_of_lt hwlt]
      split
      · rename_i hw0
        rw [Nat.testBit_and, testBit_clear hp64]
        simp [hw0]
      · rename_i hw0
        rw [← ne_eq] at hw0
        refine ⟨fun _ => hw0, fun _ => ?_⟩
        obtain ⟨j, hj, hjb⟩ := (ne_zero_iff_testBit hwlt).mp hw0
        rw [hwbit] at hjb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hjb
        exact (hprim _ hp).mpr (by
          rw [Nat.mod_eq_of_lt (hw _ hp)]
          exact (ne_zero_iff_testBit (hw _ hp)).mpr ⟨j, hj, hjb.2⟩)
    · rw [upd_ne _ _ hq]
      split
      · rw [Nat.testBit_and, testBit_clear hp64]
        have : p ≠ b / 64 := hq
        simp only [show p < 64 by omega, decide_true, this, ne_eq, not_false_eq_true, Bool.and_true,
          Bool.true_and]
        exact hprim p hp
      · exact hprim p hp
  · by_cases hq : p = b / 64
    · subst hq; rw [upd_self]; exact hwlt
    · rw [upd_ne _ _ hq]; exact hw p hp
  · split
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hpw
    · exact hpw

end Picoalloc
