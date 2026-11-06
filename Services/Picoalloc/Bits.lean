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
