import Services.Picoalloc.Alloc

/-!
# When the model's `alloc` fails

With alignment one unit on an initialised heap, `alloc` is `alloc1`, which returns `none` in
exactly four ways: the request (plus its header unit) exceeds `MAX_ALLOCATION_SIZE`; no marked bin
at or above either of the request's bins; the found bin's first chunk is too small; or the
allocation ends past the allocated space and the heap cannot grow to cover it.
-/

namespace Services.Bootstrap.Alloc

open Picoalloc

/-- **How `alloc1` fails**: the request too large; no bin found; the found bin's first chunk too
    small; or the allocation's end E past the allocated space with `grow` refusing E. -/
theorem alloc1_none {grow : Grow} {r : Nat} {s : State} (h : alloc1 grow r s = none) :
    maxSize < r + 1 ∨
    (r + 1 ≤ maxSize ∧ (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = none) ∨
    (∃ bin, r + 1 ≤ maxSize ∧ (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = some bin ∧
      wordSize (s.hdr (s.heads bin)).size < r + 1) ∨
    (∃ bin, r + 1 ≤ maxSize ∧ (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = some bin ∧
      r + 1 ≤ wordSize (s.hdr (s.heads bin)).size ∧
      s.allocated < (s.heads bin - s.base) / 32 + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) ∧
      grow s.base ((s.heads bin - s.base) / 32 + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1)) = false) := by
  unfold alloc1 at h
  split at h
  · exact Or.inl (by omega)
  rename_i hmax
  simp only [Option.orElse_eq_or] at h
  cases hfb : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) with
  | none => exact Or.inr (Or.inl ⟨by omega, rfl⟩)
  | some bin =>
    simp only [hfb, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hS; exact Or.inr (Or.inr (Or.inl ⟨bin, by omega, rfl, hS⟩))
    rename_i hS
    generalize hE : (s.heads bin - s.base) / 32 + 1 + r +
      (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) = E at h ⊢
    by_cases hlt : s.allocated < E
    · by_cases hgr : grow s.base E = true
      · simp [hlt, hgr] at h
      · subst hE; exact Or.inr (Or.inr (Or.inr ⟨bin, by omega, rfl, by omega, hlt, by simpa using hgr⟩))
    · simp [hlt] at h

end Services.Bootstrap.Alloc
