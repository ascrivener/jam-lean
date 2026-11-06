import Services.Picoalloc.FreeLists

/-!
# Facts about a member of a free list

For x in a list linked from its head, back-linked and without repeats: x's `next` is 0 or in the
list; if x is not the head, its `prevL` is in the list, and differs from its `next`.
-/

namespace Picoalloc

theorem Linked.next_mem {s : State} {a x : Nat} {l : List Nat} (h : Linked s a l) (hx : x ∈ l) :
    (s.hdr x).next = 0 ∨ (s.hdr x).next ∈ l := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  have hB := h.of_append
  cases B with
  | nil => exact Or.inl hB
  | cons y ys => exact Or.inr (by rw [hB.1]; simp)

theorem BackLinked.prevL_mem {s : State} {a x : Nat} {l : List Nat} (hl : Linked s a l) (h : BackLinked s 0 l)
    (hx : x ∈ l) (hxa : x ≠ a) : (s.hdr x).prevL ∈ l := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  rcases List.eq_nil_or_concat A with hA | ⟨A', y, hA⟩
  · subst hA; exact absurd hl.1.symm hxa
  · subst hA
    rw [List.concat_eq_append, List.append_assoc, List.singleton_append] at h ⊢
    rw [h.of_append]; simp

theorem next_ne_prevL {s : State} {a x : Nat} {l : List Nat} (hl : Linked s a l) (h : BackLinked s 0 l)
    (hnd : l.Nodup) (hx : x ∈ l) (hxa : x ≠ a) (hn : (s.hdr x).next ≠ 0) :
    (s.hdr x).next ≠ (s.hdr x).prevL := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  rcases List.eq_nil_or_concat A with hA | ⟨A', y, hA⟩
  · subst hA; exact absurd hl.1.symm hxa
  · subst hA
    rw [List.concat_eq_append, List.append_assoc, List.singleton_append] at h hl hnd
    rw [h.of_append]
    have hB := Linked.of_append (l1 := A' ++ [y]) (x := x) (l2 := B)
      (by rw [List.append_assoc, List.singleton_append]; exact hl)
    cases B with
    | nil => exact absurd hB hn
    | cons z zs =>
      rw [hB.1]
      intro e; subst e
      have := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
      exact this (List.mem_cons_of_mem _ List.mem_cons_self)

end Picoalloc
