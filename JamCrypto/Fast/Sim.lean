/-!
# Simulation of loops

The fast implementations run the same loops as the reference ones, on other state types. A
relation between the two states that every step preserves (with the same `yield`/`done` choice) is
preserved by the whole loop: `forIn_rel` (lists) and `forIn_range_rel` (`for i in [a:b]`).
-/

namespace JamCrypto.Fast

/-- Two loop steps agree: both continue or both stop, in related states. -/
def StepRel {α β : Type} (R : α → β → Prop) : ForInStep α → ForInStep β → Prop
  | .yield a, .yield b => R a b
  | .done a, .done b => R a b
  | _, _ => False

theorem forIn_rel {γ α β : Type} (R : α → β → Prop) (l : List γ)
    (f : γ → α → Id (ForInStep α)) (g : γ → β → Id (ForInStep β)) {a : α} {b : β} (h0 : R a b)
    (hs : ∀ x a b, R a b → StepRel R (f x a).run (g x b).run) :
    R (forIn l a f).run (forIn l b g).run := by
  induction l generalizing a b with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.forIn_cons]
    have := hs x a b h0
    revert this
    cases hf : f x a <;> cases hg : g x b <;> simp [StepRel, Id.run] <;> intro h
    · exact h
    · exact ih h

theorem forIn_range_rel {α β : Type} (R : α → β → Prop) (r : Std.Legacy.Range)
    (f : Nat → α → Id (ForInStep α)) (g : Nat → β → Id (ForInStep β)) {a : α} {b : β} (h0 : R a b)
    (hs : ∀ x a b, R a b → StepRel R (f x a).run (g x b).run) :
    R (forIn r a f).run (forIn r b g).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_rel R _ f g h0 hs

end JamCrypto.Fast
