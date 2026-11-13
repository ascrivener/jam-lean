import Services.Bootstrap.Acc.Impl.Impl

/-!
# `Impl` for loops

`Spec.accumulate` runs `for it in items do …` over the decoded inputs, and `onWorkItem` over the
instructions. `Impl.forIn` turns such a loop into a loop invariant on the binary's state: each
iteration implements the body and returns to the invariant for the elements left. Helpers:
`Impl.mono_post` (a weaker post-condition) and `Impl.pure_of`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap.Spec
variable {Qu : Type}

/-- **A weaker post-condition.** -/
theorem Impl.mono_post {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α : Type} {Q Q' : α → St Qu → Prop} (hQ : ∀ a s, Q a s → Q' a s) :
    ∀ (prog : Prog AOp α) (s : St Qu), Impl p R env Ab prog Q s → Impl p R env Ab prog Q' s := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    rcases h with h | ⟨s', h1, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨s', h1, h2, hQ a s' h3⟩
  | panic => intro s h; exact h
  | call op k ih =>
    intro s h
    unfold Impl at h ⊢
    rcases h with h | ⟨s₁, h1, h2, h3⟩
    · exact .inl h
    refine .inr ⟨s₁, h1, h2, ?_⟩
    revert h3
    cases ASem.step env op s.c with
    | some bc =>
      intro h3
      rcases h3 with h3 | ⟨s₂, g1, g2, g3⟩
      · exact .inl h3
      · exact .inr ⟨s₂, g1, g2, ih bc.1 s₂ g3⟩
    | none => exact id

/-- `Q a` where the run is implements `pure a`. -/
theorem Impl.pure_of {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α : Type} {Q : α → St Qu → Prop} {a : α} {s : St Qu} (h : Q a s) :
    Impl p R env Ab (Prog.pure a) Q s := .inr ⟨s, ⟨0, .refl⟩, rfl, h⟩

/-- **`Impl` along a `for` loop over a list**: with an invariant I (the elements left, the
    accumulator, the state), if each body, from I with x first, implements its step and returns to I
    for the rest (`yield`) or reaches Q (`done`), and I with nothing left gives Q, then the loop
    implements Q. -/
theorem Impl.forIn {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α β : Type} (f : α → β → Prog AOp (ForInStep β)) (Q : β → St Qu → Prop)
    (I : List α → β → St Qu → Prop)
    (hstep : ∀ x xs b s, I (x :: xs) b s →
      Impl p R env Ab (f x b) (fun r s' => match r with
        | .yield b' => I xs b' s'
        | .done b' => Q b' s') s)
    (hend : ∀ b s, I [] b s → Q b s) :
    ∀ (xs : List α) (b : β) (s : St Qu), I xs b s → Impl p R env Ab (forIn xs b f) Q s := by
  intro xs
  induction xs with
  | nil => intro b s h; exact Impl.pure_of (hend b s h)
  | cons x xs ih =>
    intro b s h
    rw [List.forIn_cons]
    apply Impl.bind
    refine Impl.mono_post ?_ _ _ (hstep x xs b s h)
    intro r s' hr
    cases r with
    | done b' => exact Impl.pure_of hr
    | yield b' => exact ih b' s' hr

end Services.Bootstrap.Acc
