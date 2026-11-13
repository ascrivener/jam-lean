import PVM.Logic.StepsH

/-!
# A loop over a per-iteration step

Refine's transform loop (`Service::refine`'s `for` over the decoded instructions, GP v0.8.0 Appendix B.4,
Ψ_R running bootstrap's code) comes back to the same head ı after every instruction. Each handler gives
one step from the head to the head, which advances an invariant `Q k` to `Q (k + 1)`, or ends in a
terminal outcome `T`, such as heap exhaustion or a trap. `loop` puts n steps together. The host context x
may change from step to step (an `Export` adds segments).

`T` must be closed under running some steps first (`pre`) and under a looser bound (`mono`), as
`Decode.LoopA.Exhausts` is.
-/

namespace Services.Bootstrap.Refine.LoopG

open PVM

/-- **The loop.** With every step taking at most B, from `Q k` at the head, the remaining m = n − k
    iterations reach `Q n` at the head within m·B, or a terminal outcome. -/
theorem loop {X : Type} {p : ByteArray} {R : HostRel X} (l : Nat) (n B : Nat)
    (Q : Nat → Regs → Memory → X → Prop) (T : Nat → Regs → Memory → X → Nat → Prop)
    (pre : ∀ {i j : Nat} {ω ω1 : Regs} {μ μ1 : Memory} {x x1 : X} {a b : Nat},
      FreeStepsH p R i ω μ x j ω1 μ1 x1 a → T j ω1 μ1 x1 b → T i ω μ x (a + b))
    (mono : ∀ {i : Nat} {ω : Regs} {μ : Memory} {x : X} {a b : Nat}, T i ω μ x a → a ≤ b → T i ω μ x b)
    (step : ∀ k ω μ x, k < n → Q k ω μ x →
      (∃ ω' μ' x', FreeStepsH p R l ω μ x l ω' μ' x' B ∧ Q (k + 1) ω' μ' x') ∨ T l ω μ x B) :
    ∀ m k ω μ x, k + m = n → Q k ω μ x →
      (∃ ω' μ' x', FreeStepsH p R l ω μ x l ω' μ' x' (m * B) ∧ Q n ω' μ' x') ∨ T l ω μ x (m * B) := by
  intro m
  induction m with
  | zero =>
    intro k ω μ x hk q
    rw [show k = n by omega] at q
    exact Or.inl ⟨ω, μ, x, FreeStepsH.refl.mono (Nat.zero_le _), q⟩
  | succ m ih =>
    intro k ω μ x hk q
    have hb : (m + 1) * B = B + m * B := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rcases step k ω μ x (by omega) q with ⟨ω1, μ1, x1, run1, q1⟩ | ht
    · rcases ih (k + 1) ω1 μ1 x1 (by omega) q1 with ⟨ω', μ', x', run', q'⟩ | ht'
      · exact Or.inl ⟨ω', μ', x', hb ▸ run1.trans run', q'⟩
      · exact Or.inr (hb ▸ pre run1 ht')
    · exact Or.inr (mono ht (by rw [hb]; omega))

/-- **The whole loop**: from `Q 0`, `Q n` within n·B, or a terminal outcome. -/
theorem loop_all {X : Type} {p : ByteArray} {R : HostRel X} (l : Nat) (n B : Nat)
    (Q : Nat → Regs → Memory → X → Prop) (T : Nat → Regs → Memory → X → Nat → Prop)
    (pre : ∀ {i j : Nat} {ω ω1 : Regs} {μ μ1 : Memory} {x x1 : X} {a b : Nat},
      FreeStepsH p R i ω μ x j ω1 μ1 x1 a → T j ω1 μ1 x1 b → T i ω μ x (a + b))
    (mono : ∀ {i : Nat} {ω : Regs} {μ : Memory} {x : X} {a b : Nat}, T i ω μ x a → a ≤ b → T i ω μ x b)
    (step : ∀ k ω μ x, k < n → Q k ω μ x →
      (∃ ω' μ' x', FreeStepsH p R l ω μ x l ω' μ' x' B ∧ Q (k + 1) ω' μ' x') ∨ T l ω μ x B)
    (ω : Regs) (μ : Memory) (x : X) (q : Q 0 ω μ x) :
    (∃ ω' μ' x', FreeStepsH p R l ω μ x l ω' μ' x' (n * B) ∧ Q n ω' μ' x') ∨ T l ω μ x (n * B) :=
  loop l n B Q T pre mono step n 0 ω μ x (Nat.zero_add n) q

end Services.Bootstrap.Refine.LoopG
