import PVM.Logic.Host

/-!
# Invariant rules for gas-free runs

Partial-correctness reasoning: pick an invariant over machine states that holds initially and is
preserved by every continuing step; then every way the run can end is an exit from a state
satisfying the invariant.

* `FreeRun.of_invariant` for Ψ (no host calls);
* `FreeRunH.of_invariant` for Ψ_H under a host contract: host calls must also preserve the
  invariant, using only what the contract guarantees.

Combined with `psi_freeRun` / `psiM_free`, these give properties of the real machine for every
amount of gas and, for Ψ_H/Ψ_M, every handler meeting the contract.
-/

namespace PVM

/-- Reachability by continuing gas-free steps. -/
inductive FreeReach (p : ByteArray) : Nat → Regs → Memory → Nat → Regs → Memory → Prop where
  | refl {i ω μ} : FreeReach p i ω μ i ω μ
  | step {i ω μ i' ω' μ' j ω'' μ''} : FreeNext p i ω μ i' ω' μ' → FreeReach p i' ω' μ' j ω'' μ'' →
      FreeReach p i ω μ j ω'' μ''

/-- A run is some continuing steps followed by an exit. -/
theorem FreeRun.decompose {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {ε : Status}
    {e : Nat} {ω' : Regs} {μ' : Memory} (h : FreeRun p i ω μ ε e ω' μ') :
    ∃ ωe μe, FreeReach p i ω μ e ωe μe ∧ FreeExit p e ωe μe ε ω' μ' := by
  induction h with
  | exit hx => exact ⟨_, _, .refl, hx⟩
  | next hn _ ih =>
    obtain ⟨ωe, μe, hr, hx⟩ := ih
    exact ⟨ωe, μe, .step hn hr, hx⟩

/-- An invariant preserved by continuing steps holds at every reachable state. -/
theorem FreeReach.invariant {p : ByteArray} (I : Nat → Regs → Memory → Prop)
    (hstep : ∀ i ω μ i' ω' μ', I i ω μ → FreeNext p i ω μ i' ω' μ' → I i' ω' μ')
    {i : Nat} {ω : Regs} {μ : Memory} {j : Nat} {ω' : Regs} {μ' : Memory}
    (h : FreeReach p i ω μ j ω' μ') (h0 : I i ω μ) : I j ω' μ' := by
  induction h with
  | refl => exact h0
  | step hn _ ih => exact ih (hstep _ _ _ _ _ _ h0 hn)

/-- **Invariant rule for Ψ.** If `I` holds initially, is preserved by continuing steps, and every
    exit from an `I`-state satisfies `Q`, then every gas-free run ends satisfying `Q`. -/
theorem FreeRun.of_invariant {p : ByteArray} (I : Nat → Regs → Memory → Prop)
    (Q : Status → Regs → Memory → Prop)
    (hstep : ∀ i ω μ i' ω' μ', I i ω μ → FreeNext p i ω μ i' ω' μ' → I i' ω' μ')
    (hexit : ∀ j ωj μj ε ω' μ', I j ωj μj → FreeExit p j ωj μj ε ω' μ' → Q ε ω' μ')
    {i : Nat} {ω : Regs} {μ : Memory} {ε : Status} {e : Nat} {ω' : Regs} {μ' : Memory}
    (h0 : I i ω μ) (h : FreeRun p i ω μ ε e ω' μ') : Q ε ω' μ' := by
  obtain ⟨ωe, μe, hr, hx⟩ := h.decompose
  exact hexit _ _ _ _ _ _ (hr.invariant I hstep h0) hx

variable {X : Type}

/-- **Invariant rule for Ψ_H under a host contract.** As `FreeRun.of_invariant`, with the context
    threaded through and two extra obligations: a host call that continues must re-establish
    `I` at ı + 1 + skip(ı), and one that stops must satisfy `Q`, in both cases for every effect the
    contract allows. -/
theorem FreeRunH.of_invariant {p : ByteArray} {R : HostRel X}
    (I : Nat → Regs → Memory → X → Prop) (Q : Status → Regs → Memory → X → Prop)
    (hstep : ∀ i ω μ x i' ω' μ', I i ω μ x → FreeNext p i ω μ i' ω' μ' → I i' ω' μ' x)
    (hexit : ∀ j ωj μj x ε ω' μ', I j ωj μj x → FreeExit p j ωj μj ε ω' μ' → (∀ h, ε ≠ .host h) →
      Q ε ω' μ' x)
    (hhost : ∀ j ωj μj x h ω' μ' ω'' μ'' x'', I j ωj μj x → FreeExit p j ωj μj (.host h) ω' μ' →
      R h.toNat ω' μ' x .cont ω'' μ'' x'' → I (blobNext p j) ω'' μ'' x'')
    (hstop : ∀ j ωj μj x h ω' μ' s ω'' μ'' x'', I j ωj μj x → FreeExit p j ωj μj (.host h) ω' μ' →
      R h.toNat ω' μ' x s ω'' μ'' x'' → s ≠ .cont → Q s.toStatus ω'' μ'' x'')
    {i : Nat} {ω : Regs} {μ : Memory} {x : X} {ε : Status} {ω' : Regs} {μ' : Memory} {x' : X}
    (h0 : I i ω μ x) (h : FreeRunH p R i ω μ x ε ω' μ' x') : Q ε ω' μ' x' := by
  induction h with
  | @exit _ _ _ x _ _ _ _ hrun hnh =>
    obtain ⟨ωe, μe, hr, hx⟩ := hrun.decompose
    exact hexit _ _ _ _ _ _ _ (hr.invariant (I · · · x) (fun _ _ _ _ _ _ hi hn => hstep _ _ _ _ _ _ _ hi hn) h0) hx hnh
  | @host _ _ _ x _ _ _ _ _ _ _ _ _ _ _ hrun hR _ ih =>
    obtain ⟨ωe, μe, hr, hx⟩ := hrun.decompose
    exact ih (hhost _ _ _ _ _ _ _ _ _ _
      (hr.invariant (I · · · x) (fun _ _ _ _ _ _ hi hn => hstep _ _ _ _ _ _ _ hi hn) h0) hx hR)
  | @hostStop _ _ _ x _ _ _ _ _ _ _ _ hrun hR hs =>
    obtain ⟨ωe, μe, hr, hx⟩ := hrun.decompose
    exact hstop _ _ _ _ _ _ _ _ _ _ _
      (hr.invariant (I · · · x) (fun _ _ _ _ _ _ hi hn => hstep _ _ _ _ _ _ _ hi hn) h0) hx hR hs

end PVM
