import PVM.Logic.Host

/-!
# Gas-free runs are deterministic

`FreeRun`s from one state all end the same way: deblob and the gas-free step are functions, so a
run cannot branch. The same holds for `FreeRunH` under a contract that allows at most one outcome
per host call (`HostRel.Functional`).

So a proof that exhibits *one* gas-free run from a program's initial state to an exit has
determined the exit of *every* run from there, in particular of Ψ and Ψ_H whenever they do not
run out of gas (`psiHStar_eq_of_freeRunH`).
-/

namespace PVM

theorem FreeExit.not_next {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {ε : Status}
    {ω' : Regs} {μ' : Memory} {i'' : Nat} {ω'' : Regs} {μ'' : Memory}
    (he : FreeExit p i ω μ ε ω' μ') (hn : FreeNext p i ω μ i'' ω'' μ'') : False := by
  obtain ⟨P, hP, hs⟩ := hn
  cases he with
  | invalid h => rw [hP] at h; cases h
  | step h hs' hne =>
    rw [hP] at h; cases h
    rw [hs] at hs'; cases hs'; exact hne rfl

theorem FreeExit.det {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {ε₁ ε₂ : Status}
    {ω₁ ω₂ : Regs} {μ₁ μ₂ : Memory}
    (h₁ : FreeExit p i ω μ ε₁ ω₁ μ₁) (h₂ : FreeExit p i ω μ ε₂ ω₂ μ₂) :
    ε₁ = ε₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ := by
  cases h₁ with
  | invalid h =>
    cases h₂ with
    | invalid _ => exact ⟨rfl, rfl, rfl⟩
    | step h' _ _ => rw [h] at h'; cases h'
  | step h hs hne =>
    cases h₂ with
    | invalid h' => rw [h] at h'; cases h'
    | step h' hs' _ =>
      rw [h] at h'; cases h'
      rw [hs] at hs'; cases hs'
      exact ⟨rfl, rfl, rfl⟩

theorem FreeNext.det {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {i₁ i₂ : Nat}
    {ω₁ ω₂ : Regs} {μ₁ μ₂ : Memory}
    (h₁ : FreeNext p i ω μ i₁ ω₁ μ₁) (h₂ : FreeNext p i ω μ i₂ ω₂ μ₂) :
    i₁ = i₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ := by
  obtain ⟨P, hP, hs⟩ := h₁
  obtain ⟨P', hP', hs'⟩ := h₂
  rw [hP] at hP'; cases hP'
  rw [hs] at hs'; cases hs'
  exact ⟨rfl, rfl, rfl⟩

/-- **Gas-free runs are deterministic.** -/
theorem FreeRun.det {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {ε₁ ε₂ : Status}
    {e₁ e₂ : Nat} {ω₁ ω₂ : Regs} {μ₁ μ₂ : Memory}
    (h₁ : FreeRun p i ω μ ε₁ e₁ ω₁ μ₁) (h₂ : FreeRun p i ω μ ε₂ e₂ ω₂ μ₂) :
    ε₁ = ε₂ ∧ e₁ = e₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ := by
  induction h₁ generalizing ε₂ e₂ ω₂ μ₂ with
  | exit he =>
    cases h₂ with
    | exit he' => obtain ⟨a, b, c⟩ := he.det he'; exact ⟨a, rfl, b, c⟩
    | next hn _ => exact (he.not_next hn).elim
  | next hn _ ih =>
    cases h₂ with
    | exit he' => exact (he'.not_next hn).elim
    | next hn' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := hn.det hn'
      exact ih hr'

variable {X : Type}

/-- Two runs that stop at the same host call (index, id, state) agree on what precedes it. -/
theorem FreeRun.det_host {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {h₁ h₂ : UInt64}
    {e₁ e₂ : Nat} {ω₁ ω₂ : Regs} {μ₁ μ₂ : Memory}
    (h₁r : FreeRun p i ω μ (.host h₁) e₁ ω₁ μ₁) (h₂r : FreeRun p i ω μ (.host h₂) e₂ ω₂ μ₂) :
    h₁ = h₂ ∧ e₁ = e₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ := by
  obtain ⟨hh, he, hω, hμ⟩ := h₁r.det h₂r
  cases hh; exact ⟨rfl, he, hω, hμ⟩

/-- Contract `R₁` pins down `R₂`: wherever `R₁` allows an outcome, `R₂` allows no other. -/
def HostRel.Pins (R₁ R₂ : HostRel X) : Prop :=
  ∀ h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂, R₁ h ω μ x s₁ ω₁ μ₁ x₁ → R₂ h ω μ x s₂ ω₂ μ₂ x₂ →
    s₁ = s₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ ∧ x₁ = x₂

/-- **Gas-free runs with host calls are deterministic**: a run under `R₁` and a run under `R₂`
    from the same state end the same way, if `R₁` pins down `R₂`. -/
theorem FreeRunH.det {p : ByteArray} {R₁ R₂ : HostRel X} (hR : R₁.Pins R₂) {i : Nat}
    {ω : Regs} {μ : Memory} {x : X} {ε₁ ε₂ : Status} {ω₁ ω₂ : Regs} {μ₁ μ₂ : Memory} {x₁ x₂ : X}
    (h₁ : FreeRunH p R₁ i ω μ x ε₁ ω₁ μ₁ x₁) (h₂ : FreeRunH p R₂ i ω μ x ε₂ ω₂ μ₂ x₂) :
    ε₁ = ε₂ ∧ ω₁ = ω₂ ∧ μ₁ = μ₂ ∧ x₁ = x₂ := by
  induction h₁ generalizing ε₂ ω₂ μ₂ x₂ with
  | exit hr hne =>
    cases h₂ with
    | exit hr' _ => obtain ⟨a, _, b, c⟩ := hr.det hr'; exact ⟨a, b, c, rfl⟩
    | host hr' _ _ => obtain ⟨a, _⟩ := hr.det hr'; exact absurd a (hne _)
    | hostStop hr' _ _ => obtain ⟨a, _⟩ := hr.det hr'; exact absurd a (hne _)
  | host hr hR1 _ ih =>
    cases h₂ with
    | exit hr' hne' => obtain ⟨a, _⟩ := hr.det hr'; exact absurd a.symm (hne' _)
    | host hr' hR2 hrest =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr.det_host hr'
      obtain ⟨_, rfl, rfl, rfl⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
      exact ih hrest
    | hostStop hr' hR2 hs =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr.det_host hr'
      obtain ⟨hc, _⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
      exact absurd hc.symm hs
  | hostStop hr hR1 hs =>
    cases h₂ with
    | exit hr' hne' => obtain ⟨a, _⟩ := hr.det hr'; exact absurd a.symm (hne' _)
    | host hr' hR2 _ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr.det_host hr'
      obtain ⟨hc, _⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
      exact absurd hc hs
    | hostStop hr' hR2 _ =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr.det_host hr'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
      exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Determining Ψ_M by one gas-free run -/

/-- The outcomes a handler can produce for some amount of gas, other than ∞: the contract a
    gas-free run of the real handler satisfies when it does not run out. -/
def HostFn.graph (f : HostFn X) : HostRel X := fun h ω μ x s ω' μ' x' =>
  s ≠ .oog ∧ ∃ g, f h g ω μ x = ⟨s, (f h g ω μ x).gas, ω', μ', x'⟩

theorem FreeRunH.to_graph {p : ByteArray} {f : HostFn X} {i : Nat} {ω : Regs} {μ : Memory}
    {x : X} {ε : Status} {ω' : Regs} {μ' : Memory} {x' : X}
    (h : FreeRunH p (fun h ω μ x s ω' μ' x' => ∃ g, f h g ω μ x = ⟨s, (f h g ω μ x).gas, ω', μ', x'⟩)
      i ω μ x ε ω' μ' x') (hε : ε ≠ .oog) :
    FreeRunH p f.graph i ω μ x ε ω' μ' x' := by
  induction h with
  | exit hr hne => exact .exit hr hne
  | host hr hR _ ih => exact .host hr ⟨by simp, hR⟩ (ih hε)
  | hostStop hr hR hs =>
    refine .hostStop hr ⟨fun ho => hε (by rw [ho]; rfl), hR⟩ hs

/-- **Ψ_M is determined by one gas-free run.** If, from Y's initial state, some run under a
    contract that pins down the handler's (non-∞) outcomes exits with ε, then Ψ_M either runs out
    of gas or returns exactly that run's output and context. -/
theorem psiM_of_freeRunH (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    (f : HostFn X) (hf : f.GasNonIncreasing) (R : HostRel X) (hR : R.Pins f.graph)
    {p : ByteArray} {ω : Regs} {μ : Memory} (hY : standardInit b a = some (p, ω, μ))
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : X} (hrun : FreeRunH p R i ω μ x ε ω' μ' x') :
    (psiM b i gas a f x).2.1.isOog = true ∨ (psiM b i gas a f x).2 = (freeOutput ε ω' μ', x') := by
  cases hno : (psiM b i gas a f x).2.1.isOog
  · right
    let G : HostRel X := fun h ω μ x s ω' μ' x' =>
      ∃ g, f h g ω μ x = ⟨s, (f h g ω μ x).gas, ω', μ', x'⟩
    have hresp : f.Respects G := fun h g ω μ x => ⟨g, rfl⟩
    rcases psiM_free b i gas a x G f hf hresp hno with ⟨hY', _⟩ | ⟨p', ω₀, μ₀, ε', ω'', μ'', x'', hY', hrun', hout⟩
    · rw [hY] at hY'; cases hY'
    · rw [hY] at hY'; cases hY'
      have hε' : ε' ≠ .oog := by
        intro he; rw [hout] at hno; simp [freeOutput, he, InvOutput.isOog] at hno
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hrun.det hR (hrun'.to_graph hε')
      exact hout
  · left; rfl

end PVM
