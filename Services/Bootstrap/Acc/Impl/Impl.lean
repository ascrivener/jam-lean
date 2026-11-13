import Services.Bootstrap.Acc.Impl.Split
import Services.Bootstrap.ASem

/-!
# `Impl`: a run implements a `Spec.Prog AOp`

How bootstrap's accumulate code is related to `Spec.accumulate` (T2, `docs/bootstrap-target.md`).

**States.** A state is the PVM state (ı, ω, μ) with the context (x, y) ∈ 𝕃² and a queue of answers
(the gas values left that `gas` and `checkpoint` put in ω₇; see `Acc/ContractQ.lean`).

**`Impl R env prog Q s`: every run from s implements `prog`.** Every gas-free run under the contract
`R` from s does what `prog` does, by recursion on `prog`:
- **`pure a`**: the run reaches a state s' satisfying `Q a`, through host calls that keep (x, y)
  (`KeepCtx R`: `log`, `gas`, the reads).
- **`panic`**: the run ends ☇, keeping (x, y).
- **`call op k`**: the run reaches, keeping (x, y), a state s₁ from which:
  - if `ASem.step env op` gives (b, c′), it reaches a state s₂ with context c′ (op's SDK wrapper),
    and `Impl R env (k b) Q` holds from s₂;
  - if it gives `none`, the run ends ☇.

The statement is about every run, so it holds vacuously from a state with no run, for instance one
whose queue is too short. Every queue can then be handled, in particular the one of the real run of
Ψ_M (`psiM_of_freeRunH_accQ`).

**Composition.**
- `Impl.pre`: a prefix that keeps (x, y) can be added.
- `Impl.bind`: `Impl` along `Prog.bind`.
Segment lemmas (one run each, `FreeStepsH`) are used through `FreeRunH.of_steps`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Spec

/-- A run state: the PVM state, the context (x, y) and the queue of answers. -/
structure St where
  i : Nat
  ω : Regs
  μ : Memory
  c : AccCtx
  q : List Nat

/-- The steps of `R` that keep the context (x, y); the queue may change. -/
def KeepCtx (R : HostRel (AccCtx × List Nat)) : HostRel (AccCtx × List Nat) :=
  fun h ω μ xq s ω' μ' xq' => R h ω μ xq s ω' μ' xq' ∧ xq'.1 = xq.1

/-- s reaches s' under R. -/
def Reaches (p : ByteArray) (R : HostRel (AccCtx × List Nat)) (s s' : St) : Prop :=
  ∃ n, FreeStepsH p R s.i s.ω s.μ (s.c, s.q) s'.i s'.ω s'.μ (s'.c, s'.q) n

/-- A run from s ends with ε and context c'. -/
def Ends (p : ByteArray) (R : HostRel (AccCtx × List Nat)) (s : St) (ε : Status) (c' : AccCtx) : Prop :=
  ∃ ω' μ' q', FreeRunH p R s.i s.ω s.μ (s.c, s.q) ε ω' μ' (c', q')

/-- **Every run from s implements `prog`** (see the module docstring). -/
def Impl (p : ByteArray) (R : HostRel (AccCtx × List Nat)) (env : AccEnv) {α : Type} :
    Prog AOp α → (α → St → Prop) → St → Prop
  | .pure a, Q, s => ∀ ε c', Ends p R s ε c' →
      ∃ s', Reaches p (KeepCtx R) s s' ∧ s'.c = s.c ∧ Q a s'
  | .panic, _, s => ∀ ε c', Ends p R s ε c' → ε = .panic ∧ c' = s.c
  | .call op k, Q, s => ∀ ε c', Ends p R s ε c' →
      ∃ s₁, Reaches p (KeepCtx R) s s₁ ∧ s₁.c = s.c ∧
        match ASem.step env op s.c with
        | some (b, c₁) => ∃ s₂, Reaches p R s₁ s₂ ∧ s₂.c = c₁ ∧ Impl p R env (k b) Q s₂
        | none => ∀ ε' c'', Ends p R s₁ ε' c'' → ε' = .panic ∧ c'' = s.c

theorem Reaches.trans {p : ByteArray} {R : HostRel (AccCtx × List Nat)} {s s' s'' : St}
    (h₁ : Reaches p R s s') (h₂ : Reaches p R s' s'') : Reaches p R s s'' := by
  obtain ⟨n₁, h₁⟩ := h₁; obtain ⟨n₂, h₂⟩ := h₂; exact ⟨n₁ + n₂, h₁.trans h₂⟩

theorem Reaches.weaken {p : ByteArray} {R : HostRel (AccCtx × List Nat)} {s s' : St}
    (h : Reaches p (KeepCtx R) s s') : Reaches p R s s' := by
  obtain ⟨n, h⟩ := h; exact ⟨n, h.weaken fun _ _ _ _ _ _ _ hk => hk.1⟩

/-- A run from s that is known to reach s' continues from s' with the same end. -/
theorem Ends.of_reaches {p : ByteArray} {R : HostRel (AccCtx × List Nat)} (hR : R.Pins R)
    {s s' : St} {ε : Status} {c' : AccCtx} (hs : Reaches p R s s') (he : Ends p R s ε c') :
    Ends p R s' ε c' := by
  obtain ⟨n, hs⟩ := hs
  obtain ⟨ω', μ', q', hr⟩ := he
  exact ⟨ω', μ', q', FreeRunH.of_steps hR hs hr⟩

/-- **A prefix that keeps the context can be added.** -/
theorem Impl.pre {p : ByteArray} {R : HostRel (AccCtx × List Nat)} (hR : R.Pins R) {env : AccEnv} :
    ∀ {α : Type} (prog : Prog AOp α) (Q : α → St → Prop) {s s' : St},
    Reaches p (KeepCtx R) s s' → s'.c = s.c → Impl p R env prog Q s' → Impl p R env prog Q s := by
  intro α prog Q s s' hs hc h
  cases prog with
  | pure a =>
    intro ε c' he
    obtain ⟨s'', h1, h2, h3⟩ := h ε c' (he.of_reaches hR hs.weaken)
    exact ⟨s'', hs.trans h1, h2.trans hc, h3⟩
  | panic =>
    intro ε c' he
    obtain ⟨h1, h2⟩ := h ε c' (he.of_reaches hR hs.weaken)
    exact ⟨h1, h2.trans hc⟩
  | call op k =>
    intro ε c' he
    obtain ⟨s₁, h1, h2, h3⟩ := h ε c' (he.of_reaches hR hs.weaken)
    refine ⟨s₁, hs.trans h1, h2.trans hc, ?_⟩
    rw [hc] at h3
    exact h3

/-- `Impl` is a statement about every run: it holds if it holds whenever there is a run. -/
theorem Impl.of_ends {p : ByteArray} {R : HostRel (AccCtx × List Nat)} {env : AccEnv} {α : Type}
    (prog : Prog AOp α) (Q : α → St → Prop) (s : St)
    (h : ∀ ε c', Ends p R s ε c' → Impl p R env prog Q s) : Impl p R env prog Q s := by
  cases prog with
  | pure a => intro ε c' he; exact h ε c' he ε c' he
  | panic => intro ε c' he; exact h ε c' he ε c' he
  | call op k => intro ε c' he; exact h ε c' he ε c' he

/-- **`Impl` along `Prog.bind`**: implement p, then at each return a, implement `f a`. -/
theorem Impl.bind {p : ByteArray} {R : HostRel (AccCtx × List Nat)} (hR : R.Pins R) {env : AccEnv}
    {α β : Type} (f : α → Prog AOp β) (Q : β → St → Prop) :
    ∀ (prog : Prog AOp α) (s : St), Impl p R env prog (fun a s' => Impl p R env (f a) Q s') s →
      Impl p R env (Prog.bind prog f) Q s := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    refine Impl.of_ends (f a) Q s fun ε c' he => ?_
    obtain ⟨s', h1, h2, h3⟩ := h ε c' he
    exact Impl.pre hR (f a) Q h1 h2 h3
  | panic =>
    intro s h
    exact h
  | call op k ih =>
    intro s h ε c' he
    obtain ⟨s₁, h1, h2, h3⟩ := h ε c' he
    refine ⟨s₁, h1, h2, ?_⟩
    show match ASem.step env op s.c with
      | some (b, c₁) => ∃ s₂, Reaches p R s₁ s₂ ∧ s₂.c = c₁ ∧ Impl p R env ((k b).bind f) Q s₂
      | none => ∀ ε' c'', Ends p R s₁ ε' c'' → ε' = .panic ∧ c'' = s.c
    revert h3
    cases ASem.step env op s.c with
    | some bc =>
      intro h3
      obtain ⟨s₂, g1, g2, g3⟩ := h3
      exact ⟨s₂, g1, g2, ih bc.1 s₂ g3⟩
    | none => exact id

/-- What a run that ends with ε and context c' reports, as Ψ_A does (GP eq. `accinvocation`): x
    after a halt, else y. -/
def runOutcome (ε : Status) (c' : AccCtx) :
    PartialState × List DeferredTransfer × Option (List UInt8) × Provisions :=
  if ε = .halt then (c'.1.state, c'.1.xfers, c'.1.yield, c'.1.provisions)
  else (c'.2.state, c'.2.xfers, c'.2.yield, c'.2.provisions)

/-- **A run that implements a program reports what the program's `ASem` run does.** Suppose every
    run from s implements `prog`, each return of `prog` leads only to halts that keep the context
    (`hQ`), and a run from s ends with ε, context c'. Then some n operations of `ASem.run` give the
    same outcome. -/
theorem Impl.outcome {p : ByteArray} {R : HostRel (AccCtx × List Nat)} (hR : R.Pins R) {env : AccEnv}
    (Q : Unit → St → Prop) (hQ : ∀ s, Q () s → ∀ ε c', Ends p R s ε c' → ε = .halt ∧ c' = s.c) :
    ∀ (prog : Prog AOp Unit) (s : St) (ε : Status) (c' : AccCtx), Impl p R env prog Q s →
      Ends p R s ε c' → ∃ n, ASem.outcome (ASem.run n prog env s.c) = runOutcome ε c' := by
  intro prog
  induction prog with
  | pure a =>
    intro s ε c' h he
    obtain ⟨s', h1, h2, h3⟩ := h ε c' he
    obtain ⟨rfl, rfl⟩ := hQ s' h3 ε c' (he.of_reaches hR h1.weaken)
    refine ⟨0, ?_⟩
    simp [ASem.run, ASem.outcome, runOutcome, h2]
  | panic =>
    intro s ε c' h he
    obtain ⟨rfl, rfl⟩ := h ε c' he
    refine ⟨0, ?_⟩
    simp [ASem.run, ASem.outcome, runOutcome]
  | call op k ih =>
    intro s ε c' h he
    obtain ⟨s₁, h1, h2, h3⟩ := h ε c' he
    have he₁ := he.of_reaches hR h1.weaken
    revert h3
    cases hst : ASem.step env op s.c with
    | some bc =>
      intro h3
      obtain ⟨s₂, g1, g2, g3⟩ := h3
      obtain ⟨n, hn⟩ := ih bc.1 s₂ ε c' g3 (he₁.of_reaches hR g1)
      refine ⟨n + 1, ?_⟩
      simp only [ASem.run, hst]
      rw [← g2]; exact hn
    | none =>
      intro h3
      obtain ⟨rfl, rfl⟩ := h3 ε c' he₁
      refine ⟨1, ?_⟩
      simp [ASem.run, hst, ASem.outcome, runOutcome]

end Services.Bootstrap.Acc
