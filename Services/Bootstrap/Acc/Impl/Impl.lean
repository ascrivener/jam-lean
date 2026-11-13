import Services.Bootstrap.Acc.Impl.Split
import Services.Bootstrap.Acc.Impl.StepSnd

/-!
# `Impl`: a run implements a `Spec.Prog AOp`

How bootstrap's accumulate code is related to `Spec.accumulate` (T2, `docs/bootstrap-target.md`).

**States.** A state is the PVM state (ı, ω, μ) with the context (x, y) ∈ 𝕃² and an answer queue `q : Qu`
(for `accContractS`, an infinite stream of the values `gas` and `checkpoint` put in ω₇).

**`Impl R env prog Q s`: a run from s implements `prog`.** By recursion on `prog`:
- **`pure a`**: the run reaches a state satisfying `Q a`, through host calls that keep (x, y)
  (`KeepCtx`).
- **`panic`**: the run ends ☇, keeping (x, y).
- **`call op k`**: the run reaches a state s₁, keeping (x, y). Then:
  - if `ASem.step env op` gives (b, c₁), the run reaches a state s₂ with context c₁ (op's SDK wrapper).
    On the way, y is always c.y or c₁.y (`YIn`). `Impl … (k b)` holds from s₂.
  - if it gives `none`, the run ends ☇, keeping (x, y).

**Consequences** (for `Q` = `Halts`, "the run halts, keeping (x, y)"):
- `Impl.run`: a run exists, and what it reports (x after a halt, y after ☇) is what some
  `ASem.run n` reports.
- `Impl.prefix` (in `Prefix.lean`): the out-of-gas case.
Composition: `Impl.pre`, `Impl.bind`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Spec

variable {Qu : Type}

/-- A run state: the PVM state, the context (x, y) and the answer queue. -/
structure St (Qu : Type) where
  i : Nat
  ω : Regs
  μ : Memory
  c : AccCtx
  q : Qu

/-- The steps of `R` that keep the context (x, y); the queue may change. -/
def KeepCtx (R : HostRel (AccCtx × Qu)) : HostRel (AccCtx × Qu) :=
  fun h ω μ xq s ω' μ' xq' => R h ω μ xq s ω' μ' xq' ∧ xq'.1 = xq.1

/-- The steps of `R` after which y is a or b: an operation's wrapper, from context c to c₁, passes
    only through y ∈ {c.y, c₁.y}, so running out of gas inside it reports one of them. -/
def YIn (R : HostRel (AccCtx × Qu)) (a b : JAM.Implications) : HostRel (AccCtx × Qu) :=
  fun h ω μ xq s ω' μ' xq' => R h ω μ xq s ω' μ' xq' ∧ (xq'.1.2 = a ∨ xq'.1.2 = b)

/-- s reaches s' under R. -/
def Reaches (p : ByteArray) (R : HostRel (AccCtx × Qu)) (s s' : St Qu) : Prop :=
  ∃ n, FreeStepsH p R s.i s.ω s.μ (s.c, s.q) s'.i s'.ω s'.μ (s'.c, s'.q) n

/-- A run from s ends with ε and context c'. -/
def Ends (p : ByteArray) (R : HostRel (AccCtx × Qu)) (s : St Qu) (ε : Status) (c' : AccCtx) : Prop :=
  ∃ ω' μ' q', FreeRunH p R s.i s.ω s.μ (s.c, s.q) ε ω' μ' (c', q')

/-- **A run from s implements `prog`** (see the module docstring). -/
def Impl (p : ByteArray) (R : HostRel (AccCtx × Qu)) (env : AccEnv) {α : Type} :
    Prog AOp α → (α → St Qu → Prop) → St Qu → Prop
  | .pure a, Q, s => ∃ s', Reaches p (KeepCtx R) s s' ∧ s'.c = s.c ∧ Q a s'
  | .panic, _, s => Ends p (KeepCtx R) s .panic s.c
  | .call op k, Q, s =>
      ∃ s₁, Reaches p (KeepCtx R) s s₁ ∧ s₁.c = s.c ∧
        match ASem.step env op s.c with
        | some (b, c₁) => ∃ s₂, Reaches p (YIn R s.c.2 c₁.2) s₁ s₂ ∧ s₂.c = c₁ ∧ Impl p R env (k b) Q s₂
        | none => Ends p (KeepCtx R) s₁ .panic s.c

/-- The run halts from s, keeping (x, y): the post-condition of the whole program. -/
def Halts (p : ByteArray) (R : HostRel (AccCtx × Qu)) (_ : Unit) (s : St Qu) : Prop :=
  Ends p (KeepCtx R) s .halt s.c

theorem Reaches.trans {p : ByteArray} {R : HostRel (AccCtx × Qu)} {s s' s'' : St Qu}
    (h₁ : Reaches p R s s') (h₂ : Reaches p R s' s'') : Reaches p R s s'' := by
  obtain ⟨n₁, h₁⟩ := h₁; obtain ⟨n₂, h₂⟩ := h₂; exact ⟨n₁ + n₂, h₁.trans h₂⟩

theorem Reaches.mono {p : ByteArray} {R R' : HostRel (AccCtx × Qu)} {s s' : St Qu}
    (hR : ∀ h ω μ x s ω' μ' x', R h ω μ x s ω' μ' x' → R' h ω μ x s ω' μ' x')
    (h : Reaches p R s s') : Reaches p R' s s' := by
  obtain ⟨n, h⟩ := h; exact ⟨n, h.weaken fun _ _ _ _ _ _ _ hk => hR _ _ _ _ _ _ _ _ hk⟩

/-- Steps before a run. -/
theorem FreeRunH.prepend {p : ByteArray} {R : HostRel (AccCtx × Qu)} {i ω μ x i' ω' μ' x' n ε ω'' μ'' x''}
    (hs : FreeStepsH p R i ω μ x i' ω' μ' x' n) (hr : FreeRunH p R i' ω' μ' x' ε ω'' μ'' x'') :
    FreeRunH p R i ω μ x ε ω'' μ'' x'' := by
  induction hs with
  | refl => exact hr
  | pad _ ih => exact ih hr
  | next hn _ _ ih => exact (ih hr).cons_next hn
  | host hP _ hst hRs _ ih =>
    have he := FreeRun.exit (FreeExit.step hP hst (by simp))
    simp only [show ¬((Status.host _ : Status) = .halt ∨ (Status.host _ : Status) = .panic) by simp,
      ite_false] at he
    refine .host he hRs ?_
    rw [blobNext_of_deblob hP]
    exact ih hr

theorem Ends.prepend {p : ByteArray} {R : HostRel (AccCtx × Qu)} {s s' : St Qu} {ε : Status} {c' : AccCtx}
    (hs : Reaches p R s s') (he : Ends p R s' ε c') : Ends p R s ε c' := by
  obtain ⟨n, hs⟩ := hs; obtain ⟨ω', μ', q', hr⟩ := he
  exact ⟨ω', μ', q', FreeRunH.prepend hs hr⟩

theorem FreeRunH.unkeep {p : ByteArray} {R : HostRel (AccCtx × Qu)} {i ω μ x ε ω' μ' x'}
    (h : FreeRunH p (KeepCtx R) i ω μ x ε ω' μ' x') : FreeRunH p R i ω μ x ε ω' μ' x' := by
  induction h with
  | exit hr hne => exact .exit hr hne
  | host hr hR _ ih => exact .host hr hR.1 ih
  | hostStop hr hR hs => exact .hostStop hr hR.1 hs

theorem Ends.weaken {p : ByteArray} {R : HostRel (AccCtx × Qu)} {s : St Qu} {ε : Status} {c' : AccCtx}
    (h : Ends p (KeepCtx R) s ε c') : Ends p R s ε c' := by
  obtain ⟨ω', μ', q', h⟩ := h
  exact ⟨ω', μ', q', FreeRunH.unkeep h⟩

/-- **A prefix that keeps the context can be added.** -/
theorem Impl.pre {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {α : Type}
    (prog : Prog AOp α) (Q : α → St Qu → Prop) {s s' : St Qu}
    (hs : Reaches p (KeepCtx R) s s') (hc : s'.c = s.c) (h : Impl p R env prog Q s') :
    Impl p R env prog Q s := by
  cases prog with
  | pure a =>
    obtain ⟨s'', h1, h2, h3⟩ := h
    exact ⟨s'', hs.trans h1, h2.trans hc, h3⟩
  | panic =>
    have : Ends p (KeepCtx R) s' .panic s'.c := h
    rw [hc] at this
    exact Ends.prepend hs this
  | call op k =>
    unfold Impl at h ⊢
    obtain ⟨s₁, h1, h2, h3⟩ := h
    refine ⟨s₁, hs.trans h1, h2.trans hc, ?_⟩
    rw [← hc]
    exact h3

/-- **`Impl` along `Prog.bind`**: implement p, then at each return a, implement `f a`. -/
theorem Impl.bind {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv}
    {α β : Type} (f : α → Prog AOp β) (Q : β → St Qu → Prop) :
    ∀ (prog : Prog AOp α) (s : St Qu), Impl p R env prog (fun a s' => Impl p R env (f a) Q s') s →
      Impl p R env (Prog.bind prog f) Q s := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    obtain ⟨s', h1, h2, h3⟩ := h
    exact Impl.pre (f a) Q h1 h2 h3
  | panic => intro s h; exact h
  | call op k ih =>
    intro s h
    unfold Impl at h
    obtain ⟨s₁, h1, h2, h3⟩ := h
    show Impl p R env (Prog.call op (fun b => (k b).bind f)) Q s
    unfold Impl
    refine ⟨s₁, h1, h2, ?_⟩
    show match ASem.step env op s.c with
      | some (b, c₁) => ∃ s₂, Reaches p (YIn R s.c.2 c₁.2) s₁ s₂ ∧ s₂.c = c₁ ∧
          Impl p R env ((k b).bind f) Q s₂
      | none => Ends p (KeepCtx R) s₁ .panic s.c
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

/-- **A run exists, and it reports what some `ASem.run n` reports.** -/
theorem Impl.run {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} :
    ∀ (prog : Prog AOp Unit) (s : St Qu), Impl p R env prog (Halts p R) s →
      ∃ ε c', Ends p R s ε c' ∧ ∃ n, ASem.outcome (ASem.run n prog env s.c) = runOutcome ε c' := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    obtain ⟨s', h1, h2, h3⟩ := h
    have h3' : Ends p R s' .halt s'.c := Ends.weaken h3
    rw [h2] at h3'
    refine ⟨.halt, s.c, Ends.prepend (h1.mono fun _ _ _ _ _ _ _ _ h => h.1) h3', 0, ?_⟩
    simp [ASem.run, ASem.outcome, runOutcome]
  | panic =>
    intro s h
    refine ⟨.panic, s.c, Ends.weaken h, 0, ?_⟩
    simp [ASem.run, ASem.outcome, runOutcome]
  | call op k ih =>
    intro s h
    unfold Impl at h
    obtain ⟨s₁, h1, h2, h3⟩ := h
    have h1' : Reaches p R s s₁ := h1.mono fun _ _ _ _ _ _ _ _ h => h.1
    revert h3
    cases hst : ASem.step env op s.c with
    | some bc =>
      intro h3
      obtain ⟨s₂, g1, g2, g3⟩ := h3
      obtain ⟨ε, c', he, n, hn⟩ := ih bc.1 s₂ g3
      refine ⟨ε, c', Ends.prepend (h1'.trans (g1.mono fun _ _ _ _ _ _ _ _ h => h.1)) he, n + 1, ?_⟩
      simp only [ASem.run, hst]
      rw [← g2]; exact hn
    | none =>
      intro h3
      have h3' : Ends p R s₁ .panic s.c := Ends.weaken h3
      refine ⟨.panic, s.c, Ends.prepend h1' h3', 1, ?_⟩
      simp [ASem.run, hst, ASem.outcome, runOutcome]

end Services.Bootstrap.Acc
