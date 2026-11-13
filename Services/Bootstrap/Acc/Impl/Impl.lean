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
- **Early ☇, for a listed reason.** For `pure` and `call`, the run may instead reach a state where
  the reason predicate `Ab` holds and then end ☇ keeping (x, y); inside an operation's wrapper it may
  do so with y ∈ {c.y, c₁.y} (`Aborts`). `Ab` is a parameter: for accumulate, heap exhaustion and
  the named quirks. Ψ_A then reports y (GP eq. `accinvocation`), and `Impl.run` says a reason held.

**Consequences** (for `Q` = `Halts`, "the run halts, keeping (x, y)"):
- `Impl.run` (in `Prefix.lean`): a run exists, and what it reports (x after a halt, y after ☇)
  is what some `ASem.run n` reports, or the y it started with.
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

/-- **An early ☇ for an allowed reason**: the run from s reaches a state s' where the reason `Ab`
    holds, and from there ends ☇ with context c'. -/
def Aborts (p : ByteArray) (R : HostRel (AccCtx × Qu)) (Ab : St Qu → Prop) (s : St Qu) (c' : AccCtx) :
    Prop :=
  ∃ s', Reaches p R s s' ∧ Ab s' ∧ Ends p R s' .panic c'

/-- **A run from s implements `prog`** (see the module docstring). `Ab` lists the reasons an early ☇
    may have. -/
def Impl (p : ByteArray) (R : HostRel (AccCtx × Qu)) (env : AccEnv) (Ab : St Qu → Prop) {α : Type} :
    Prog AOp α → (α → St Qu → Prop) → St Qu → Prop
  | .pure a, Q, s => Aborts p (KeepCtx R) Ab s s.c ∨
      ∃ s', Reaches p (KeepCtx R) s s' ∧ s'.c = s.c ∧ Q a s'
  | .panic, _, s => Ends p (KeepCtx R) s .panic s.c
  | .call op k, Q, s => Aborts p (KeepCtx R) Ab s s.c ∨
      ∃ s₁, Reaches p (KeepCtx R) s s₁ ∧ s₁.c = s.c ∧
        match ASem.step env op s.c with
        | some (b, c₁) =>
            (∃ c', (c'.2 = s.c.2 ∨ c'.2 = c₁.2) ∧ Aborts p (YIn R s.c.2 c₁.2) Ab s₁ c') ∨
            ∃ s₂, Reaches p (YIn R s.c.2 c₁.2) s₁ s₂ ∧ s₂.c = c₁ ∧ Impl p R env Ab (k b) Q s₂
        | none => Ends p (KeepCtx R) s₁ .panic s.c

/-- The run halts from s, keeping (x, y), with ω₈ = 0 (an empty output, so Ψ_A takes no yield
    from it): the post-condition of the whole program. -/
def Halts (p : ByteArray) (R : HostRel (AccCtx × Qu)) (_ : Unit) (s : St Qu) : Prop :=
  ∃ ω' μ' q', FreeRunH p (KeepCtx R) s.i s.ω s.μ (s.c, s.q) .halt ω' μ' (s.c, q') ∧ (ω'.get 8).toNat = 0

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

theorem FreeRunH.mono {p : ByteArray} {R R' : HostRel (AccCtx × Qu)}
    (hR : ∀ h ω μ x s ω' μ' x', R h ω μ x s ω' μ' x' → R' h ω μ x s ω' μ' x') {i ω μ x ε ω' μ' x'}
    (h : FreeRunH p R i ω μ x ε ω' μ' x') : FreeRunH p R' i ω μ x ε ω' μ' x' := by
  induction h with
  | exit hr hne => exact .exit hr hne
  | host hr hR' _ ih => exact .host hr (hR _ _ _ _ _ _ _ _ hR') ih
  | hostStop hr hR' hs => exact .hostStop hr (hR _ _ _ _ _ _ _ _ hR') hs

theorem Ends.weaken {p : ByteArray} {R : HostRel (AccCtx × Qu)} {s : St Qu} {ε : Status} {c' : AccCtx}
    (h : Ends p (KeepCtx R) s ε c') : Ends p R s ε c' := by
  obtain ⟨ω', μ', q', h⟩ := h
  exact ⟨ω', μ', q', FreeRunH.unkeep h⟩

theorem Aborts.prepend {p : ByteArray} {R : HostRel (AccCtx × Qu)} {Ab : St Qu → Prop} {s s' : St Qu}
    {c' : AccCtx} (hs : Reaches p R s s') (h : Aborts p R Ab s' c') : Aborts p R Ab s c' := by
  obtain ⟨s'', h1, h2, h3⟩ := h
  exact ⟨s'', hs.trans h1, h2, h3⟩

theorem Aborts.ends {p : ByteArray} {R : HostRel (AccCtx × Qu)} {Ab : St Qu → Prop} {s : St Qu}
    {c' : AccCtx} (h : Aborts p R Ab s c') : Ends p R s .panic c' := by
  obtain ⟨s', h1, -, h3⟩ := h
  exact Ends.prepend h1 h3

/-- **An early ☇ for an allowed reason, keeping (x, y), implements every program.** -/
theorem Impl.abort {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop} {α : Type}
    (prog : Prog AOp α) (Q : α → St Qu → Prop) {s : St Qu} (h : Aborts p (KeepCtx R) Ab s s.c) :
    Impl p R env Ab prog Q s := by
  cases prog with
  | pure a => exact .inl h
  | panic => exact h.ends
  | call op k => unfold Impl; exact .inl h

/-- **A prefix that keeps the context can be added.** -/
theorem Impl.pre {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop} {α : Type}
    (prog : Prog AOp α) (Q : α → St Qu → Prop) {s s' : St Qu}
    (hs : Reaches p (KeepCtx R) s s') (hc : s'.c = s.c) (h : Impl p R env Ab prog Q s') :
    Impl p R env Ab prog Q s := by
  cases prog with
  | pure a =>
    rcases h with h | ⟨s'', h1, h2, h3⟩
    · rw [hc] at h; exact .inl (Aborts.prepend hs h)
    · exact .inr ⟨s'', hs.trans h1, h2.trans hc, h3⟩
  | panic =>
    have : Ends p (KeepCtx R) s' .panic s'.c := h
    rw [hc] at this
    exact Ends.prepend hs this
  | call op k =>
    unfold Impl at h ⊢
    rcases h with h | ⟨s₁, h1, h2, h3⟩
    · rw [hc] at h; exact .inl (Aborts.prepend hs h)
    refine .inr ⟨s₁, hs.trans h1, h2.trans hc, ?_⟩
    rw [← hc]
    exact h3

/-- **`Impl` along `Prog.bind`**: implement p, then at each return a, implement `f a`. -/
theorem Impl.bind {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α β : Type} (f : α → Prog AOp β) (Q : β → St Qu → Prop) :
    ∀ (prog : Prog AOp α) (s : St Qu), Impl p R env Ab prog (fun a s' => Impl p R env Ab (f a) Q s') s →
      Impl p R env Ab (Prog.bind prog f) Q s := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    rcases h with h | ⟨s', h1, h2, h3⟩
    · exact Impl.abort (f a) Q h
    · exact Impl.pre (f a) Q h1 h2 h3
  | panic => intro s h; exact h
  | call op k ih =>
    intro s h
    unfold Impl at h
    show Impl p R env Ab (Prog.call op (fun b => (k b).bind f)) Q s
    unfold Impl
    rcases h with h | ⟨s₁, h1, h2, h3⟩
    · exact .inl h
    refine .inr ⟨s₁, h1, h2, ?_⟩
    show match ASem.step env op s.c with
      | some (b, c₁) =>
          (∃ c', (c'.2 = s.c.2 ∨ c'.2 = c₁.2) ∧ Aborts p (YIn R s.c.2 c₁.2) Ab s₁ c') ∨
          ∃ s₂, Reaches p (YIn R s.c.2 c₁.2) s₁ s₂ ∧ s₂.c = c₁ ∧ Impl p R env Ab ((k b).bind f) Q s₂
      | none => Ends p (KeepCtx R) s₁ .panic s.c
    revert h3
    cases ASem.step env op s.c with
    | some bc =>
      intro h3
      rcases h3 with h3 | ⟨s₂, g1, g2, g3⟩
      · exact .inl h3
      · exact .inr ⟨s₂, g1, g2, ih bc.1 s₂ g3⟩
    | none => exact id

end Services.Bootstrap.Acc
