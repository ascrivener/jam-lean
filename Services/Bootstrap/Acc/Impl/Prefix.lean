import Services.Bootstrap.Acc.Impl.Impl

/-!
# Prefixes of a run, for the out-of-gas case

When Ψ_M runs out of gas, Ψ_A reports y (GP eq. `accinvocation`), and the context it holds is the
context at the last host call that continued. `Pre R s c'` says a run from s reaches context c'
through host calls that continue.

`Impl.prefix`: if a run from s implements `prog` and the contract pins itself, then every such
c' has a y that some `ASem.run n` reports (`stopped` or otherwise), or the y s started with. Two
facts make this work:
- y changes only inside an operation's wrapper, and there it is c.y or c₁.y (`YIn`);
- an operation keeps y, or leaves (x, x) (`ASem.step_snd`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Spec

variable {Qu : Type}

/-- A run from s reaches the context c' through host calls that continue. -/
inductive Pre (p : ByteArray) (R : HostRel (AccCtx × Qu)) : St Qu → AccCtx → Prop where
  | here (s : St Qu) : Pre p R s s.c
  | host {s : St Qu} {h : UInt64} {e : Nat} {ω' : Regs} {μ' : Memory} {ω'' : Regs} {μ'' : Memory}
      {c'' : AccCtx} {q'' : Qu} {c₀ : AccCtx} :
      FreeRun p s.i s.ω s.μ (.host h) e ω' μ' → R h.toNat ω' μ' (s.c, s.q) .cont ω'' μ'' (c'', q'') →
      Pre p R ⟨blobNext p e, ω'', μ'', c'', q''⟩ c₀ → Pre p R s c₀

/-- A prefix from a state with a continuing step continues after it. -/
theorem Pre.uncons_next {p : ByteArray} {R : HostRel (AccCtx × Qu)} {s : St Qu} {i' : Nat} {ω' : Regs}
    {μ' : Memory} {c₀ : AccCtx} (hn : FreeNext p s.i s.ω s.μ i' ω' μ') (hp : Pre p R s c₀) :
    c₀ = s.c ∨ Pre p R ⟨i', ω', μ', s.c, s.q⟩ c₀ := by
  cases hp with
  | here => exact .inl rfl
  | host hr hR hrest => exact .inr (.host (hr.uncons_next hn) hR hrest)

/-- **A prefix along a known segment**: if every step of the segment keeps the invariant I, then a
    prefix from its start either ends inside the segment (with I) or continues from its end. -/
theorem Pre.split {p : ByteArray} {R R' : HostRel (AccCtx × Qu)} (hR : R.Pins R)
    (hR' : ∀ h ω μ x s ω' μ' x', R' h ω μ x s ω' μ' x' → R h ω μ x s ω' μ' x')
    (I : AccCtx → Prop) (hI : ∀ h ω μ x s ω' μ' x', R' h ω μ x s ω' μ' x' → I x.1 → I x'.1) :
    ∀ {i ω μ xq i₁ ω₁ μ₁ xq₁ n}, FreeStepsH p R' i ω μ xq i₁ ω₁ μ₁ xq₁ n → I xq.1 →
      ∀ {c₀}, Pre p R ⟨i, ω, μ, xq.1, xq.2⟩ c₀ → I c₀ ∨ Pre p R ⟨i₁, ω₁, μ₁, xq₁.1, xq₁.2⟩ c₀ := by
  intro i ω μ xq i₁ ω₁ μ₁ xq₁ n hs
  induction hs with
  | refl => intro _ _ hp; exact .inr hp
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    intro hI0 c₀ hp
    rcases hp.uncons_next hn with h | h
    · exact .inl (h ▸ hI0)
    · exact ih hI0 h
  | host hP _ hst hRs _ ih =>
    intro hI0 c₀ hp
    cases hp with
    | here => exact .inl hI0
    | host hrun hR'' hrest =>
      obtain ⟨hh, he, hω, hμ⟩ := FreeRun.at_host hP hst hrun
      cases hh; subst he; subst hω; subst hμ
      obtain ⟨-, rfl, rfl, rfl⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ (hR' _ _ _ _ _ _ _ _ hRs) hR''
      rw [blobNext_of_deblob hP] at hrest
      exact ih (hI _ _ _ _ _ _ _ _ hRs hI0) hrest

/-- **A prefix along a known complete run** stays inside it: if every step keeps I, it ends with I. -/
theorem Pre.split_run {p : ByteArray} {R R' : HostRel (AccCtx × Qu)} (hR : R.Pins R)
    (hR' : ∀ h ω μ x s ω' μ' x', R' h ω μ x s ω' μ' x' → R h ω μ x s ω' μ' x')
    (I : AccCtx → Prop) (hI : ∀ h ω μ x s ω' μ' x', R' h ω μ x s ω' μ' x' → I x.1 → I x'.1) :
    ∀ {i ω μ xq ε ω' μ' xq'}, FreeRunH p R' i ω μ xq ε ω' μ' xq' → I xq.1 →
      ∀ {c₀}, Pre p R ⟨i, ω, μ, xq.1, xq.2⟩ c₀ → I c₀ := by
  intro i ω μ xq ε ω' μ' xq' hr
  induction hr with
  | exit hrun hne =>
    intro hI0 c₀ hp
    cases hp with
    | here => exact hI0
    | host hrun' _ _ =>
      obtain ⟨a, _⟩ := hrun.det hrun'
      exact (hne _ a).elim
  | host hrun hR1 _ ih =>
    intro hI0 c₀ hp
    cases hp with
    | here => exact hI0
    | host hrun' hR2 hrest =>
      obtain ⟨hh, he, hω, hμ⟩ := hrun.det_host hrun'
      cases hh; subst he; subst hω; subst hμ
      obtain ⟨-, rfl, rfl, rfl⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ (hR' _ _ _ _ _ _ _ _ hR1) hR2
      exact ih (hI _ _ _ _ _ _ _ _ hR1 hI0) hrest
  | hostStop hrun hR1 hs =>
    intro hI0 c₀ hp
    cases hp with
    | here => exact hI0
    | host hrun' hR2 hrest =>
      obtain ⟨hh, he, hω, hμ⟩ := hrun.det_host hrun'
      cases hh; subst he; subst hω; subst hμ
      obtain ⟨hs1, -⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ (hR' _ _ _ _ _ _ _ _ hR1) hR2
      exact (hs hs1).elim

/-- What y reports. -/
def yOutcome (y : JAM.Implications) :
    PartialState × List DeferredTransfer × Option (List UInt8) × Provisions :=
  (y.state, y.xfers, y.yield, y.provisions)

theorem outcome_stopped (c : AccCtx) {s : ASem.Stop} (hs : s ≠ .done) :
    ASem.outcome (s, c) = yOutcome c.2 := by
  cases s <;> first | exact absurd rfl hs | rfl

/-- After one operation that left (x, x), every `ASem.run` reports y. -/
theorem run_xx (env : AccEnv) (prog : Prog AOp Unit) (x : JAM.Implications) :
    ASem.outcome (ASem.run 0 prog env (x, x)) = yOutcome x := by
  cases prog <;> rfl

/-- **The out-of-gas case.** If a run from s implements `prog` (under a self-pinning contract),
    every context c₀ it reaches at a host call has the y s started with, or a y that some
    `ASem.run n` reports. -/
theorem Impl.prefix {p : ByteArray} {R : HostRel (AccCtx × Qu)} (hR : R.Pins R) {env : AccEnv} :
    ∀ (prog : Prog AOp Unit) (s : St Qu), Impl p R env prog (Halts p R) s →
      ∀ c₀, Pre p R s c₀ → c₀.2 = s.c.2 ∨ ∃ n, ASem.outcome (ASem.run n prog env s.c) = yOutcome c₀.2 := by
  have keepR : ∀ h ω μ x s ω' μ' x', KeepCtx R h ω μ x s ω' μ' x' → R h ω μ x s ω' μ' x' :=
    fun _ _ _ _ _ _ _ _ h => h.1
  have keepI : ∀ (c : AccCtx) h ω μ (x : AccCtx × Qu) s ω' μ' (x' : AccCtx × Qu),
      KeepCtx R h ω μ x s ω' μ' x' → x.1 = c → x'.1 = c := fun _ _ _ _ _ _ _ _ _ h hc => h.2.trans hc
  intro prog
  induction prog with
  | pure a =>
    intro s h c₀ hp
    obtain ⟨s', ⟨n, h1⟩, h2, ω', μ', q', h3, -⟩ := h
    rcases Pre.split hR keepR (fun c => c = s.c) (keepI s.c) h1 rfl hp with hc | hp'
    · exact .inl (by rw [hc])
    · have := Pre.split_run hR keepR (fun c => c = s'.c) (keepI s'.c) h3 rfl hp'
      exact .inl (by rw [this, h2])
  | panic =>
    intro s h c₀ hp
    obtain ⟨ω', μ', q', h⟩ := h
    have := Pre.split_run hR keepR (fun c => c = s.c) (keepI s.c) h rfl hp
    exact .inl (by rw [this])
  | call op k ih =>
    intro s h c₀ hp
    unfold Impl at h
    obtain ⟨s₁, ⟨n₁, h1⟩, h2, h3⟩ := h
    rcases Pre.split hR keepR (fun c => c = s.c) (keepI s.c) h1 rfl hp with hc | hp₁
    · exact .inl (by rw [hc])
    revert h3
    cases hst : ASem.step env op s.c with
    | some bc =>
      intro h3
      obtain ⟨s₂, ⟨n₂, g1⟩, g2, g3⟩ := h3
      -- after the operation: y is s's, or the operation left (x, x)
      have after : bc.2.2 = s.c.2 ∨ ∃ n, ASem.outcome (ASem.run n (Prog.call op k) env s.c) = yOutcome bc.2.2 := by
        rcases ASem.step_snd env op s.c (b := bc.1) (c₁ := bc.2) hst with e | e
        · exact .inl e
        · refine .inr ⟨1, ?_⟩
          simp only [ASem.run, hst]
          rw [e]; exact run_xx env (k bc.1) s.c.1
      rcases Pre.split hR (fun _ _ _ _ _ _ _ _ h => h.1) (fun c => c.2 = s.c.2 ∨ c.2 = bc.2.2)
          (fun _ _ _ _ _ _ _ _ h _ => h.2) g1 (.inl (by rw [h2])) hp₁ with hc | hp₂
      · rcases hc with hc | hc
        · exact .inl hc
        · rw [hc]; exact after
      · rcases ih bc.1 s₂ g3 c₀ hp₂ with hc | ⟨n, hn⟩
        · rw [hc, g2]; exact after
        · refine .inr ⟨n + 1, ?_⟩
          simp only [ASem.run, hst]
          rw [← g2]; exact hn
    | none =>
      intro h3
      obtain ⟨ω', μ', q', h3⟩ := h3
      have := Pre.split_run hR keepR (fun c => c = s.c) (keepI s.c) h3 h2 hp₁
      exact .inl (by rw [this])

end Services.Bootstrap.Acc
