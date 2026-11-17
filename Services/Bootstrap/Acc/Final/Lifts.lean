import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# Runs that keep the context are runs that keep y

A step under `KeepCtx R` keeps (x, y); so a run under it from y = a is a run under `YIn R a b` (y is
a throughout). T2's composition (`accumulate_spec`) runs the start-up, the first log line and the inputs
decode inside `fetchItems`'s wrapper section (`YIn`); the log line's failure tail (`ExhaustsP`) is stated
under `KeepCtx`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

variable {Qu : Type}

/-- A `KeepCtx R` run keeps the context. -/
theorem FreeStepsH.ctx_keep {p : ByteArray} {R : HostRel (AccCtx × Qu)}
    {i : Nat} {ω : Regs} {μ : Memory} {xq : AccCtx × Qu} {i' : Nat} {ω' : Regs} {μ' : Memory}
    {xq' : AccCtx × Qu} {n : Nat} (run : FreeStepsH p (KeepCtx R) i ω μ xq i' ω' μ' xq' n) :
    xq'.1 = xq.1 := by
  induction run with
  | refl => rfl
  | pad _ ih => exact ih
  | next _ _ _ ih => exact ih
  | host _ _ _ hr _ ih => exact ih.trans hr.2

/-- **A `KeepCtx R` run from y = a is a `YIn R a b` run.** -/
theorem FreeStepsH.keepYIn {p : ByteArray} {R : HostRel (AccCtx × Qu)} (a b : Implications)
    {i : Nat} {ω : Regs} {μ : Memory} {xq : AccCtx × Qu} {i' : Nat} {ω' : Regs} {μ' : Memory}
    {xq' : AccCtx × Qu} {n : Nat} (run : FreeStepsH p (KeepCtx R) i ω μ xq i' ω' μ' xq' n)
    (ha : xq.1.2 = a) : FreeStepsH p (YIn R a b) i ω μ xq i' ω' μ' xq' n := by
  induction run with
  | refl => exact .refl
  | pad _ ih => exact .pad (ih ha)
  | next hn hc _ ih => exact .next hn hc (ih ha)
  | host hP hc hst hr _ ih =>
    obtain ⟨hR, he⟩ := hr
    have ha' : _ = a := (congrArg Prod.snd he).trans ha
    exact .host hP hc hst ⟨hR, .inl ha'⟩ (ih ha')

/-- **A `KeepCtx R` run to an exit, from y = a, is a `YIn R a b` run.** -/
theorem FreeRunH.keepYIn {p : ByteArray} {R : HostRel (AccCtx × Qu)} (a b : Implications)
    {i : Nat} {ω : Regs} {μ : Memory} {xq : AccCtx × Qu} {ε : Status} {ω' : Regs} {μ' : Memory}
    {xq' : AccCtx × Qu} (run : FreeRunH p (KeepCtx R) i ω μ xq ε ω' μ' xq')
    (ha : xq.1.2 = a) : FreeRunH p (YIn R a b) i ω μ xq ε ω' μ' xq' := by
  induction run with
  | exit hr hne => exact .exit hr hne
  | host hr hR _ ih =>
    obtain ⟨hR, he⟩ := hR
    have ha' : _ = a := (congrArg Prod.snd he).trans ha
    exact .host hr ⟨hR, .inl ha'⟩ (ih ha')
  | hostStop hr hR hs =>
    obtain ⟨hR, he⟩ := hR
    exact .hostStop hr ⟨hR, .inl ((congrArg Prod.snd he).trans ha)⟩ hs

/-- `Reaches` under `KeepCtx R` from y = a is `Reaches` under `YIn R a b`. -/
theorem Reaches.keepYIn {p : ByteArray} {R : HostRel (AccCtx × Qu)} (a b : Implications) {s s' : St Qu}
    (h : Reaches p (KeepCtx R) s s') (ha : s.c.2 = a) : Reaches p (YIn R a b) s s' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, FreeStepsH.keepYIn a b h ha⟩

/-- **An early ☇ keeping the context, from y = a, is one under `YIn R a b`.** -/
theorem Aborts.keepYIn {p : ByteArray} {R : HostRel (AccCtx × Qu)} {Ab : St Qu → Prop} (a b : Implications)
    {s : St Qu} (h : Aborts p (KeepCtx R) Ab s s.c) (ha : s.c.2 = a) : Aborts p (YIn R a b) Ab s s.c := by
  obtain ⟨s', ⟨n, h1⟩, h2, ω', μ', q', h3⟩ := h
  have hc : s'.c = s.c := FreeStepsH.ctx_keep h1
  refine ⟨s', ⟨n, FreeStepsH.keepYIn a b h1 ha⟩, h2, ω', μ', q', FreeRunH.keepYIn a b h3 ?_⟩
  show s'.c.2 = a
  rw [hc]; exact ha

end Services.Bootstrap.Acc
