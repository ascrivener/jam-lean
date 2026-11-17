import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Transfer.SetKeyCall

/-!
# `Impl` for a context-keeping call and for `orPanic`

Two shapes `on_transfer` uses (GP v0.8.0 §B.4, the accumulate host calls; Spec `onTransfer`):
- `impl_call_keep`: `op o >>= f` for an operation that keeps the context (`read`): the run reaches,
  keeping the context, a state that implements `f b`.
- `impl_orPanic`: `orPanic o`: the run reaches s₁ keeping the context, the operation's wrapper runs
  under `YIn` to s₂ with the operation's context, and there either the reply is `ok a` and s₂
  implements `pure a`, or it is `error` and the run ends ☇ (or the wrapper aborts for a reason in `Ab`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Spec

variable {Qu : Type}

/-- **A call that keeps the context**: `op o >>= f` from s, if ASem's step returns b with the context
    unchanged and the run reaches, keeping the context, a state s₂ implementing `f b`. -/
theorem impl_call_keep {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α β : Type} (o : AOp β) (f : β → Prog AOp α) (Q : α → St Qu → Prop) (s s₂ : St Qu) {b : β}
    (hst : ASem.step env o s.c = some (b, s.c)) (h2 : Reaches p (KeepCtx R) s s₂) (hc2 : s₂.c = s.c)
    (hk : Impl p R env Ab (f b) Q s₂) : Impl p R env Ab (Prog.bind (Prog.op o) f) Q s := by
  show Impl p R env Ab (.call o fun b => f b) Q s
  unfold Impl
  refine .inr ⟨s, ⟨0, .refl⟩, rfl, ?_⟩
  rw [hst]
  obtain ⟨n, h2⟩ := h2
  exact .inr ⟨s₂, ⟨n, h2.keepY _ _ rfl⟩, hc2, hk⟩

/-- **`orPanic o`**: the run reaches s₁ keeping the context; ASem's step returns r and c₁; from s₁
    the wrapper aborts (for a reason in `Ab`, y as before), or runs under `YIn` to s₂ with context
    c₁, where `ok a` continues as `pure a` and `error` ends ☇. -/
theorem impl_orPanic {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α : Type} (o : AOp (Except Unit α)) (Q : α → St Qu → Prop) (s s₁ : St Qu) {r : Except Unit α}
    {c₁ : AccCtx} (h1 : Reaches p (KeepCtx R) s s₁) (hc1 : s₁.c = s.c)
    (hst : ASem.step env o s.c = some (r, c₁))
    (h2 : Aborts p (YIn R s.c.2 c₁.2) Ab s₁ s.c ∨
      ∃ s₂, Reaches p (YIn R s.c.2 c₁.2) s₁ s₂ ∧ s₂.c = c₁ ∧
        match r with
        | .ok a => Impl p R env Ab (.pure a) Q s₂
        | .error _ => Ends p (KeepCtx R) s₂ .panic s₂.c) :
    Impl p R env Ab (orPanic o) Q s := by
  show Impl p R env Ab (.call o fun r => match r with | .ok a => .pure a | .error _ => .panic) Q s
  unfold Impl
  refine .inr ⟨s₁, h1, hc1, ?_⟩
  rw [hst]
  rcases h2 with h | ⟨s₂, h2, hc2, hk⟩
  · exact .inl ⟨s.c, .inl rfl, h⟩
  · refine .inr ⟨s₂, h2, hc2, ?_⟩
    cases r with
    | ok a => exact hk
    | error e => exact hk

end Services.Bootstrap.Acc
