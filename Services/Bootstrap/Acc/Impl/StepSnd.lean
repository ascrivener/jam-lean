import Services.Bootstrap.ASem
import Services.Bootstrap.Acc.Checkpoint

/-!
# What an `ASem` operation does to y

GP v0.8.0 eq. `accinvocation`: only Ω_C (`checkpoint`) writes the exceptional dimension y, setting
it to x. So an operation keeps y, or leaves the context (x, x) (`ASem.step_snd`). The out-of-gas
case of the lift uses this: a run that runs out of gas reports y.
-/

namespace Services.Bootstrap.ASem

open PVM JAM Services.Bootstrap.Spec Services.Bootstrap.Acc

/-- One host call keeps y, or leaves (x, x). -/
theorem call_snd {env : AccEnv} {n : Nat} {args : List Bytes} {vals : List Nat} {c : AccCtx}
    {o : HostOut AccCtx} (h : call env n args vals c = some o) : o.ctx.2 = c.2 ∨ o.ctx = (c.1, c.1) := by
  dsimp only [call] at h
  split at h
  · cases h
    rcases dispatch_ctx_snd env n opGas (argRegs vals) (argMem args) c with h1 | ⟨-, h2⟩
    · exact .inl h1
    · exact .inr h2
  · cases h

theorem writeValue_ctx {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8))) (o f z : Nat) :
    (writeValue out v o f z).ctx = out.ctx := by
  unfold writeValue
  rcases v with _ | (_ | _) <;> dsimp only <;> (try split) <;> rfl

theorem hostFetch_ctx {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (cx : FetchContext) (x : X) :
    (hostFetch gas ω μ cx x).ctx = x := by
  unfold hostFetch charged
  dsimp only
  generalize Constants.CgasY _ = gg
  obtain ⟨gc, gl⟩ := gg
  dsimp only
  split
  · rfl
  · exact writeValue_ctx _ _ _ _ _

/-- `fetch`, `lookup`, `read` and `info` keep the context. -/
theorem call_keep {env : AccEnv} {n : Nat} (hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) {args : List Bytes}
    {vals : List Nat} {c : AccCtx} {o : HostOut AccCtx} (h : call env n args vals c = some o) : o.ctx = c := by
  dsimp only [call] at h
  split at h
  · cases h
    rcases hn with rfl | rfl | rfl | rfl
    · exact hostFetch_ctx _ _ _ _ _
    · rfl
    · rfl
    · rfl
  · cases h

/-- **An operation keeps y, or leaves (x, x).** -/
theorem step_snd (env : AccEnv) {β : Type} (op : AOp β) (c : AccCtx) {b : β} {c₁ : AccCtx}
    (h : step env op c = some (b, c₁)) : c₁.2 = c.2 ∨ c₁ = (c.1, c.1) := by
  cases op <;> simp only [step, twoPhase, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  all_goals obtain ⟨o, ho, hb⟩ := h
  all_goals first
    | (have e := (Prod.mk.inj (Option.some.inj hb)).2
       rw [← e]; exact call_snd ho)
    | (have hk := call_keep (by decide) ho
       split at hb
       · have e := (Prod.mk.inj (Option.some.inj hb)).2
         rw [← e, hk]; exact .inl rfl
       · obtain ⟨o', ho', hb'⟩ := Option.bind_eq_some_iff.1 hb
         have e := (Prod.mk.inj (Option.some.inj hb')).2
         rw [hk] at ho'
         rw [← e, call_keep (by decide) ho']; exact .inl rfl)

end Services.Bootstrap.ASem
