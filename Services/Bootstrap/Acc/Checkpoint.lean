import JAM.Theorems.Confinement

/-!
# Checkpoints in Ψ_A: what an accumulate run commits

Ψ_A (GP v0.8.0 eq. `accinvocation`) runs the service with the context (x, y) ∈ 𝕃², the regular
and the exceptional dimension. These are facts about the model only, with no binary in them.
Bootstrap's accumulate (`Services/Bootstrap/Acc/README.md`) relies on them for its rollback:

* `dispatch_ctx_snd`: **y changes only at `checkpoint`.** Every host call except
  `checkpoint` (id 18) leaves y as it was. `checkpoint` either runs out of gas, leaving the
  context unchanged, or sets y to the current x (Ω_C, `dispatch_checkpoint`).
* `psiARun_eq`: **Ψ_A reports x after a halt, and y after ☇ or ∞.** The state, transfers and
  provisions come from x when the code halts, and from y when it panics or runs out of gas. The
  yield is the output if that is 32 octets long, else x's yield.

Together: when a run ends in ☇ or ∞, Ψ_A's result is the regular dimension x as it was at the
run's last successful `checkpoint` call, or the initial implications if there was none. Storage
writes (`write`, id 5) and the other accumulate host functions update x at once, so a checkpoint
commits every effect made before it.
-/

namespace Services.Bootstrap.Acc

open PVM JAM JAM.AccHost

/-- The body of a charged host function keeps y if it does; on ∞ the context is unchanged. -/
theorem charged_snd (g gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (body : HostOut AccCtx → HostOut AccCtx)
    (hb : (body ⟨.cont, (gas : Int) - g, ω, μ, c⟩).ctx.2 = c.2) :
    (charged g gas ω μ c body).ctx.2 = c.2 :=
  charged_ctx (fun c' : AccCtx => c'.2 = c.2) g gas ω μ c body rfl hb

/-- Close `(f …).ctx.2 = c.2` for an accumulate host function `f`: every branch returns `out`
    with only the registers, the status or x changed. -/
macro "snd_tac" : tactic =>
  `(tactic| (
    apply charged_snd
    dsimp only
    (repeat' split) <;> simp only [JAM.AccHost.r7, JAM.AccHost.panic, JAM.AccHost.updX]))

theorem bless_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (bless env gas ω μ c).ctx.2 = c.2 := by unfold bless charge; snd_tac
theorem assign_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (assign env gas ω μ c).ctx.2 = c.2 := by unfold assign charge; snd_tac
theorem designate_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (designate env gas ω μ c).ctx.2 = c.2 := by unfold designate charge; snd_tac
theorem new_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (new env gas ω μ c).ctx.2 = c.2 := by unfold new charge; snd_tac
theorem upgrade_snd (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (upgrade gas ω μ c).ctx.2 = c.2 := by unfold upgrade charge; snd_tac
theorem transfer_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (transfer env gas ω μ c).ctx.2 = c.2 := by unfold transfer charge; snd_tac
theorem eject_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (eject env gas ω μ c).ctx.2 = c.2 := by unfold eject charge; snd_tac
theorem query_snd (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (query gas ω μ c).ctx.2 = c.2 := by unfold query charge; snd_tac
theorem solicit_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (solicit env gas ω μ c).ctx.2 = c.2 := by unfold solicit charge; snd_tac
theorem forget_snd (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (forget env gas ω μ c).ctx.2 = c.2 := by unfold forget charge; snd_tac
theorem yield_snd (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (yield gas ω μ c).ctx.2 = c.2 := by unfold yield charge; snd_tac
theorem provide_snd (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (provide gas ω μ c).ctx.2 = c.2 := by unfold provide charge; snd_tac

/-- **Every host call but `checkpoint` keeps y** (GP eq. `accinvocation`: only Ω_C writes the
    exceptional dimension). This includes the general functions, run on x through G. -/
theorem dispatch_snd (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hn : n ≠ 18) : (dispatch env n gas ω μ c).ctx.2 = c.2 := by
  unfold dispatch
  split
  · exact charged_snd _ _ _ _ _ _ rfl
  · unfold hostGrowHeap; rfl
  · exact charged_ctx (fun c' : AccCtx => c'.2 = c.2) _ _ _ _ _ _ rfl (by rw [writeValue_ctx])
  · rfl
  · rfl
  · rfl
  · rfl
  · exact bless_snd env gas ω μ c
  · exact assign_snd env gas ω μ c
  · exact designate_snd env gas ω μ c
  · exact absurd rfl hn
  · exact new_snd env gas ω μ c
  · exact upgrade_snd gas ω μ c
  · exact transfer_snd env gas ω μ c
  · exact eject_snd env gas ω μ c
  · exact query_snd gas ω μ c
  · exact solicit_snd env gas ω μ c
  · exact forget_snd env gas ω μ c
  · exact yield_snd gas ω μ c
  · exact provide_snd gas ω μ c
  · rfl

/-- **Ω_C, `checkpoint` = 18**: with less than 𝖬_C gas the call runs out of gas and the context
    is unchanged; otherwise it continues, y becomes x, and ω'_7 is the gas left. -/
theorem dispatch_checkpoint (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    dispatch env 18 gas ω μ c =
      if gas < Constants.CgasC then ⟨.oog, (gas : Int) - Constants.CgasC, ω, μ, c⟩
      else ⟨.cont, (gas : Int) - Constants.CgasC,
            setR7 ω ((gas : Int) - Constants.CgasC).toNat, μ, (c.1, c.1)⟩ := by
  simp only [dispatch, checkpoint, charge, charged]

/-- **What a host call can do to y**: keep it, or (only `checkpoint`, id 18) set it to the
    current x. -/
theorem dispatch_ctx_snd (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (dispatch env n gas ω μ c).ctx.2 = c.2 ∨
      (n = 18 ∧ (dispatch env n gas ω μ c).ctx = (c.1, c.1)) := by
  by_cases hn : n = 18
  · subst hn
    rw [dispatch_checkpoint]
    split
    · exact .inl rfl
    · exact .inr ⟨rfl, rfl⟩
  · exact .inl (dispatch_snd env n gas ω μ c hn)

/-- The same for the handler Ψ_H runs (`accHostFn`, gas clamped at 0). -/
theorem accHostFn_ctx_snd (env : AccEnv) (n : Nat) (gas : UInt64) (ω : Regs) (μ : Memory)
    (c : AccCtx) :
    (accHostFn env n gas ω μ c).ctx.2 = c.2 ∨
      (n = 18 ∧ (accHostFn env n gas ω μ c).ctx = (c.1, c.1)) :=
  dispatch_ctx_snd env n gas.toNat ω μ c

/-- **Ψ_A's result from the final context** (GP eq. `accinvocation`): for code `c` within
    𝖶_C, Ψ_A runs Ψ_M from instruction 5 on (x₀, x₀) with x₀ = I(**e**, s). If that panics or runs
    out of gas, the result is the exceptional dimension y; if it halts, the regular dimension x,
    with the output as the yield when it is 32 octets long. -/
theorem psiARun_eq (params : Params) (entropy : List UInt8) (st : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) (code : ByteArray)
    (hcode : (st.accounts.get? s).bind (·.code) = some code)
    (hsize : ¬ code.size > Constants.Cmaxservicecodesize) :
    let x₀ := initImplications st s t entropy
    let env : AccEnv := { params, slot := t, entropy, inputs, code }
    let r := psiM code 5 (UInt64.ofNat g)
      ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩ (accHostFn env) (x₀, x₀)
    psiARun params entropy st t s g inputs =
      match r.2.1 with
      | .oog | .panic => ⟨r.2.2.2.state, r.2.2.2.xfers, r.2.2.2.yield, r.1, r.2.2.2.provisions⟩
      | .ok out =>
        if out.size = 32 then ⟨r.2.2.1.state, r.2.2.1.xfers, some out.toList, r.1, r.2.2.1.provisions⟩
        else ⟨r.2.2.1.state, r.2.2.1.xfers, r.2.2.1.yield, r.1, r.2.2.1.provisions⟩ := by
  intro x₀ env r
  unfold psiARun
  simp only [hcode, hsize, ↓reduceIte]
  rfl

end Services.Bootstrap.Acc
