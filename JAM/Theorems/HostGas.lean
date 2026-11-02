import JAM.Accumulate
import JAM.Refine
import PVM.Theorems.Termination

/-!
# The host-call dispatchers never add gas

Every host function of GP v0.8.0 Appendix B returns ϱ' ≤ ϱ: the common rules charge g ≥ 0, and
the one function that hands gas back, `invoke` (Ω_K), returns only what is left of the g_R it
charged (`PVM.psi_gas_le`). So the dispatchers of Ψ_A, Ψ_R and Ψ_I are `HostFn.GasNonIncreasing`,
and `PVM.psiHStar_eq` applies: for these invocations `psiHStar`'s fuel never runs out, and it is the
paper's Ψ_H exactly.
-/

namespace JAM

open PVM

/-! ## Helpers -/

@[simp] theorem setR7_gas {X} (o : HostOut X) (v : Nat) :
    ({ o with regs := setR7 o.regs v } : HostOut X).gas = o.gas := rfl

theorem writeValue_gas {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) : (writeValue out v o f z).gas = out.gas := by
  unfold writeValue
  dsimp only
  repeat' split
  all_goals rfl

/-- The common rules: with a body that leaves ϱ alone, ϱ' = ϱ − g ≤ ϱ. -/
theorem charged_gas_le {X : Type} (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) (hb : ∀ o, (body o).gas = o.gas) :
    (charged g gas ω μ x body).gas ≤ gas := by
  unfold charged
  split
  · show (gas : Int) - g ≤ gas; omega
  · rw [hb]; show (gas : Int) - g ≤ gas; omega

/-- Close `∀ o, (body o).gas = o.gas` by splitting every `if` and `match` in the body. -/
macro "gas_body" : tactic =>
  `(tactic| (intro o; first | rfl | ((try dsimp only) <;> (repeat' split) <;>
    (try simp only [writeValue_gas, AccHost.r7, AccHost.panic, AccHost.updX, AccHost.onSelf,
      RefineHost.r7, RefineHost.panic]) <;> rfl)))

/-! ## General functions -/

theorem hostGas_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) :
    (hostGas gas ω μ x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => rfl

theorem hostGrowHeap_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (jam : ByteArray) (x : X) :
    (hostGrowHeap gas ω μ jam x).gas ≤ gas := by
  unfold hostGrowHeap
  dsimp only
  repeat' split
  all_goals (rename_i h; simp only at h; omega)

theorem hostFetch_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (cx : FetchContext) (x : X) :
    (hostFetch gas ω μ cx x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => writeValue_gas ..

theorem hostLookup_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (s : ServiceAccount) (sid : Nat)
    (d : Accounts) (x : X) : (hostLookup gas ω μ s sid d x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => writeValue_gas ..

theorem hostRead_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (s : ServiceAccount) (sid : Nat)
    (d : Accounts) (x : X) : (hostRead gas ω μ s sid d x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => writeValue_gas ..

theorem hostWrite_gas (gas : Nat) (ω : Regs) (μ : Memory) (s : ServiceAccount) :
    (hostWrite gas ω μ s).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem hostInfo_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (sid : Nat) (d : Accounts) (x : X) :
    (hostInfo gas ω μ sid d x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => writeValue_gas ..

/-! ## Accumulate -/

namespace AccHost

theorem bless_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (bless env gas ω μ c).gas ≤ gas := by
  unfold bless charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem assign_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (assign env gas ω μ c).gas ≤ gas := by
  unfold assign charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem designate_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (designate env gas ω μ c).gas ≤ gas := by
  unfold designate charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem new_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (new env gas ω μ c).gas ≤ gas := by
  unfold new charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem transfer_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (transfer env gas ω μ c).gas ≤ gas := by
  unfold transfer charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem eject_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (eject env gas ω μ c).gas ≤ gas := by
  unfold eject charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem solicit_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (solicit env gas ω μ c).gas ≤ gas := by
  unfold solicit charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem forget_gas (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (forget env gas ω μ c).gas ≤ gas := by
  unfold forget charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem checkpoint_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (checkpoint gas ω μ c).gas ≤ gas := by
  unfold checkpoint charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem upgrade_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (upgrade gas ω μ c).gas ≤ gas := by
  unfold upgrade charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem query_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (query gas ω μ c).gas ≤ gas := by
  unfold query charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem yield_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (yield gas ω μ c).gas ≤ gas := by
  unfold yield charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem provide_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (provide gas ω μ c).gas ≤ gas := by
  unfold provide charge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem dispatch_gas (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) :
    (dispatch env n gas ω μ c).gas ≤ gas := by
  unfold dispatch
  split
  all_goals first
    | with_reducible exact hostGas_gas ..
    | with_reducible exact hostGrowHeap_gas ..
    | with_reducible exact hostFetch_gas ..
    | with_reducible exact hostLookup_gas ..
    | with_reducible exact hostRead_gas ..
    | with_reducible exact hostInfo_gas ..
    | (simp only [onSelf]; exact hostWrite_gas ..)
    | with_reducible exact bless_gas ..
    | with_reducible exact assign_gas ..
    | with_reducible exact designate_gas ..
    | with_reducible exact new_gas ..
    | with_reducible exact transfer_gas ..
    | with_reducible exact eject_gas ..
    | with_reducible exact solicit_gas ..
    | with_reducible exact forget_gas ..
    | with_reducible exact checkpoint_gas ..
    | with_reducible exact upgrade_gas ..
    | with_reducible exact query_gas ..
    | with_reducible exact yield_gas ..
    | with_reducible exact provide_gas ..
    | (show (gas : Int) - _ ≤ gas; omega)

end AccHost

/-- **F of Ψ_A never adds gas.** -/
theorem accHostFn_gasNonIncreasing (env : AccEnv) : (accHostFn env).GasNonIncreasing := by
  intro h g ω μ x
  have := AccHost.dispatch_gas env h g.toNat ω μ x
  have hg := g.toNat_lt
  simp only [accHostFn]
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size] at hg ⊢; omega)]
  omega

/-! ## Refine and is-authorized -/

namespace RefineHost

theorem unknown_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) :
    (unknown gas ω μ x).gas ≤ gas := by
  show (gas : Int) - _ ≤ gas; omega

theorem invoke_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (invoke gas ω μ c).gas ≤ gas := by
  unfold invoke
  dsimp only
  generalize (if μ.rangeWritable (reg ω 8) 112 = true then
          some (Num.decodeLE (List.take 8 (μ.readN (reg ω 8) 112)),
            decodeRegs (List.drop 8 (μ.readN (reg ω 8) 112)))
        else none) = w?
  unfold charged
  rcases w? with _ | ⟨gR, w⟩
  · dsimp only
    split <;> (show (gas : Int) - _ ≤ gas; omega)
  · dsimp only
    split
    · show (gas : Int) - _ ≤ gas; omega
    · rename_i hge
      split
      · show (gas : Int) - _ ≤ gas; omega
      · rename_i vm _
        have hp := psi_gas_le vm.code vm.pc (UInt64.ofNat gR) vm.charged w vm.ram
        have hu : (UInt64.ofNat gR).toNat ≤ gR := UInt64.toNat_ofNat_le
        generalize psi vm.code vm.pc (UInt64.ofNat gR) vm.charged w vm.ram = r at hp ⊢
        rcases r with ⟨st, pc, g', ch', regs, mem⟩
        dsimp only at hp ⊢
        cases st <;> (show (gas : Int) - _ + _ ≤ gas; omega)

theorem exportSeg_gas (gas : Nat) (ω : Regs) (μ : Memory) (off : Nat) (c : RefineCtx) :
    (exportSeg gas ω μ off c).gas ≤ gas := by
  unfold exportSeg; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem machine_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (machine gas ω μ c).gas ≤ gas := by
  unfold machine; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem peek_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (peek gas ω μ c).gas ≤ gas := by
  unfold peek; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem poke_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (poke gas ω μ c).gas ≤ gas := by
  unfold poke; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem pages_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (pages gas ω μ c).gas ≤ gas := by
  unfold pages; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem expunge_gas (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (expunge gas ω μ c).gas ≤ gas := by
  unfold expunge; exact charged_gas_le _ _ _ _ _ _ (by gas_body)

theorem historicalLookup_gas {X} (gas : Nat) (ω : Regs) (μ : Memory) (s : Nat) (d : Accounts)
    (t : Nat) (x : X) : (historicalLookup gas ω μ s d t x).gas ≤ gas :=
  charged_gas_le _ _ _ _ _ _ fun _ => writeValue_gas ..

theorem dispatch_gas (env : Env) (n gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (dispatch env n gas ω μ c).gas ≤ gas := by
  unfold dispatch
  split
  all_goals first
    | with_reducible exact hostGas_gas ..
    | with_reducible exact hostGrowHeap_gas ..
    | with_reducible exact hostFetch_gas ..
    | with_reducible exact invoke_gas ..
    | with_reducible exact unknown_gas ..
    | with_reducible exact historicalLookup_gas ..
    | with_reducible exact exportSeg_gas ..
    | with_reducible exact machine_gas ..
    | with_reducible exact peek_gas ..
    | with_reducible exact poke_gas ..
    | with_reducible exact pages_gas ..
    | with_reducible exact expunge_gas ..

theorem dispatchI_gas (params : Params) (p : WorkPackage) (code : ByteArray) (n gas : Nat)
    (ω : Regs) (μ : Memory) (c : Unit) : (dispatchI params p code n gas ω μ c).gas ≤ gas := by
  unfold dispatchI
  split
  all_goals first
    | with_reducible exact hostGas_gas ..
    | with_reducible exact hostGrowHeap_gas ..
    | with_reducible exact hostFetch_gas ..
    | with_reducible exact unknown_gas ..

end RefineHost

theorem toHostFn_gasNonIncreasing {X : Type} (f : Nat → Nat → Regs → Memory → X → HostOut X)
    (hf : ∀ n gas ω μ x, (f n gas ω μ x).gas ≤ gas) : (toHostFn f).GasNonIncreasing := by
  intro h g ω μ x
  have := hf h g.toNat ω μ x
  have hg := g.toNat_lt
  simp only [toHostFn]
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size] at hg ⊢; omega)]
  omega

/-- **F of Ψ_R never adds gas.** -/
theorem refineHostFn_gasNonIncreasing (env : RefineHost.Env) :
    (toHostFn (RefineHost.dispatch env)).GasNonIncreasing :=
  toHostFn_gasNonIncreasing _ (RefineHost.dispatch_gas env)

/-- **F of Ψ_I never adds gas.** -/
theorem isAuthHostFn_gasNonIncreasing (params : Params) (p : WorkPackage) (code : ByteArray) :
    (toHostFn (RefineHost.dispatchI params p code)).GasNonIncreasing :=
  toHostFn_gasNonIncreasing _ (RefineHost.dispatchI_gas params p code)

end JAM
