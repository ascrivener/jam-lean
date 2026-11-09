import JAM.Theorems.RefineContract
import JAM.Accumulate

/-!
# A contract for the accumulate dispatcher that pins down its outcomes

The accumulate counterpart of `JAM.refineContract`. Gas-free proofs (`FreeStepsH`, `FreeRunH`)
step through host calls under a contract, a relation saying which outcomes a call may have. For
the lift to Ψ_M (`PVM.psiM_of_freeRunH`), the contract must *pin down* the real handler, Ψ_A's F
(`JAM.accHostFn`, GP v0.8.0 eq. `accinvocation`): every non-∞ outcome the handler produces, for
any gas, must be the one the contract allows.

`accContractK cap env` is the graph of `accHostFn env`, restricted to two things:
- the ids whose non-∞ outcome does not depend on the gas left (`AccGasFreeId`);
- calls that do not run out of gas with `cap`.

`accContractK_pins` proves that it pins down the handler. The contract is defined from the
model's dispatcher alone, so it adds no assumption about the host.

`AccGasFreeId` covers the general functions accumulate's start-up uses, and the ids the
dispatcher does not know. The general functions are `grow_heap` (1), `fetch` (2), `lookup` (3),
`read` (4), `write` (5) and `info` (6); `log` (100) is one of the unknown ids. It leaves out `gas`
(0) and `checkpoint` (18), since both report the gas left in ω₇. It also leaves out the other
accumulate functions (15–27); they can be added the same way when the handlers need them.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- The accumulate host-call ids whose non-∞ outcome does not depend on the gas: the general
    functions `grow_heap`, `fetch`, `lookup`, `read`, `write`, `info` (1 … 6), and every id the
    accumulate dispatcher does not know (7 … 14 and above 27, e.g. `log` = 100). -/
def AccGasFreeId (h : Nat) : Prop := (1 ≤ h ∧ h ≤ 14) ∨ 27 < h

/-- A general function's tail through `writeValue` does not depend on the gas it is handed. -/
theorem writeValue_body_sameButGas {X : Type} (ω : Regs) (μ : Memory) (x : X)
    (v : Except Unit (Option (List UInt8))) (o f z : Nat) (a b : Int) :
    SameButGas (writeValue ⟨.cont, a, ω, μ, x⟩ v o f z) (writeValue ⟨.cont, b, ω, μ, x⟩ v o f z) :=
  writeValue_sameButGas _ _ _ _ _ _ _ _ _ _

/-- Ω_W's body does not depend on the gas it is handed. -/
theorem hostWrite_sameButGas (ω : Regs) (μ : Memory) (s : ServiceAccount) {gas₁ gas₂ : Nat}
    (h₁ : (hostWrite gas₁ ω μ s).status ≠ .oog) (h₂ : (hostWrite gas₂ ω μ s).status ≠ .oog) :
    SameButGas (hostWrite gas₁ ω μ s) (hostWrite gas₂ ω μ s) := by
  unfold hostWrite at *
  refine charged_sameButGas _ _ _ _ _ (fun a b => ?_) h₁ h₂
  unfold SameButGas
  dsimp only
  repeat' split
  all_goals simp

namespace AccHost

/-- **The accumulate dispatcher's non-∞ outcome does not depend on the gas**, for the ids of
    `AccGasFreeId`. -/
theorem dispatch_sameButGas (env : AccEnv) {h : Nat} (hh : AccGasFreeId h) (ω : Regs) (μ : Memory)
    (c : AccCtx) {gas₁ gas₂ : Nat} (h₁ : (AccHost.dispatch env h gas₁ ω μ c).status ≠ .oog)
    (h₂ : (AccHost.dispatch env h gas₂ ω μ c).status ≠ .oog) :
    SameButGas (AccHost.dispatch env h gas₁ ω μ c) (AccHost.dispatch env h gas₂ ω μ c) := by
  -- the unknown ids: WHAT, charged 𝖬_∅
  have unk : ∀ (g : Nat), h ≠ 0 → h ≠ 1 → h ≠ 2 → h ≠ 3 → h ≠ 4 → h ≠ 5 → h ≠ 6 →
      (h < 15 ∨ 27 < h) →
      AccHost.dispatch env h g ω μ c =
        let g' : Int := (g : Int) - Constants.Cgasunknown
        ⟨if g' < 0 then .oog else .cont, g', setR7 ω Result.WHAT, μ, c⟩ := by
    intro g n0 n1 n2 n3 n4 n5 n6 hr
    unfold AccHost.dispatch
    split <;> first | omega | rfl
  by_cases e1 : h = 1
  · -- grow_heap
    subst e1
    simp only [AccHost.dispatch] at *
    unfold hostGrowHeap SameButGas at *
    generalize growHeapCore ω μ env.code = q at *
    obtain ⟨a, b, hp, w⟩ := q
    dsimp only at *
    by_cases hc : w ≤ hp ∨ w > b
    · simp [hc]
    · simp only [hc, ↓reduceIte] at h₁ h₂ ⊢
      by_cases g₁ : gas₁ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear <;>
        by_cases g₂ : gas₂ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear <;>
        simp only [g₁, g₂, ↓reduceIte] at h₁ h₂ ⊢ <;> simp_all
  by_cases e2 : h = 2
  · subst e2
    simp only [AccHost.dispatch] at *
    exact charged_sameButGas _ _ _ _ _ (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
  by_cases e3 : h = 3
  · subst e3
    simp only [AccHost.dispatch, hostLookup] at *
    obtain ⟨a, b, c', d⟩ := charged_sameButGas _ _ _ _ _
      (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
    exact ⟨a, b, c', rfl⟩
  by_cases e4 : h = 4
  · subst e4
    simp only [AccHost.dispatch, hostRead] at *
    obtain ⟨a, b, c', d⟩ := charged_sameButGas _ _ _ _ _
      (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
    exact ⟨a, b, c', rfl⟩
  by_cases e5 : h = 5
  · subst e5
    simp only [AccHost.dispatch, AccHost.onSelf] at *
    obtain ⟨a, b, c', d⟩ := hostWrite_sameButGas ω μ c.1.self h₁ h₂
    exact ⟨a, b, c', by rw [d]⟩
  by_cases e6 : h = 6
  · subst e6
    simp only [AccHost.dispatch, hostInfo] at *
    obtain ⟨a, b, c', d⟩ := charged_sameButGas _ _ _ _ _
      (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
    exact ⟨a, b, c', rfl⟩
  -- the rest are unknown ids
  have hr : h < 15 ∨ 27 < h := by unfold AccGasFreeId at hh; omega
  have h0 : h ≠ 0 := by unfold AccGasFreeId at hh; omega
  rw [unk gas₁ h0 e1 e2 e3 e4 e5 e6 hr] at h₁ ⊢
  rw [unk gas₂ h0 e1 e2 e3 e4 e5 e6 hr] at h₂ ⊢
  unfold SameButGas
  dsimp only at h₁ h₂ ⊢
  split at h₁ <;> split at h₂ <;> simp_all
  simp only [show ¬((gas₁ : Int) - Constants.Cgasunknown < 0) by omega,
    show ¬((gas₂ : Int) - Constants.Cgasunknown < 0) by omega, ↓reduceIte]

end AccHost

/-- **The accumulate contract**: Ψ_A's handler F (`accHostFn env`) at the gas-independent ids,
    for calls that do not run out of gas with `cap`, and its outcome with that much gas. `cap`
    is the most gas a host call may charge. -/
def accContractK (cap : Nat) (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' =>
    AccGasFreeId h ∧ s ≠ .oog ∧
      accHostFn env h (UInt64.ofNat cap) ω μ x =
        ⟨s, (accHostFn env h (UInt64.ofNat cap) ω μ x).gas, ω', μ', x'⟩

/-- `accContractK` at `hostCostMax`, the cap the refine proofs use. -/
def accContract (env : AccEnv) : HostRel AccCtx := accContractK hostCostMax env

/-- **The contract pins down Ψ_A's handler**, for any cap: a step that `accContractK cap env`
    allows is the only non-∞ outcome `accHostFn env` has, for any gas. -/
theorem accContractK_pins (cap : Nat) (env : AccEnv) :
    (accContractK cap env).Pins (accHostFn env).graph := by
  intro h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ ⟨hh, hs₁, he₁⟩ ⟨hs₂, g₂, he₂⟩
  simp only [accHostFn, HostResult.mk.injEq] at he₁ he₂
  obtain ⟨e1s, -, e1r, e1m, e1c⟩ := he₁
  obtain ⟨e2s, -, e2r, e2m, e2c⟩ := he₂
  have n₁ : (AccHost.dispatch env h (UInt64.ofNat cap).toNat ω μ x).status ≠ .oog := by
    intro hc; apply hs₁; rw [← e1s, hc]
  have n₂ : (AccHost.dispatch env h g₂.toNat ω μ x).status ≠ .oog := by
    intro hc; apply hs₂; rw [← e2s, hc]
  obtain ⟨a, b, c, d⟩ := AccHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  exact ⟨e1s ▸ e2s ▸ a, e1r ▸ e2r ▸ b, e1m ▸ e2m ▸ c, e1c ▸ e2c ▸ d⟩

/-- **The contract pins down Ψ_A's handler**: a step that `accContract env` allows is the only
    non-∞ outcome `accHostFn env` has, for any gas. -/
theorem accContract_pins (env : AccEnv) : (accContract env).Pins (accHostFn env).graph :=
  accContractK_pins hostCostMax env

end Services.Bootstrap.Acc
