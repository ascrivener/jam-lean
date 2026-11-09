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

`AccGasFreeId` covers every id except `gas` (0) and `checkpoint` (18):
- the general functions `grow_heap` (1), `fetch` (2), `lookup` (3), `read` (4), `write` (5) and
  `info` (6);
- the accumulate functions `bless` (15), `assign` (16), `designate` (17), `new` (19), `upgrade`
  (20), `transfer` (21), `eject` (22), `query` (23), `solicit` (24), `forget` (25), `yield` (26) and
  `provide` (27). Each charges a cost fixed by its registers and the context (for `transfer`,
  𝖬_T + t with t = l on success), and its body never reads the gas left;
- the ids the dispatcher does not know (7 … 14 and above 27; `log` = 100 is one).

`gas` and `checkpoint` are left out: both report the gas left in ω₇ (Ω_G, Ω_C), so no contract
can pin them down in this sense.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- The accumulate host-call ids whose non-∞ outcome does not depend on the gas: every id but
    `gas` (0) and `checkpoint` (18), which report the gas left. These are the general functions
    `grow_heap` … `info` (1 … 6), the accumulate functions 15 … 17 and 19 … 27, and every id the
    accumulate dispatcher does not know (7 … 14 and above 27, e.g. `log` = 100). -/
def AccGasFreeId (h : Nat) : Prop := h ≠ 0 ∧ h ≠ 18

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

open JAM.AccHost

/-- Close `SameButGas (charge g gas₁ ω μ c body) (charge g gas₂ ω μ c body)` for an accumulate
    host function, with both calls' `≠ .oog` in context: every branch of the body returns its
    `out` with only the registers, the status or x changed, and branches on registers, memory
    and context, never on the gas. -/
macro "sbg_tac" : tactic =>
  `(tactic| (
    refine charged_sameButGas _ _ _ _ _ (fun a b => ?_) ‹_› ‹_›
    unfold SameButGas
    try dsimp only
    (repeat' split) <;> simp_all [JAM.AccHost.r7, JAM.AccHost.panic, JAM.AccHost.updX]))

/-- Ω_B (`bless`, 15)'s non-∞ outcome does not depend on the gas. -/
theorem bless_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (bless env gas₁ ω μ c).status ≠ .oog) (h₂ : (bless env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (bless env gas₁ ω μ c) (bless env gas₂ ω μ c) := by
  unfold bless charge at *; sbg_tac

/-- Ω_A (`assign`, 16)'s non-∞ outcome does not depend on the gas. -/
theorem assign_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (assign env gas₁ ω μ c).status ≠ .oog) (h₂ : (assign env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (assign env gas₁ ω μ c) (assign env gas₂ ω μ c) := by
  unfold assign charge at *; sbg_tac

/-- Ω_D (`designate`, 17)'s non-∞ outcome does not depend on the gas. -/
theorem designate_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (designate env gas₁ ω μ c).status ≠ .oog) (h₂ : (designate env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (designate env gas₁ ω μ c) (designate env gas₂ ω μ c) := by
  unfold designate charge at *; sbg_tac

/-- Ω_N (`new`, 19)'s non-∞ outcome does not depend on the gas. -/
theorem new_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (new env gas₁ ω μ c).status ≠ .oog) (h₂ : (new env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (new env gas₁ ω μ c) (new env gas₂ ω μ c) := by
  unfold new charge at *; sbg_tac

/-- Ω_U (`upgrade`, 20)'s non-∞ outcome does not depend on the gas. -/
theorem upgrade_sameButGas (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (upgrade gas₁ ω μ c).status ≠ .oog) (h₂ : (upgrade gas₂ ω μ c).status ≠ .oog) :
    SameButGas (upgrade gas₁ ω μ c) (upgrade gas₂ ω μ c) := by
  unfold upgrade charge at *; sbg_tac

/-- Ω_T (`transfer`, 21)'s non-∞ outcome does not depend on the gas. -/
theorem transfer_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (transfer env gas₁ ω μ c).status ≠ .oog) (h₂ : (transfer env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (transfer env gas₁ ω μ c) (transfer env gas₂ ω μ c) := by
  unfold transfer charge at *; sbg_tac

/-- Ω_J (`eject`, 22)'s non-∞ outcome does not depend on the gas. -/
theorem eject_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (eject env gas₁ ω μ c).status ≠ .oog) (h₂ : (eject env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (eject env gas₁ ω μ c) (eject env gas₂ ω μ c) := by
  unfold eject charge at *; sbg_tac

/-- Ω_Q (`query`, 23)'s non-∞ outcome does not depend on the gas. -/
theorem query_sameButGas (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (query gas₁ ω μ c).status ≠ .oog) (h₂ : (query gas₂ ω μ c).status ≠ .oog) :
    SameButGas (query gas₁ ω μ c) (query gas₂ ω μ c) := by
  unfold query charge at *; sbg_tac

/-- Ω_S (`solicit`, 24)'s non-∞ outcome does not depend on the gas. -/
theorem solicit_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (solicit env gas₁ ω μ c).status ≠ .oog) (h₂ : (solicit env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (solicit env gas₁ ω μ c) (solicit env gas₂ ω μ c) := by
  unfold solicit charge at *; sbg_tac

/-- Ω_F (`forget`, 25)'s non-∞ outcome does not depend on the gas. -/
theorem forget_sameButGas (env : AccEnv) (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (forget env gas₁ ω μ c).status ≠ .oog) (h₂ : (forget env gas₂ ω μ c).status ≠ .oog) :
    SameButGas (forget env gas₁ ω μ c) (forget env gas₂ ω μ c) := by
  unfold forget charge at *; sbg_tac

/-- Ω_♉ (`yield`, 26)'s non-∞ outcome does not depend on the gas. -/
theorem yield_sameButGas (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (yield gas₁ ω μ c).status ≠ .oog) (h₂ : (yield gas₂ ω μ c).status ≠ .oog) :
    SameButGas (yield gas₁ ω μ c) (yield gas₂ ω μ c) := by
  unfold yield charge at *; sbg_tac

/-- Ω_♈ (`provide`, 27)'s non-∞ outcome does not depend on the gas. -/
theorem provide_sameButGas (ω : Regs) (μ : Memory) (c : AccCtx) {gas₁ gas₂ : Nat}
    (h₁ : (provide gas₁ ω μ c).status ≠ .oog) (h₂ : (provide gas₂ ω μ c).status ≠ .oog) :
    SameButGas (provide gas₁ ω μ c) (provide gas₂ ω μ c) := by
  unfold provide charge at *; sbg_tac

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
  -- the accumulate functions 15 … 27, but `checkpoint` (18)
  have h0 : h ≠ 0 := hh.1
  have h18 : h ≠ 18 := hh.2
  by_cases e15 : h = 15
  · subst e15; simp only [AccHost.dispatch] at *; exact bless_sameButGas env ω μ c h₁ h₂
  by_cases e16 : h = 16
  · subst e16; simp only [AccHost.dispatch] at *; exact assign_sameButGas env ω μ c h₁ h₂
  by_cases e17 : h = 17
  · subst e17; simp only [AccHost.dispatch] at *; exact designate_sameButGas env ω μ c h₁ h₂
  by_cases e19 : h = 19
  · subst e19; simp only [AccHost.dispatch] at *; exact new_sameButGas env ω μ c h₁ h₂
  by_cases e20 : h = 20
  · subst e20; simp only [AccHost.dispatch] at *; exact upgrade_sameButGas ω μ c h₁ h₂
  by_cases e21 : h = 21
  · subst e21; simp only [AccHost.dispatch] at *; exact transfer_sameButGas env ω μ c h₁ h₂
  by_cases e22 : h = 22
  · subst e22; simp only [AccHost.dispatch] at *; exact eject_sameButGas env ω μ c h₁ h₂
  by_cases e23 : h = 23
  · subst e23; simp only [AccHost.dispatch] at *; exact query_sameButGas ω μ c h₁ h₂
  by_cases e24 : h = 24
  · subst e24; simp only [AccHost.dispatch] at *; exact solicit_sameButGas env ω μ c h₁ h₂
  by_cases e25 : h = 25
  · subst e25; simp only [AccHost.dispatch] at *; exact forget_sameButGas env ω μ c h₁ h₂
  by_cases e26 : h = 26
  · subst e26; simp only [AccHost.dispatch] at *; exact yield_sameButGas ω μ c h₁ h₂
  by_cases e27 : h = 27
  · subst e27; simp only [AccHost.dispatch] at *; exact provide_sameButGas ω μ c h₁ h₂
  -- the rest are unknown ids
  have hr : h < 15 ∨ 27 < h := by omega
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
