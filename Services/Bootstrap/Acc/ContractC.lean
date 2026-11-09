import Services.Bootstrap.Acc.Contract
import Services.Bootstrap.Acc.Checkpoint
import PVM.Logic.Dead7

/-!
# `checkpoint` in the accumulate contract

Ω_C (`checkpoint`, id 18, GP v0.8.0 eq. `accinvocation`) charges 𝖬_C, sets y to x, and reports the
gas left in ω₇. The gas left is not something a gas-free proof knows, so no contract can pin the
call down exactly (`HostRel.Pins`). `accContractCK` adds `checkpoint` to `accContractK` with its
model outcome except that ω₇ is a fixed value, **0**. Any fixed value would do; 0 is the simplest,
and nothing in a lifted run depends on it: the lift (`PVM.psiM_of_freeRunH7`) requires ω₇ to be dead
after every `ecalli 18` in the blob, so the value is overwritten before it is read.

`accContractCK_pins7` proves that the contract pins down Ψ_A's handler F (`accHostFn`) except in
ω₇ at id 18 (`HostRel.PinsExcept7`). It is defined from the model's dispatcher and Ω_C alone, so it
adds no assumption about the host.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- **The accumulate contract with `checkpoint`**: `accContractK cap env`, and at id 18 Ω_C's
    continuing outcome (𝖬_C within `cap`; y := x; memory kept) with ω₇ := 0 in place of the gas
    left. -/
def accContractCK (cap : Nat) (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' =>
    accContractK cap env h ω μ x s ω' μ' x' ∨
      (h = 18 ∧ Constants.CgasC ≤ cap ∧ s = .cont ∧ ω' = setR7 ω 0 ∧ μ' = μ ∧ x' = (x.1, x.1))

/-- `accContractCK` at `hostCostMax`. -/
def accContractC (env : AccEnv) : HostRel AccCtx := accContractCK hostCostMax env

/-- `setR7 ω v` and `setR7 ω w` agree except at ω₇. -/
theorem agree7_setR7 (ω : Regs) (v w : Nat) : Agree7 (setR7 ω v) (setR7 ω w) := by
  unfold Agree7 setR7
  rw [Vector.set_set, Vector.set_set]

/-- **The contract pins down Ψ_A's handler except in ω₇ at `checkpoint`.** A step that
    `accContractCK cap env` allows agrees with every non-∞ outcome `accHostFn env` has, for any
    gas, in status, memory and context, and in registers except ω₇ at id 18. -/
theorem accContractCK_pins7 (cap : Nat) (env : AccEnv) :
    (accContractCK cap env).PinsExcept7 (· = 18) (accHostFn env).graph := by
  intro h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ h₁ h₂
  rcases h₁ with h₁ | ⟨rfl, -, rfl, rfl, rfl, rfl⟩
  · exact HostRel.Pins.except7 (· = 18) (accContractK_pins cap env) h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ h₁ h₂
  · obtain ⟨hs₂, g, he⟩ := h₂
    simp only [accHostFn, dispatch_checkpoint, HostResult.mk.injEq] at he
    split at he
    · exact absurd he.1.symm hs₂
    · obtain ⟨rfl, -, rfl, rfl, rfl⟩ := he
      exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl, agree7_setR7 _ _ _⟩⟩

/-- `accContractC` pins down Ψ_A's handler except in ω₇ at `checkpoint`. -/
theorem accContractC_pins7 (env : AccEnv) :
    (accContractC env).PinsExcept7 (· = 18) (accHostFn env).graph :=
  accContractCK_pins7 hostCostMax env

/-- Every step `accContractK` allows, `accContractCK` allows. -/
theorem accContractK_le_CK (cap : Nat) (env : AccEnv) {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {s : PVM.HostStatus} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hk : accContractK cap env h ω μ x s ω' μ' x') : accContractCK cap env h ω μ x s ω' μ' x' :=
  .inl hk

/-- **A `checkpoint` step** under `accContractCK cap`: at an `ecalli 18`, the call continues with
    ω₇ := 0 (the contract's fixed value), memory kept, and y := x. -/
theorem FreeStepsH.checkpointAccK (cap : Nat) (hcap : Constants.CgasC ≤ cap) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 18) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractCK cap env) n (setR7 ω 0) μ (x.1, x.1) i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractCK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.host_decode hd (.inr ⟨rfl, hcap, rfl, rfl, rfl, rfl⟩) rest

/-- **A `checkpoint` step** under `accContractC`. -/
theorem FreeStepsH.checkpointAcc (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 18) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractC env) n (setR7 ω 0) μ (x.1, x.1) i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractC env) i ω μ x i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.checkpointAccK hostCostMax (by decide) env hd rest

/-- **A host-call step at a gas-independent id** under `accContractC`: the call continues with
    the registers, memory and context of Ψ_A's handler F (`accHostFn env`) at the largest gas,
    when that continues. The state-changing accumulate functions (15–17, 19–27) are stepped
    through this way; their outcomes are the model's (`JAM.AccHost.bless` … `provide`). -/
theorem FreeStepsH.accHostC (env : AccEnv) {h : Nat} (hh : AccGasFreeId h)
    {p : ByteArray} {P : Program} {i n : Nat} {hx : UInt64} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli hx) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap) (hId : hx.toNat = h)
    (hs : (accHostFn env h (UInt64.ofNat hostCostMax) ω μ x).status = .cont)
    (rest : FreeStepsH p (accContractC env) n (accHostFn env h (UInt64.ofNat hostCostMax) ω μ x).regs
      (accHostFn env h (UInt64.ofNat hostCostMax) ω μ x).mem
      (accHostFn env h (UInt64.ofNat hostCostMax) ω μ x).ctx i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractC env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  subst hId
  refine FreeStepsH.host_decode hd (.inl ⟨hh, by simp, ?_⟩) rest
  cases ho : accHostFn env hx.toNat (UInt64.ofNat hostCostMax) ω μ x
  simp_all

/-- **A `log` step** (id 100, which Ψ_A's dispatcher does not know: 𝖬_∅ is charged and ω₇ := WHAT,
    GP v0.8.0 eq. `accinvocation`) under `accContractC`. -/
theorem FreeStepsH.logAcc (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractC env) n (setR7 ω Result.WHAT) μ x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractC env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  refine FreeStepsH.host_decode hd (.inl ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩) rest
  simp [accHostFn, AccHost.dispatch, hostCostMax, Constants.Cgasunknown]

end Services.Bootstrap.Acc
