import JAM.Refine
import JAM.Theorems.HostGas
import PVM.Logic.Det
import PVM.Logic.StepsH

/-!
# A contract for the refine dispatcher that pins down its outcomes

`FreeRunH` and `FreeStepsH` abstract gas away, so the handler a proof steps through is a contract:
which outcomes a host call may have. For the lift to Ψ_M (`PVM.psiM_of_freeRunH`) the contract
must *pin down* the real handler: whatever non-∞ outcome the handler produces, for whatever gas,
must be the one the contract allows.

That holds for host calls whose non-∞ outcome does not depend on the gas left: `grow_heap`,
`fetch` and any id the dispatcher does not know (`log`, for instance). It fails for `gas`, which
reports the gas left. `refineContract` is the dispatcher's graph restricted to those ids, and
`refineContract_pins` proves it pins down the dispatcher.
-/

namespace JAM

open PVM

/-- Two host outcomes that agree except for the gas left. -/
def SameButGas {X : Type} (o₁ o₂ : HostOut X) : Prop :=
  o₁.status = o₂.status ∧ o₁.regs = o₂.regs ∧ o₁.mem = o₂.mem ∧ o₁.ctx = o₂.ctx

/-- The common rules: if the body's outcome does not depend on the gas it is handed and is never
    ∞, the charged function's non-∞ outcomes do not depend on the gas. -/
theorem charged_sameButGas {X : Type} (g : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X)
    (hb : ∀ a b, SameButGas (body ⟨.cont, a, ω, μ, x⟩) (body ⟨.cont, b, ω, μ, x⟩))
    {gas₁ gas₂ : Nat} (h₁ : (charged g gas₁ ω μ x body).status ≠ .oog)
    (h₂ : (charged g gas₂ ω μ x body).status ≠ .oog) :
    SameButGas (charged g gas₁ ω μ x body) (charged g gas₂ ω μ x body) := by
  unfold charged at *
  split at h₁
  · exact absurd rfl h₁
  · split at h₂
    · exact absurd rfl h₂
    · simp only [*]
      exact hb _ _

theorem writeValue_sameButGas {X : Type} (s : HostStatus) (a b : Int) (ω : Regs) (μ : Memory)
    (x : X) (v : Except Unit (Option (List UInt8))) (o f z : Nat) :
    SameButGas (writeValue ⟨s, a, ω, μ, x⟩ v o f z) (writeValue ⟨s, b, ω, μ, x⟩ v o f z) := by
  unfold writeValue SameButGas
  dsimp only
  repeat' split
  all_goals simp

/-- The host-call ids whose non-∞ outcome does not depend on the gas: `grow_heap`, `fetch`, and
    any id the refine dispatcher does not know. -/
def GasFreeId (h : Nat) : Prop := h = 1 ∨ h = 2 ∨ 14 < h


/-- The protocol parameters always encode to 122 octets (`fetch` case 0). -/
@[simp] theorem Params.encode_length (c : Params) : c.encode.length = 122 := by
  unfold Params.encode
  simp only [Codec.fixed, List.length_append, PVM.Num.length_encodeLE]

namespace RefineHost

theorem dispatch_sameButGas (env : Env) {h : Nat} (hh : GasFreeId h) (ω : Regs) (μ : Memory)
    (c : RefineCtx) {gas₁ gas₂ : Nat} (h₁ : (dispatch env h gas₁ ω μ c).status ≠ .oog)
    (h₂ : (dispatch env h gas₂ ω μ c).status ≠ .oog) :
    SameButGas (dispatch env h gas₁ ω μ c) (dispatch env h gas₂ ω μ c) := by
  rcases hh with rfl | rfl | hlt
  · -- grow_heap
    simp only [dispatch] at *
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
  · -- fetch
    simp only [dispatch] at *
    exact charged_sameButGas _ _ _ _ _ (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
  · -- an unknown id
    have hu : ∀ g, dispatch env h g ω μ c = unknown g ω μ c := by
      intro g; unfold dispatch; split <;> first | omega | rfl
    simp only [hu] at h₁ h₂ ⊢
    unfold unknown at h₁ h₂ ⊢
    unfold SameButGas
    dsimp only at h₁ h₂ ⊢
    split at h₁ <;> split at h₂ <;> simp_all
    simp only [show ¬((gas₁ : Int) - Constants.Cgasunknown < 0) by omega,
      show ¬((gas₂ : Int) - Constants.Cgasunknown < 0) by omega, ↓reduceIte]

end RefineHost

/-- The refine dispatcher's outcomes for the gas-independent ids. -/
def refineContract (env : RefineHost.Env) : HostRel RefineCtx := fun h ω μ x s ω' μ' x' =>
  GasFreeId h ∧ (toHostFn (RefineHost.dispatch env)).graph h ω μ x s ω' μ' x'

/-- **The contract pins down the dispatcher**: a step allowed by `refineContract` is the only
    non-∞ outcome the real handler has, for any gas. -/
theorem refineContract_pins (env : RefineHost.Env) :
    (refineContract env).Pins (toHostFn (RefineHost.dispatch env)).graph := by
  intro h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ ⟨hh, hs₁, g₁, he₁⟩ ⟨hs₂, g₂, he₂⟩
  simp only [toHostFn, HostResult.mk.injEq] at he₁ he₂
  obtain ⟨e1s, -, e1r, e1m, e1c⟩ := he₁
  obtain ⟨e2s, -, e2r, e2m, e2c⟩ := he₂
  have n₁ : (RefineHost.dispatch env h g₁.toNat ω μ x).status ≠ .oog := by rw [e1s]; exact hs₁
  have n₂ : (RefineHost.dispatch env h g₂.toNat ω μ x).status ≠ .oog := by rw [e2s]; exact hs₂
  obtain ⟨a, b, c, d⟩ := RefineHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  exact ⟨e1s ▸ e2s ▸ a, e1r ▸ e2r ▸ b, e1m ▸ e2m ▸ c, e1c ▸ e2c ▸ d⟩

/-! ## The host-step tactic -/

/-- Prove that a host call's outcome is allowed by `refineContract`: check the id is gas-free,
    then compute the dispatcher at the largest gas and fix the outcome by `rfl` (cf. `pvm_simp`
    for ordinary steps). The extra terms are facts for `simp`. -/
syntax "pvm_host" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_host [$hs,*]) => `(tactic| (
    refine ⟨by unfold JAM.GasFreeId; decide, by decide, UInt64.ofNat (2 ^ 64 - 1), ?_⟩
    simp only [JAM.toHostFn, JAM.RefineHost.dispatch, JAM.hostFetch, JAM.hostGrowHeap, JAM.charged,
      JAM.fetchValue, JAM.writeValue, JAM.RefineHost.unknown, JAM.memGas, JAM.reg, JAM.setR7,
      JAM.Params.encode_length, PVM.Memory.rangeWritable, PVM.Regs.get, Fin.getElem_fin,
      PVM.regIdx_val_0, PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4,
      PVM.regIdx_val_5, PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9,
      PVM.regIdx_val_10, PVM.regIdx_val_11, PVM.regIdx_val_12, Vector.getElem_ofFn,
      Vector.getElem_set, UInt64.toNat_ofNat', UInt64.toNat_ofNat, UInt64.reduceToNat,
      Option.getD_some, List.getD_cons_zero, List.getD_cons_succ, Fin.isValue, ↓reduceIte,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceDiv,
      Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, Int.reduceLT, Int.reduceSub, Int.reduceNeg,
      Nat.min_def, List.take_zero, List.drop_zero, PVM.Memory.writeN_nil, beq_self_eq_true,
      Bool.true_or, Bool.or_true, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, Nat.lt_irrefl, Nat.zero_le, Nat.sub_self,
      PVM.two32, PVM.two64, PVM.pageSize, JAM.Constants.CgasY, id_eq, PVM.getElem_regsNF,
      PVM.lookup_cons_nat, List.lookup_nil, Option.getD_none, PVM.set_regsNF, PVM.insertReg, $hs,*]
    rfl))

end JAM
