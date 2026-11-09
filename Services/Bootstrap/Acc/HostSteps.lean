import Services.Bootstrap.Acc.Contract
import JAM.Theorems.GrowHeap

/-!
# Host steps under the accumulate contract

The accumulate counterparts of `JAM.FreeStepsH.growHeapK` / `growHeap` and of the `pvm_host`
tactic, for gas-free runs of a service's accumulate under `accContract` (`Contract.lean`). Both
compute the model's Ψ_A handler F (`JAM.accHostFn`, GP v0.8.0 eq. `accinvocation`) on the
general functions: Ω_♊ and every gas-independent id.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- **A `grow_heap` step** under `accContractK cap`. From a memory whose heap is described by
    `HeapPages`, the call continues with ω'_7 = the new top `t` and pages a … t writable, provided
    its cost 275 + 121 (t − h) fits in `cap`. -/
theorem FreeStepsH.growHeapAccK (cap : Nat) (hcap : cap < 2 ^ 64) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat}
    {ω : Regs} {μ : Memory} {x : AccCtx} {a b h : Nat} (t : Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 1) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hb : heapBounds env.code = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b)
    (hbs : b < 2 ^ 32) (ht : growTop (reg ω 7) h b = t)
    (hcost : Constants.CgasGeminiconst + (t - h) * Constants.CgasGeminilinear ≤ cap)
    (rest : FreeStepsH p (accContractK cap env) n (setR7 ω t)
      (μ.setPages a (t - a) (some .write)) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  subst ht
  apply FreeStepsH.host_decode hd _ rest
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, hostGrowHeap, growHeapCore_eq ω μ env.code hb hp hah hhb,
    growTop] at hcost ⊢
  have hw := (ω.get 7).toNat_lt
  simp only [reg] at hw hcost ⊢
  by_cases hc : (ω.get 7).toNat ≤ h ∨ (ω.get 7).toNat > b
  · simp [hc]
  · simp only [hc, ↓reduceIte] at hcost
    have : ¬ cap % 18446744073709551616 <
        Constants.CgasGeminiconst + ((ω.get 7).toNat - h) * Constants.CgasGeminilinear := by
      rw [Nat.mod_eq_of_lt hcap]
      omega
    simp [hc, this]

/-- **A `grow_heap` step** under `accContract`: `growHeapAccK` at `hostCostMax`. -/
theorem FreeStepsH.growHeapAcc (env : AccEnv) {p : ByteArray} {P : Program} {i n : Nat}
    {ω : Regs} {μ : Memory} {x : AccCtx} {a b h : Nat} (t : Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 1) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hb : heapBounds env.code = (a, b)) (hp : HeapPages μ a b h) (hah : a ≤ h) (hhb : h ≤ b)
    (hbs : b < 2 ^ 32) (ht : growTop (reg ω 7) h b = t)
    (hcost : Constants.CgasGeminiconst + (t - h) * Constants.CgasGeminilinear ≤ hostCostMax)
    (rest : FreeStepsH p (accContract env) n (setR7 ω t)
      (μ.setPages a (t - a) (some .write)) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContract env) i ω μ x i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.growHeapAccK hostCostMax (by decide) env t hd hb hp hah hhb hbs ht hcost rest

/-- Prove that a host call's outcome is allowed by `accContract`: check that the id is
    gas-independent, then compute Ψ_A's handler at the largest gas and fix the outcome by `rfl`.
    (The accumulate counterpart of `pvm_host`.) The extra terms are facts for `simp`. -/
syntax "pvm_host_acc" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_host_acc [$hs,*]) => `(tactic| (
    refine ⟨by unfold Services.Bootstrap.Acc.AccGasFreeId; decide, by decide, ?_⟩
    simp only [JAM.hostCostMax, JAM.accHostFn, JAM.AccHost.dispatch, JAM.hostFetch, JAM.hostGrowHeap,
      JAM.hostLookup, JAM.hostRead, JAM.hostInfo, JAM.AccHost.onSelf, JAM.hostWrite, JAM.charged,
      JAM.fetchValue, JAM.writeValue, JAM.memGas, JAM.reg, JAM.setR7,
      JAM.Params.encode_length, PVM.Memory.rangeWritable, PVM.Regs.get, Fin.getElem_fin,
      PVM.regIdx_val_0, PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4,
      PVM.regIdx_val_5, PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9,
      PVM.regIdx_val_10, PVM.regIdx_val_11, PVM.regIdx_val_12, Vector.getElem_ofFn,
      Vector.getElem_set, UInt64.toNat_ofNat', UInt64.toNat_ofNat, UInt64.reduceToNat,
      PVM.getD_some', List.getD_cons_zero, List.getD_cons_succ, Fin.isValue, ↓reduceIte,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceDiv,
      Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, Int.reduceLT, Int.reduceSub, Int.reduceNeg,
      Nat.min_def, List.take_zero, List.drop_zero, PVM.Memory.writeN_nil, beq_self_eq_true,
      List.take_of_length_le, Nat.le_refl, Nat.reduceBEq, Nat.reduceBNe, decide_eq_true_eq,
      Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, Nat.lt_irrefl, Nat.zero_le, Nat.sub_self,
      PVM.two32, PVM.two64, PVM.pageSize, JAM.Constants.CgasY, id_eq, PVM.getElem_regsNF,
      PVM.lookup_cons_nat, List.lookup_nil, Option.getD_none, PVM.set_regsNF, PVM.insertReg, $hs,*]
    rfl))

end Services.Bootstrap.Acc
