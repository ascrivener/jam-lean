import Services.Bootstrap.Acc.Transfer.Hyp
import Services.Bootstrap.Acc.ContractC

/-!
# A `log` step under `accContractS`

`log` (100) is not one of Ψ_A's host calls: 𝖬_∅ is charged and ω₇ := WHAT (GP v0.8.0 eq.
`accinvocation`), the context kept.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap

/-- **A `log` step** under `KeepCtx (accContractS env)`: ω₇ := WHAT, memory, context and stream kept. -/
theorem _root_.PVM.FreeStepsH.logS (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {xq : AccCtx × Stream}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {xq'' : AccCtx × Stream} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (KeepCtx (accContractS env)) n (setR7 ω Result.WHAT) μ xq i'' ω'' μ'' xq'' k) :
    FreeStepsH p (KeepCtx (accContractS env)) i ω μ xq i'' ω'' μ'' xq'' (k + 1) := by
  refine FreeStepsH.host_decode hd ⟨.inl ⟨by unfold AccGasFreeId; decide, by decide, rfl,
    UInt64.ofNat hostCostMax, ?_⟩, rfl⟩ rest
  simp [accHostFn, AccHost.dispatch, UInt64.toNat_ofNat]
  decide

end Services.Bootstrap.Acc
