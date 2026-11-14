import JAM.Theorems.RefineContract

namespace Services.Bootstrap.Refine.HostSteps

open PVM JAM

/-- **A `log` (100) step** under `refineContractK cap` (1000 ≤ cap): the refine dispatcher does not know
    id 100, so it charges 𝖬_∅ and returns WHAT in ω₇; memory and the context are kept (GP v0.8.0
    Appendix B.4, eq. `refinemutator`). The message is not looked at. -/
theorem FreeStepsH.logRef (cap : Nat) (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : RefineHost.Env)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : RefineCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (refineContractK cap env) n (setR7 ω Result.WHAT) μ x i'' ω'' μ'' x'' k) :
    FreeStepsH p (refineContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  have hc : ¬ ((cap : Int) - ((1000 : Nat) : Int) < 0) := by omega
  refine ⟨by unfold GasFreeId; decide, by decide, ?_⟩
  simp only [toHostFn, RefineHost.dispatch, RefineHost.unknown, UInt64.toNat_ofNat', UInt64.reduceToNat,
    Nat.reducePow, Constants.Cgasunknown, Nat.mod_eq_of_lt hcap.2, hc, ↓reduceIte]

/-- The context after Ω_E (GP v0.8.0 Appendix B.4, `export`) of the octets at ω₇ (length ω₈): the segment
    of min(ω₈, 𝖶_G) octets, zero-padded to 𝖶_G, appended to the exports while ς + |**e**| < 𝖶_X. -/
def exportCtx (env : RefineHost.Env) (ω : Regs) (μ : Memory) (x : RefineCtx) : RefineCtx :=
  if env.exportOffset + x.2.length ≥ Constants.Cmaxpackageexports then x
  else (x.1, x.2 ++ [μ.readN (reg ω 7) (min (reg ω 8) Constants.Csegmentsize) ++
    List.replicate (Constants.Csegmentsize - min (reg ω 8) Constants.Csegmentsize) 0])

/-- ω₇ after Ω_E: FULL, or the new segment's index ς + |**e**|. -/
def exportR7 (env : RefineHost.Env) (x : RefineCtx) : Nat :=
  if env.exportOffset + x.2.length ≥ Constants.Cmaxpackageexports then Result.FULL
  else env.exportOffset + x.2.length

/-- **An `export` (8) step** under `refineContractK cap` (𝖬_E ≤ cap), the octets readable: Ω_E's outcome,
    `exportCtx` and ω₇ := `exportR7`; memory kept. -/
theorem FreeStepsH.exportRef (cap : Nat) (hcap : 3521 ≤ cap ∧ cap < 2 ^ 64) (env : RefineHost.Env)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : RefineCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 8) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hrd : μ.rangeReadable (reg ω 7) (min (reg ω 8) Constants.Csegmentsize) = true)
    (rest : FreeStepsH p (refineContractK cap env) n (setR7 ω (exportR7 env x)) μ (exportCtx env ω μ x)
      i'' ω'' μ'' x'' k) :
    FreeStepsH p (refineContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  have hc : ¬ cap < 3521 := by omega
  refine ⟨by unfold GasFreeId; decide, by decide, ?_⟩
  simp only [toHostFn, RefineHost.dispatch, RefineHost.exportSeg, charged, UInt64.toNat_ofNat',
    UInt64.reduceToNat, Nat.reducePow, Constants.CgasE, Nat.mod_eq_of_lt hcap.2, hc, ↓reduceIte, hrd,
    Bool.not_true, Bool.false_eq_true, exportCtx, exportR7]
  split <;> simp [RefineHost.r7]

end Services.Bootstrap.Refine.HostSteps
