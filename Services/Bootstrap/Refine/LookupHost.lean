import Services.Bootstrap.Refine.HostSteps

/-!
# The `historical_lookup` (7) step under the refine contract

Refine's eager `Lookup` handler calls Ω_H (GP v0.8.0 Appendix B.4, `historical_lookup`) twice through the SDK's
`foreign_historical_lookup` (49015): once with an empty buffer for the length, then with a buffer of that length
for the preimage. Its service id ω₇ is a zero-extended u32, never 2^64 − 1, so Ω_H looks up **d**[ω₇].
-/

namespace Services.Bootstrap.Refine.LookupHost

open PVM JAM

/-- The preimage Ω_H finds for the registers ω (service ω₇ ≠ 2^64 − 1, hash at ω₈): Λ(**d**[ω₇], t, μ_{ω₈…+32})
    (GP v0.8.0 Appendix B.4, `historical_lookup`). -/
def lookupVal (env : RefineHost.Env) (ω : Regs) (μ : Memory) : Option (List UInt8) :=
  (env.accounts.get? (reg ω 7)).bind fun a => a.historicalLookup env.lookupSlot (μ.readN (reg ω 8) 32)

/-- ω₇ after Ω_H: NONE, or the preimage's length. -/
def lookupR7 (env : RefineHost.Env) (ω : Regs) (μ : Memory) : Nat :=
  match lookupVal env ω μ with
  | none => Result.NONE
  | some v => v.length

/-- Memory after Ω_H: the preimage's octets v_{f…+l} written at ω₉, with f = min(ω₁₀, |v|) and
    l = min(ω₁₁, |v| − f); unchanged when there is no preimage. -/
def lookupMem (env : RefineHost.Env) (ω : Regs) (μ : Memory) : Memory :=
  match lookupVal env ω μ with
  | none => μ
  | some v => μ.writeN (reg ω 9) ((v.drop (min (reg ω 10) v.length)).take
      (min (reg ω 11) (v.length - min (reg ω 10) v.length)))

/-- **A `historical_lookup` (7) step** under `refineContractK cap` (cap at least Ω_H's charge
    𝖬_{H,c} + 𝔊(𝖬_{H,ℓ}, ω₁₁)), service ω₇ ≠ 2^64 − 1, the hash readable and the output range writable: ω₇ :=
    `lookupR7`, memory := `lookupMem`, the context kept. -/
theorem FreeStepsH.lookupRef (cap : Nat) (env : RefineHost.Env)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : RefineCtx} {k : Nat}
    (hcap : Constants.CgasHconst + memGas Constants.CgasHlinear (reg ω 11) ≤ cap ∧ cap < 2 ^ 64)
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 7) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (h7 : reg ω 7 ≠ 2 ^ 64 - 1)
    (hrd : μ.rangeReadable (reg ω 8) 32 = true)
    (hwr : ∀ v, lookupVal env ω μ = some v →
      μ.rangeWritable (reg ω 9) (min (reg ω 11) (v.length - min (reg ω 10) v.length)) = true)
    (rest : FreeStepsH p (refineContractK cap env) n (setR7 ω (lookupR7 env ω μ))
      (lookupMem env ω μ) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (refineContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  have hc : ¬ cap < Constants.CgasHconst + memGas Constants.CgasHlinear (reg ω 11) := by omega
  refine ⟨by unfold GasFreeId; decide, by decide, ?_⟩
  have hv : (if reg ω 7 = 2 ^ 64 - 1 ∧ env.accounts.contains env.service then env.accounts.get? env.service
      else env.accounts.get? (reg ω 7)) = env.accounts.get? (reg ω 7) := by
    rw [ite_eq_right (fun h => absurd h.1 h7)]
  simp only [toHostFn, RefineHost.dispatch, RefineHost.historicalLookup, charged, UInt64.toNat_ofNat',
    UInt64.reduceToNat, Nat.reducePow, Nat.mod_eq_of_lt hcap.2, hc, ↓reduceIte, hrd, Bool.not_true,
    Bool.false_eq_true, hv]
  have hwr' := hwr
  unfold lookupVal at hwr'
  unfold lookupR7 lookupMem lookupVal
  cases hl : (env.accounts.get? (reg ω 7)).bind
      (fun a => a.historicalLookup env.lookupSlot (μ.readN (reg ω 8) 32)) with
  | none => simp [writeValue, Memory.rangeWritable]
  | some v =>
    have hw := hwr' v hl
    simp [writeValue, hw]

end Services.Bootstrap.Refine.LookupHost
