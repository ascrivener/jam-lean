import Services.Bootstrap.ASemLemmas
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# One `read` (4) of this service's storage, as an `accContractS` step

The SDK's `get` makes Ω_R calls with ω₇ = NONE (this service), the key at ω₈ (ω₉ octets) and the
output at ω₁₀ (offset ω₁₁ = 0, length ω₁₂). Under `accContractS` such a call continues:
- ω₇ is the stored value's length, or NONE;
- the first ω₁₂ octets of the value are written at ω₁₀;
- the context and the stream are kept (`read_stepS`).
GP v0.8.0 Appendix B, Ω_R.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.ASem

/-- What Ω_R leaves: ω₇ and the memory. -/
def readRegs (ω : Regs) (v : Option (List UInt8)) : Regs :=
  setR7 ω (match v with | none => Result.NONE | some v => v.length)

def readMem (μ : Memory) (o z : Nat) (v : Option (List UInt8)) : Memory :=
  match v with | none => μ | some v => μ.writeN o (v.take z)

/-- **A `read` of this service's storage is an `accContractS` step.** -/
theorem read_stepS (env : AccEnv) (ω : Regs) (μ : Memory) (xq : AccCtx × Stream) (kO kZ o z : Nat)
    (key : List UInt8) (h7 : reg ω 7 = 2 ^ 64 - 1) (h8 : reg ω 8 = kO) (h9 : reg ω 9 = kZ)
    (h10 : reg ω 10 = o) (h11 : reg ω 11 = 0) (h12 : reg ω 12 = z) (hkZ : kZ < 2 ^ 32) (hz : z < 2 ^ 32)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (hw : μ.rangeWritable o (min z ((xq.1.1.self.storage.get? key).map List.length |>.getD 0)) = true) :
    accContractS env 4 ω μ xq .cont (readRegs ω (xq.1.1.self.storage.get? key))
      (readMem μ o z (xq.1.1.self.storage.get? key)) xq := by
  refine .inl ⟨by unfold AccGasFreeId; decide, by simp, rfl, UInt64.ofNat (2 ^ 63), ?_⟩
  have e := hostRead_self (2 ^ 63) ω μ xq.1.1.self xq.1.1.id xq.1.1.state.accounts () kO kZ o z key h7 h8 h9 h10
    h11 h12 (by unfold memGas Constants.CgasRconst Constants.CgasRkeylinear Constants.CgasRvallinear; omega)
    hk hkey hw
  simp only [accHostFn, AccHost.dispatch, UInt64.toNat_ofNat_of_lt' (show 2 ^ 63 < 2 ^ 64 by decide), e]
  cases xq.1.1.self.storage.get? key <;> rfl

end Services.Bootstrap.Acc
