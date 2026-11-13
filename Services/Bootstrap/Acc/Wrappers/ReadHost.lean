import Services.Bootstrap.ASemLemmas
import Services.Bootstrap.Acc.Impl.ContractS

/-!
# One `read` (4) or `write` (5) of this service's storage, as an `accContractS` step

The SDK's `get` makes Ω_R calls with ω₇ = NONE (this service), the key at ω₈ (ω₉ octets) and the
output at ω₁₀ (offset ω₁₁ = 0, length ω₁₂). Under `accContractS` such a call continues:
- ω₇ is the stored value's length, or NONE;
- the first ω₁₂ octets of the value are written at ω₁₀;
- the context and the stream are kept (`read_stepS`).
GP v0.8.0 Appendix B, Ω_R.

The SDK's `set` makes Ω_W calls with the key at ω₇ (ω₈ octets) and the value at ω₉ (ω₁₀ octets); such
a call continues with ω₇ := FULL or the old value's length or NONE (`writeR7`), the memory kept, x's
account updated unless FULL (`writeSelf`), y and the stream kept (`write_stepS`, Ω_W).
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

/-- What Ω_W leaves in ω₇: FULL if the new balance is below the threshold, else the old value's
    length or NONE. -/
def writeR7 (self : ServiceAccount) (key value : List UInt8) : Nat :=
  if (writeAcct self key value).minBalance > (writeAcct self key value).balance then Result.FULL
  else (self.storage.get? key).map List.length |>.getD Result.NONE

/-- What Ω_W leaves of the account: unchanged if FULL, else with the key set. -/
def writeSelf (self : ServiceAccount) (key value : List UInt8) : ServiceAccount :=
  if (writeAcct self key value).minBalance > (writeAcct self key value).balance then self
  else writeAcct self key value

/-- **A `write` of this service's storage is an `accContractS` step**: ω₇ := `writeR7`, the memory
    kept, x's account := `writeSelf`, y and the stream kept. -/
theorem write_stepS (env : AccEnv) (ω : Regs) (μ : Memory) (xq : AccCtx × Stream) (kO kZ vO vZ : Nat)
    (key value : List UInt8) (h7 : reg ω 7 = kO) (h8 : reg ω 8 = kZ) (h9 : reg ω 9 = vO) (h10 : reg ω 10 = vZ)
    (hkZ : kZ < 2 ^ 32) (hvZ : vZ < 2 ^ 32)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (hv : μ.rangeReadable vO vZ = true) (hval : μ.readN vO vZ = value) (hvl : value.length = vZ) :
    accContractS env 5 ω μ xq .cont (setR7 ω (writeR7 xq.1.1.self key value)) μ
      (((xq.1.1.setSelf (writeSelf xq.1.1.self key value)), xq.1.2), xq.2) := by
  refine .inl ⟨by unfold AccGasFreeId; decide, by simp, rfl, UInt64.ofNat (2 ^ 63), ?_⟩
  have e := hostWrite_eval (2 ^ 63) ω μ xq.1.1.self kO kZ vO vZ key value h7 h8 h9 h10
    (by unfold memGas Constants.CgasWconst Constants.CgasWkeylinear Constants.CgasWvallinear; omega)
    hk hkey hv hval hvl
  simp only [accHostFn, AccHost.dispatch, AccHost.onSelf, UInt64.toNat_ofNat_of_lt' (show 2 ^ 63 < 2 ^ 64 by decide), e,
    writeR7, writeSelf]
  split <;> rfl

end Services.Bootstrap.Acc
