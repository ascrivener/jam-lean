import Services.Bootstrap.Acc.Handlers.DesignateAlloc
import Services.Bootstrap.Acc.ContractC

/-!
# `Designate`'s host call (49874)

Ω_D (`designate`, id 17, GP v0.8.0 §B.7) with o = ω₇ and z = ω₈: when the 336 · z octets at o are
readable, the call continues. It gives HUH (the key-set size z is not in 𝕍, or the service is not
the delegator, x_s ≠ χ_D) or OK with the staging set ι := the z keys. `designate_eq` is that outcome
at the contract's cap; `call` is the step at 49874.
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateCall

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Ω_D's continuing outcome: the registers with ω₇ := HUH or OK, and the context with the staging
    set replaced on OK. -/
def designateOut (env : AccEnv) (ω : Regs) (x : AccCtx) (z : Nat) (v : List UInt8) : Regs × AccCtx :=
  if !AccHost.validKeyCount env.params.coreCount z || x.1.id ≠ x.1.state.delegator then (setR7 ω Result.HUH, x)
  else (setR7 ω Result.OK, ({ x.1 with state := { x.1.state with staging := AccHost.chunks 336 v z } }, x.2))

/-- Ω_D (id 17) when the 336 · z octets at o are readable, at a cap covering its charge
    1100 + 302 · z: the call continues with `designateOut`, memory kept. -/
theorem designate_eq (cap : Nat) (env : AccEnv) (ω : Regs) (μ : Memory) (x : AccCtx) (o z : Nat)
    (v : List UInt8) (h7 : reg ω 7 = o) (h8 : reg ω 8 = z)
    (hcap : Constants.CgasDconst + z * Constants.CgasDlinear ≤ cap) (hcap' : cap < 18446744073709551616)
    (hr : μ.rangeReadable o (336 * z) = true) (hv : μ.readN o (336 * z) = v) :
    (accHostFn env 17 (UInt64.ofNat cap) ω μ x).status = .cont ∧
    (accHostFn env 17 (UInt64.ofNat cap) ω μ x).regs = (designateOut env ω x z v).1 ∧
    (accHostFn env 17 (UInt64.ofNat cap) ω μ x).mem = μ ∧
    (accHostFn env 17 (UInt64.ofNat cap) ω μ x).ctx = (designateOut env ω x z v).2 := by
  have hm : AccHost.readMem μ o (336 * z) = some v := by unfold AccHost.readMem; rw [hr, hv]; rfl
  unfold designateOut
  simp [accHostFn, AccHost.dispatch, AccHost.designate, AccHost.charge, charged, AccHost.r7,
    AccHost.updX, Nat.mod_eq_of_lt hcap', Nat.not_lt.mpr hcap, h7, h8, hm]
  split <;> simp_all

/-- **The call at 49874** (then the fallthrough at 49876) under `accContractCK cap`, the n keys'
    serialisation readable at ptr (ω₇) and n in ω₈: on to 49877 with `designateOut`'s registers and
    context, memory kept. -/
theorem call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat) (env : AccEnv)
    (x : AccCtx) (ω : Regs) (μ : Memory) (ptr n : Nat) (v : List UInt8)
    (h7 : ω[7] = UInt64.ofNat ptr) (h8 : ω[8] = UInt64.ofNat n) (hptr : ptr < 18446744073709551616)
    (hn : n < 18446744073709551616)
    (hcap : Constants.CgasDconst + n * Constants.CgasDlinear ≤ cap) (hcap' : cap < 18446744073709551616)
    (hr : μ.rangeReadable ptr (336 * n) = true) (hv : μ.readN ptr (336 * n) = v) :
    FreeStepsH p (accContractK cap env) 49874 ω μ x 49877 (designateOut env ω x n v).1 μ
      (designateOut env ω x n v).2 2 := by
  have r7 : reg ω 7 = ptr := by simp [reg, Regs.get, h7, Nat.mod_eq_of_lt hptr]
  have r8 : reg ω 8 = n := by simp [reg, Regs.get, h8, Nat.mod_eq_of_lt hn]
  obtain ⟨hs, hω, hμ, hx⟩ := designate_eq cap env ω μ x ptr n v r7 r8 hcap hcap' hr hv
  refine FreeStepsH.accHostK cap env (h := 17) (by unfold AccGasFreeId; decide)
    (d_49874 (p := p) (P := P)) rfl hs ?_
  rw [hω, hμ, hx]
  pvm_go []

end Services.Bootstrap.Acc.Handlers.DesignateCall
