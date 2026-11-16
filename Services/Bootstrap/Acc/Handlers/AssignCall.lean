import Services.Bootstrap.Acc.Handlers.AssignAlloc
import Services.Bootstrap.Acc.ContractC

/-!
# `Assign`'s host call (40397)

Ω_A (`assign`, id 16, GP v0.8.0 §B.7) with c = ω₇, o = ω₈, a = ω₉: when the 32 · Q octets at o are
readable (Q the authorizer queue's size), the call continues with CORE (c ≥ C), HUH (the service is
not c's assigner), WHO (a ≥ 2³²) or OK, with c's queue and assigner set. `assign_eq` is that outcome
at the contract's cap (𝖬_A = 1818 ≤ cap); `call` is the step at 40397.
-/

namespace Services.Bootstrap.Acc.Handlers.AssignCall

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Ω_A's continuing outcome: the registers with ω₇ := CORE, HUH, WHO or OK, and the context with
    c's authorizer queue and assigner set on OK. -/
def assignOut (env : AccEnv) (ω : Regs) (x : AccCtx) (core a : Nat) (q : List UInt8) : Regs × AccCtx :=
  if core ≥ env.params.coreCount then (setR7 ω Result.CORE, x)
  else if x.1.id ≠ x.1.state.assigners.getD core 0 then (setR7 ω Result.HUH, x)
  else if a ≥ 2 ^ 32 then (setR7 ω Result.WHO, x)
  else (setR7 ω Result.OK, ({ x.1 with state := { x.1.state with
    authQueue := x.1.state.authQueue.set core (AccHost.chunks 32 q env.params.authQueueSize),
    assigners := x.1.state.assigners.set core a } }, x.2))

/-- Ω_A (id 16) when the 32 · Q octets at o are readable, at a cap covering 𝖬_A: the call continues
    with `assignOut`, memory kept. -/
theorem assign_eq (cap : Nat) (env : AccEnv) (ω : Regs) (μ : Memory) (x : AccCtx) (core o a : Nat)
    (q : List UInt8) (h7 : reg ω 7 = core) (h8 : reg ω 8 = o) (h9 : reg ω 9 = a)
    (hcap : Constants.CgasA ≤ cap) (hcap' : cap < 18446744073709551616)
    (hr : μ.rangeReadable o (32 * env.params.authQueueSize) = true)
    (hq : μ.readN o (32 * env.params.authQueueSize) = q) :
    (accHostFn env 16 (UInt64.ofNat cap) ω μ x).status = .cont ∧
    (accHostFn env 16 (UInt64.ofNat cap) ω μ x).regs = (assignOut env ω x core a q).1 ∧
    (accHostFn env 16 (UInt64.ofNat cap) ω μ x).mem = μ ∧
    (accHostFn env 16 (UInt64.ofNat cap) ω μ x).ctx = (assignOut env ω x core a q).2 := by
  have hm : AccHost.readMem μ o (32 * env.params.authQueueSize) = some q := by
    unfold AccHost.readMem; rw [hr, hq]; rfl
  unfold assignOut
  simp [accHostFn, AccHost.dispatch, AccHost.assign, AccHost.charge, charged, AccHost.r7,
    AccHost.updX, Nat.mod_eq_of_lt hcap', Nat.not_lt.mpr hcap, h7, h8, h9, hm]
  split <;> (try split) <;> (try split) <;> simp_all

/-- **The call at 40397** (then the fallthrough at 40399) under `accContractCK cap`: on to 40400
    with `assignOut`'s registers and context, memory kept. -/
theorem call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat) (env : AccEnv)
    (x : AccCtx) (ω : Regs) (μ : Memory) (core ptr a : Nat) (q : List UInt8)
    (h7 : ω[7] = UInt64.ofNat core) (h8 : ω[8] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat a)
    (hc : core < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (ha : a < 18446744073709551616)
    (hcap : Constants.CgasA ≤ cap) (hcap' : cap < 18446744073709551616)
    (hr : μ.rangeReadable ptr (32 * env.params.authQueueSize) = true)
    (hq : μ.readN ptr (32 * env.params.authQueueSize) = q) :
    FreeStepsH p (accContractK cap env) 40397 ω μ x 40400 (assignOut env ω x core a q).1 μ
      (assignOut env ω x core a q).2 2 := by
  have r7 : reg ω 7 = core := by simp [reg, Regs.get, h7, Nat.mod_eq_of_lt hc]
  have r8 : reg ω 8 = ptr := by simp [reg, Regs.get, h8, Nat.mod_eq_of_lt hptr]
  have r9 : reg ω 9 = a := by simp [reg, Regs.get, h9, Nat.mod_eq_of_lt ha]
  obtain ⟨hs, hω, hμ, hx⟩ := assign_eq cap env ω μ x core ptr a q r7 r8 r9 hcap hcap' hr hq
  refine FreeStepsH.accHostK cap env (h := 16) (by unfold AccGasFreeId; decide)
    (d_40397 (p := p) (P := P)) rfl hs ?_
  rw [hω, hμ, hx]
  pvm_go []

end Services.Bootstrap.Acc.Handlers.AssignCall
