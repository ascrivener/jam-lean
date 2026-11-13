import Services.Bootstrap.Acc.CkSites
import Services.Bootstrap.Acc.CkDead
import Services.Bootstrap.CodeAOk
import Services.Bootstrap.Acc.ContractC
import JAM.Theorems.HostGas

/-!
# ω₇ is dead after every `checkpoint` in bootstrap's code

`deadAfter_checkpoint`: bootstrap's PVM blob satisfies `PVM.DeadAfter … (· = 18)`, the condition
of the lift `PVM.psiM_of_freeRunH7` for a contract that fixes `checkpoint`'s ω₇
(`Acc.accContractC`). `ecalli 18` is only at 8490, 9944 and 11889 (`CkSites.ckSites_ok`), and
ω₇ is dead after each (`CkDead`).
-/

namespace Services.Bootstrap.Acc

open PVM PVM.NatBlob Services.Bootstrap.Blob Services.Bootstrap.CodeA

/-- **ω₇ is dead after every `ecalli 18`** in bootstrap's PVM blob. -/
theorem deadAfter_checkpoint : DeadAfter (ba N 11888 83235) (· = 18) := by
  intro P hP k hk e he
  subst hk
  obtain ⟨P', hok⟩ := checkCode_sound CodeCheck.checkCode_ok
  have h1 : P' = P := Option.some.inj (hok.parse.symm.trans hP)
  have h2 : P' = CodeCheck.prog := Option.some.inj (hok.parse.symm.trans CodeCheck.parse)
  subst h1
  haveI := CodeACheck.hasCodeA hok
  have hs := CkSites.ckSites_ok e (by rw [← h2]; exact he)
  simp only [CkSites.ckSites, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · rw [(d_8490 (p := ba N 11888 83235) (P := P')).2.2.1]; exact CkDead.p8492 (P := P')
  · rw [(d_9944 (p := ba N 11888 83235) (P := P')).2.2.1]; exact CkDead.k9946 (P := P')
  · rw [(d_11889 (p := ba N 11888 83235) (P := P')).2.2.1]; exact CkDead.p11891 (P := P')

/-- **Ψ_M of bootstrap's accumulate is determined by one gas-free run under `accContractC`**
    (`checkpoint` with ω₇ := 0): Ψ_M runs out of gas, or returns that run's output and context
    (GP §A.8, eq. `accinvocation`). -/
theorem psiM_of_freeRunH_accC (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray)
    (x : JAM.AccCtx) (env : JAM.AccEnv) {ω : Regs} {μ : Memory}
    (hY : standardInit b a = some (ba N 11888 83235, ω, μ))
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : JAM.AccCtx}
    (hrun : FreeRunH (ba N 11888 83235) (accContractC env) i ω μ x ε ω' μ' x') :
    (psiM b i gas a (JAM.accHostFn env) x).2.1.isOog = true ∨
      (psiM b i gas a (JAM.accHostFn env) x).2 = (freeOutput ε ω' μ', x') :=
  psiM_of_freeRunH7 b i gas a x _ (JAM.accHostFn_gasNonIncreasing env) (· = 18) _
    (accContractC_pins7 env) hY deadAfter_checkpoint hrun

/-- **`psiM_of_freeRunH_accC` at any cap**: a gas-free run of bootstrap under `accContractCK cap`
    (each host call's outcome the model's at gas `cap`) determines Ψ_M: ∞, or that run's output and
    context. -/
theorem psiM_of_freeRunH_accCK (cap : Nat) (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray)
    (x : JAM.AccCtx) (env : JAM.AccEnv) {ω : Regs} {μ : Memory}
    (hY : standardInit b a = some (ba N 11888 83235, ω, μ))
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : JAM.AccCtx}
    (hrun : FreeRunH (ba N 11888 83235) (accContractCK cap env) i ω μ x ε ω' μ' x') :
    (psiM b i gas a (JAM.accHostFn env) x).2.1.isOog = true ∨
      (psiM b i gas a (JAM.accHostFn env) x).2 = (freeOutput ε ω' μ', x') :=
  psiM_of_freeRunH7 b i gas a x _ (JAM.accHostFn_gasNonIncreasing env) (· = 18) _
    (accContractCK_pins7 cap env) hY deadAfter_checkpoint hrun

end Services.Bootstrap.Acc
