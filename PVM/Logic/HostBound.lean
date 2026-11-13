import PVM.Logic.Host
import PVM.Theorems.Termination

/-!
# Gas-free runs under a contract that holds only up to a gas bound

`psiHStar_freeRunH` needs the handler to respect the contract at every gas. A contract stated at a
fixed gas cap (each call's outcome is the model's at gas `cap`) is respected only at gas ≤ cap: above
the cap a call may succeed where the contract's run would be ∞. Ψ_H*'s gas never grows (Ψ's
does not, GP §A.4, and the handler does not add gas), so from an initial gas ≤ B every host call
sees gas ≤ B. Hence:
* `psiHStar_freeRunH_le`: if `f` respects `R` at every gas ≤ B whenever the call is not ∞, every
  Ψ_H* run from gas ≤ B that does not end in ∞ is a `FreeRunH` under `R`;
* `psiM_free_le`: the same for Ψ_M (GP §A.8), as `psiM_free`.
-/

namespace PVM

variable {X : Type}

/-- `f` respects `R` at every gas ≤ B, for the calls that do not run out of gas. -/
def HostFn.RespectsLe (f : HostFn X) (R : HostRel X) (B : Nat) : Prop :=
  ∀ h g ω μ x, g.toNat ≤ B → (f h g ω μ x).status ≠ .oog →
    R h ω μ x (f h g ω μ x).status (f h g ω μ x).regs (f h g ω μ x).mem (f h g ω μ x).ctx

theorem psiHStar_freeRunH_le (p : ByteArray) (R : HostRel X) (f : HostFn X) (B : Nat)
    (hf : f.GasNonIncreasing) (hR : f.RespectsLe R B) :
    ∀ (m i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (x : X),
      runMeasure p i gas ch < m → gas.toNat ≤ B → (psiHStar p i gas ch ω μ f x).status ≠ .oog →
      FreeRunH p R i ω μ x (psiHStar p i gas ch ω μ f x).status (psiHStar p i gas ch ω μ f x).regs
        (psiHStar p i gas ch ω μ f x).mem (psiHStar p i gas ch ω μ f x).ctx := by
  intro m
  induction m with
  | zero => intros; omega
  | succ m ih =>
    intro i gas ch ω μ x hm hB hno
    have hgl := psi_gas_le p i gas ch ω μ
    rw [psiHStar_eq p i gas ch ω μ f hf x] at hno ⊢
    dsimp only at hno ⊢
    generalize hr : psi p i gas ch ω μ = r at hno ⊢ hgl
    cases hst : r.status <;> simp only [hst] at hno ⊢
    case host h =>
      have hps : (psi p i gas ch ω μ).status = .host h := by rw [hr, hst]
      obtain ⟨e, hrun, hpc⟩ := psi_freeRun (by rw [hps]; simp)
      rw [hr, hst] at hrun hpc
      simp [exitPcOf] at hpc
      have hRy := hR h.toNat r.gas r.regs r.mem x (by omega)
      have hgy := hf h.toNat r.gas r.regs r.mem x
      generalize hy : f h.toNat r.gas r.regs r.mem x = y at hno ⊢ hRy hgy
      cases hys : y.status <;> simp only [hys] at hno ⊢ hRy
      case cont =>
        have hlt : runMeasure p (blobNext p r.pc) y.gas r.charged < m := by
          have h1 := psi_host_measure hps
          rw [hr] at h1
          have h2 := runMeasure_mono_gas p (blobNext p r.pc) r.charged hgy
          omega
        have := ih _ _ _ _ _ _ hlt (by omega) hno
        rw [hpc] at this ⊢
        exact .host hrun (hRy (by simp)) this
      case oog => simp [HostStatus.toStatus] at hno
      all_goals exact .hostStop hrun (hRy (by simp)) (by simp)
    case oog => exact absurd rfl hno
    all_goals
      have hps : (psi p i gas ch ω μ).status ≠ .oog := by rw [hr, hst]; simp
      obtain ⟨e, hrun, _⟩ := psi_freeRun hps
      rw [hr, hst] at hrun
      exact .exit hrun (by simp)

/-- **Gas abstraction for Ψ_M, up to a gas bound.** As `psiM_free`, for a handler that respects `R`
    only at gas ≤ B, from an initial gas ≤ B. -/
theorem psiM_free_le (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    (R : HostRel X) (f : HostFn X) (B : Nat) (hf : f.GasNonIncreasing) (hR : f.RespectsLe R B)
    (hB : gas.toNat ≤ B) (hno : (psiM b i gas a f x).2.1.isOog = false) :
    (standardInit b a = none ∧ (psiM b i gas a f x).2 = (.panic, x)) ∨
      ∃ p ω μ ε ω' μ' x', standardInit b a = some (p, ω, μ) ∧
        FreeRunH p R i ω μ x ε ω' μ' x' ∧ (psiM b i gas a f x).2 = (freeOutput ε ω' μ', x') := by
  unfold psiM at hno ⊢
  split at hno
  · rename_i hY; left; simp [hY]
  · rename_i p ω μ hY
    right
    simp only [hY]
    generalize hr : psiH p i gas ω μ f x = r at hno ⊢
    have hstat : r.status ≠ .oog := by
      intro h; simp [invocationResult, h, InvOutput.isOog] at hno
    have hrun := psiHStar_freeRunH_le p R f B hf hR _ i gas false ω μ x (Nat.lt_succ_self _) hB
      (by unfold psiH at hr; rw [hr]; exact hstat)
    unfold psiH at hr
    rw [hr] at hrun
    refine ⟨p, ω, μ, r.status, r.regs, r.mem, r.ctx, rfl, hrun, ?_⟩
    simp only [invocationResult, freeOutput]
    cases r.status <;> simp <;> split <;> rfl

end PVM
