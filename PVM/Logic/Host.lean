import PVM.Logic.Free
import PVM.Theorems.Invocation

/-!
# Gas-free runs with abstract host calls

A host *contract* `R : HostRel X` says which effects a host call may have: given the call id and
the machine state and context at the call, which (exit reason, registers, memory, context) it may
produce. A handler `f` *respects* `R` if every result it produces is allowed.

* `FreeRunH`: gas-free runs of Ψ_H* in which every host call takes some step allowed by `R`.
* `psiHStar_freeRunH`: **every Ψ_H* run under a handler respecting `R` that does not end in ∞ is a
  `FreeRunH`.**
* `psiM_free`: the same for Ψ_M: its output (when not ∞) is the gas-free output of some
  `FreeRunH` from Y's initial state.

So a property proved for all gas-free runs under a contract holds for the real Ψ_M under every
handler that meets the contract, whatever the gas.
-/

namespace PVM

variable {X : Type}

/-- A host contract: `R h ω μ x s ω' μ' x'` allows host call `h` in state (ω, μ, x) to end with
    handler status `s` and state (ω', μ', x'). -/
abbrev HostRel (X : Type) :=
  Nat → Regs → Memory → X → HostStatus → Regs → Memory → X → Prop

/-- `f` only ever does what `R` allows (gas aside). -/
def HostFn.Respects (f : HostFn X) (R : HostRel X) : Prop :=
  ∀ h g ω μ x, R h ω μ x (f h g ω μ x).status (f h g ω μ x).regs (f h g ω μ x).mem (f h g ω μ x).ctx

/-- Gas-free runs of Ψ_H* under contract `R`, ending with exit reason ε and state (ω', μ', x'). -/
inductive FreeRunH (p : ByteArray) (R : HostRel X) :
    Nat → Regs → Memory → X → Status → Regs → Memory → X → Prop where
  /-- The machine exits with something other than a host call. -/
  | exit {i ω μ x ε e ω' μ'} : FreeRun p i ω μ ε e ω' μ' → (∀ h, ε ≠ .host h) →
      FreeRunH p R i ω μ x ε ω' μ' x
  /-- A host call that continues: resume at ı + 1 + skip(ı). -/
  | host {i ω μ x h e ω' μ' ω'' μ'' x'' ε ω''' μ''' x'''} :
      FreeRun p i ω μ (.host h) e ω' μ' → R h.toNat ω' μ' x .cont ω'' μ'' x'' →
      FreeRunH p R (blobNext p e) ω'' μ'' x'' ε ω''' μ''' x''' →
      FreeRunH p R i ω μ x ε ω''' μ''' x'''
  /-- A host call that ends the run with the handler's ∎, ☇ or ∞. -/
  | hostStop {i ω μ x h e ω' μ' s ω'' μ'' x''} :
      FreeRun p i ω μ (.host h) e ω' μ' → R h.toNat ω' μ' x s ω'' μ'' x'' → s ≠ .cont →
      FreeRunH p R i ω μ x s.toStatus ω'' μ'' x''

/-- **Gas abstraction for Ψ_H\*.** For a handler that respects `R` and does not add gas, every
    run that does not end in ∞ is a gas-free run under `R`. -/
theorem psiHStar_freeRunH (p : ByteArray) (R : HostRel X) (f : HostFn X)
    (hf : f.GasNonIncreasing) (hR : f.Respects R) :
    ∀ (m i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (x : X),
      runMeasure p i gas ch < m → (psiHStar p i gas ch ω μ f x).status ≠ .oog →
      FreeRunH p R i ω μ x (psiHStar p i gas ch ω μ f x).status (psiHStar p i gas ch ω μ f x).regs
        (psiHStar p i gas ch ω μ f x).mem (psiHStar p i gas ch ω μ f x).ctx := by
  intro m
  induction m with
  | zero => intros; omega
  | succ m ih =>
    intro i gas ch ω μ x hm hno
    rw [psiHStar_eq p i gas ch ω μ f hf x] at hno ⊢
    dsimp only at hno ⊢
    generalize hr : psi p i gas ch ω μ = r at hno ⊢
    cases hst : r.status <;> simp only [hst] at hno ⊢
    case host h =>
      have hps : (psi p i gas ch ω μ).status = .host h := by rw [hr, hst]
      obtain ⟨e, hrun, hpc⟩ := psi_freeRun (by rw [hps]; simp)
      rw [hr, hst] at hrun hpc
      simp [exitPcOf] at hpc
      have hRy := hR h.toNat r.gas r.regs r.mem x
      generalize hy : f h.toNat r.gas r.regs r.mem x = y at hno ⊢ hRy
      cases hys : y.status <;> simp only [hys] at hno ⊢ hRy
      case cont =>
        have hlt : runMeasure p (blobNext p r.pc) y.gas r.charged < m := by
          have h1 := psi_host_measure hps
          rw [hr] at h1
          have h2 := runMeasure_mono_gas p (blobNext p r.pc) r.charged
            (hy ▸ hf h.toNat r.gas r.regs r.mem x)
          omega
        have := ih _ _ _ _ _ _ hlt hno
        rw [hpc] at this ⊢
        exact .host hrun hRy this
      case oog => simp [HostStatus.toStatus] at hno
      all_goals exact .hostStop hrun hRy (by simp)
    case oog => exact absurd rfl hno
    all_goals
      have hps : (psi p i gas ch ω μ).status ≠ .oog := by rw [hr, hst]; simp
      obtain ⟨e, hrun, _⟩ := psi_freeRun hps
      rw [hr, hst] at hrun
      exact .exit hrun (by simp)

/-- The output Ψ_M's R gives for an exit (ε, ω', μ'), gas aside (GP §A.8). -/
def freeOutput (ε : Status) (ω : Regs) (μ : Memory) : InvOutput :=
  let a := (ω.get 7).toNat
  let n := (ω.get 8).toNat
  match ε with
  | .oog => .oog
  | .halt => if μ.rangeReadable a n then .ok ⟨(μ.readN a n).toArray⟩ else .ok ByteArray.empty
  | _ => .panic

/-- Ψ_M's output is not ∞. -/
def InvOutput.isOog : InvOutput → Bool
  | .oog => true
  | _ => false

/-- **Gas abstraction for Ψ_M.** For a handler that respects `R` and does not add gas, if Ψ_M does
    not report ∞ then either Y failed (output ☇, context unchanged), or its output and final
    context come from a gas-free run under `R` from Y's initial state. -/
theorem psiM_free (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    (R : HostRel X) (f : HostFn X) (hf : f.GasNonIncreasing) (hR : f.Respects R)
    (hno : (psiM b i gas a f x).2.1.isOog = false) :
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
    have hrun := psiHStar_freeRunH p R f hf hR _ i gas false ω μ x (Nat.lt_succ_self _)
      (by unfold psiH at hr; rw [hr]; exact hstat)
    unfold psiH at hr
    rw [hr] at hrun
    refine ⟨p, ω, μ, r.status, r.regs, r.mem, r.ctx, rfl, hrun, ?_⟩
    simp only [invocationResult, freeOutput]
    cases r.status <;> simp <;> split <;> rfl

end PVM
