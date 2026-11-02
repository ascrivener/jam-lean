import PVM.Theorems.Termination

/-!
# Gas-free execution

Gas only ever stops a run early: the gas stage of Ψ₁ either continues, leaving the instruction's
effect untouched, or reports ∞. So for any property of the form "if the run ends with ε ≠ ∞,
then …" we can forget gas entirely.

* `Program.freeStep`: Ψ₁ without its gas stage, (ε*, ı*, ω*, μ*) from ε^μ and the mutation table.
* `FreeRun`: big-step runs of the gas-free machine, ending the way Ψ ends.
* `psi_freeRun`: **every Ψ run that does not end in ∞ is a `FreeRun`** with the same exit reason,
  registers and memory, and Ψ's returned ı is determined by the exit index.

Because the gas-free machine has no blocks to charge, straight-line code is just consecutive
steps; the basic-block structure and the gas cost model never appear in proofs built on it.
-/

namespace PVM

namespace Program

/-- Ψ₁ without the gas stage (GP §A.4): (ε^μ, ı, ω, μ) if ε^μ ≠ ▸, else the regular execution. -/
def freeStep (P : Program) (i : Nat) (ω : Regs) (μ : Memory) : Status × Nat × Regs × Memory :=
  let m := P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ
  finalState .cont i ω μ m (memoryException μ m.reads m.writes)

/-- When Ψ₁ does not run out of gas, its (ε*, ı*, ω*, μ*) is the gas-free step's. -/
theorem step_eq_freeStep {P : Program} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} (h : (P.step i gas ch ω μ).status ≠ .oog) :
    ((P.step i gas ch ω μ).status, (P.step i gas ch ω μ).pc, (P.step i gas ch ω μ).regs,
      (P.step i gas ch ω μ).mem) = P.freeStep i ω μ := by
  have hcg := P.chargeGas_cases i gas ch
  have hεg : (P.chargeGas i gas ch).1 = .cont := by
    cases ch
    · rcases hcg.1 rfl with ⟨_, h1, _⟩ | h1
      · rw [h1]
      · exfalso; apply h; simp [step, h1, finalState]
    · rw [hcg.2 rfl]
  simp only [step, freeStep, hεg]

end Program

/-- How a gas-free run ends at index `i`, mirroring Ψ's exit cases (GP §A.1): a deblob failure
    (☇ with the state unchanged), or a step whose ε* ≠ ▸ (∎ and ☇ keep ω*, μ*; F and h̵ keep the
    state before the step). -/
inductive FreeExit (p : ByteArray) : Nat → Regs → Memory → Status → Regs → Memory → Prop where
  | invalid {i ω μ} : deblob p i = none → FreeExit p i ω μ .panic ω μ
  | step {i ω μ P ε j ω' μ'} : deblob p i = some P → P.freeStep i ω μ = (ε, j, ω', μ') →
      ε ≠ .cont →
      FreeExit p i ω μ ε (if ε = .halt ∨ ε = .panic then ω' else ω)
        (if ε = .halt ∨ ε = .panic then μ' else μ)

/-- One continuing gas-free step. -/
def FreeNext (p : ByteArray) (i : Nat) (ω : Regs) (μ : Memory) (i' : Nat) (ω' : Regs)
    (μ' : Memory) : Prop :=
  ∃ P, deblob p i = some P ∧ P.freeStep i ω μ = (.cont, i', ω', μ')

/-- Gas-free runs: `FreeRun p i ω μ ε e ω' μ'` says that from (ı, ω, μ) the program continues
    through any number of steps and then exits with ε at index `e`, leaving (ω', μ'). -/
inductive FreeRun (p : ByteArray) : Nat → Regs → Memory → Status → Nat → Regs → Memory → Prop where
  | exit {i ω μ ε ω' μ'} : FreeExit p i ω μ ε ω' μ' → FreeRun p i ω μ ε i ω' μ'
  | next {i ω μ i' ω' μ' ε e ω'' μ''} : FreeNext p i ω μ i' ω' μ' →
      FreeRun p i' ω' μ' ε e ω'' μ'' → FreeRun p i ω μ ε e ω'' μ''

/-- Ψ's returned ı for an exit with ε at index `e`: 0 on ∎ and ☇, `e` otherwise (GP §A.1). -/
def exitPcOf (ε : Status) (e : Nat) : Nat := if ε = .halt ∨ ε = .panic then 0 else e

theorem runFuel_freeRun {p : ByteArray} :
    ∀ (n i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (r : Result),
      runFuel p n i gas ch ω μ = some r → r.status ≠ .oog →
      ∃ e, FreeRun p i ω μ r.status e r.regs r.mem ∧ r.pc = exitPcOf r.status e := by
  intro n
  induction n with
  | zero => intros; simp_all [runFuel]
  | succ n ih =>
    intro i gas ch ω μ r hr hno
    unfold runFuel at hr
    cases hP : deblob p i with
    | none =>
      rw [hP] at hr; cases hr
      exact ⟨i, .exit (.invalid hP), by simp [exitPcOf]⟩
    | some P =>
      rw [hP] at hr
      dsimp only at hr
      generalize hs : P.step i gas ch ω μ = s at hr
      have hfree := fun h => (hs ▸ Program.step_eq_freeStep (P := P) (i := i) (gas := gas)
        (ch := ch) (ω := ω) (μ := μ) (hs ▸ h))
      cases hst : s.status <;> simp only [hst] at hr
      case cont =>
        obtain ⟨e, hrun, hpc⟩ := ih _ _ _ _ _ _ hr hno
        have hf := hfree (by rw [hst]; simp)
        rw [hst] at hf
        exact ⟨e, .next ⟨P, hP, hf.symm⟩ hrun, hpc⟩
      case oog => cases hr; simp at hno
      all_goals
        cases hr
        have hf := hfree (by rw [hst]; simp)
        rw [hst] at hf
        refine ⟨i, .exit ?_, by simp [exitPcOf]⟩
        have := FreeExit.step (p := p) hP hf.symm (by simp)
        simpa using this

/-- **Gas abstraction for Ψ.** Every Ψ run that does not end in ∞ is a gas-free run with the
    same exit reason, registers and memory; Ψ's ı is 0 on ∎ and ☇ and the exit index otherwise. -/
theorem psi_freeRun {p : ByteArray} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs} {μ : Memory}
    (hno : (psi p i gas ch ω μ).status ≠ .oog) :
    ∃ e, FreeRun p i ω μ (psi p i gas ch ω μ).status e (psi p i gas ch ω μ).regs
      (psi p i gas ch ω μ).mem ∧ (psi p i gas ch ω μ).pc = exitPcOf (psi p i gas ch ω μ).status e :=
  runFuel_freeRun _ i gas ch ω μ _ (psi_eq_runFuel p (runMeasure p i gas ch + 1) i gas ch ω μ
    (by omega)) hno

end PVM
