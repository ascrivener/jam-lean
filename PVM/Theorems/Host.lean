import PVM.Machine
import PVM.Theorems.Decode

/-!
# Only `ecalli` exits with a host call

The only instruction whose execution yields h̵ is `ecalli` (GP §A.5.2), and the host-call
identifier is its own immediate ν_X. We prove this for the mutation table (`exec`), for the
single step Ψ₁ (`step`) and for the full machine Ψ (`psi`).
-/

namespace PVM

namespace Program

@[simp] theorem sjump_ne_host (P : Program) (i : Nat) (b : Int) (h : UInt64) :
    (P.sjump i b).1 ≠ .host h := by
  unfold sjump; split <;> simp

@[simp] theorem branch_ne_host (P : Program) (i : Nat) (b : Int) (c : Bool) (h : UInt64) :
    (P.branch i b c).1 ≠ .host h := by
  unfold branch; repeat' split
  all_goals simp

@[simp] theorem djump_ne_host (P : Program) (i a : Nat) (h : UInt64) :
    (P.djump i a).1 ≠ .host h := by
  unfold djump; dsimp only; repeat' split
  all_goals simp

/-- The mutation table yields h̵ × h exactly for `ecalli` with immediate h. -/
theorem exec_status_eq_host_iff (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (μ : Memory)
    (h : UInt64) : (P.exec i ins ω μ).status = .host h ↔ ins = .oneImm .ecalli h := by
  constructor
  · intro hs
    cases ins with
    | oneImm op x => cases op; simp_all [exec]
    | noArgs op => cases op <;> simp_all [exec]
    | regImm op a x => cases op <;> simp_all [exec]
    | twoRegImm op a b x => cases op <;> simp_all [exec]
    | regImmOffset op a x y => cases op <;> simp_all [exec]
    | twoRegTwoImm op a b x y => cases op; simp_all [exec]
    | oneOffset op x => cases op; simp_all [exec]
    | _ => simp_all [exec]
  · rintro rfl; simp [exec]

/-- If Ψ₁ exits with h̵ × h, the instruction at ı decodes to `ecalli` with immediate h. -/
theorem step_host {P : Program} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs} {μ : Memory}
    {h : UInt64} (hs : (P.step i gas ch ω μ).status = .host h) :
    P.decode i = some (.oneImm .ecalli h) := by
  have hεg : (P.chargeGas i gas ch).1 = .cont ∨ (P.chargeGas i gas ch).1 = .oog := by
    unfold chargeGas; split
    · simp
    · dsimp only; split <;> simp
  simp only [step] at hs
  generalize P.chargeGas i gas ch = g at hs hεg
  generalize hm : P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ = m at hs
  generalize memoryException μ m.reads m.writes = e at hs
  obtain ⟨εg, gas', ch'⟩ := g
  rcases hεg with rfl | rfl
  · cases e with
    | some e' => cases e' <;> simp [finalState] at hs
    | none =>
      simp only [finalState, ne_eq, not_true_eq_false, ↓reduceIte] at hs
      cases hdec : P.decode i with
      | none => rw [hdec] at hm; subst hm; simp [exec] at hs
      | some ins =>
        rw [hdec] at hm; subst hm
        rw [(exec_status_eq_host_iff P i ins ω μ h).1 hs]
  · simp [finalState] at hs

end Program

/-- If `runFuel` (Ψ with fuel) exits with h̵ × h, the program deblobs at the exit index and the
    instruction there decodes to `ecalli` with immediate h. -/
theorem runFuel_host {p : ByteArray} {n i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} {r : Result} {h : UInt64}
    (hr : runFuel p n i gas ch ω μ = some r) (hs : r.status = .host h) :
    ∃ P, deblob p r.exitPc = some P ∧ P.decode r.exitPc = some (.oneImm .ecalli h) := by
  induction n generalizing i gas ch ω μ with
  | zero => simp [runFuel] at hr
  | succ n ih =>
    unfold runFuel at hr
    cases hP : deblob p i with
    | none => rw [hP] at hr; cases hr; simp at hs
    | some P =>
      rw [hP] at hr
      dsimp only at hr
      split at hr
      · exact ih hr
      · cases hr; simp_all
      · cases hr; simp_all
      · cases hr
        exact ⟨P, hP, Program.step_host hs⟩

/-- **Only `ecalli` exits with a host call.** If Ψ exits with h̵ × h, then the instruction
    that caused the exit decodes to `ecalli` and h is its immediate. -/
theorem psi_host {p : ByteArray} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs} {μ : Memory}
    {h : UInt64} (hs : (psi p i gas ch ω μ).status = .host h) :
    ∃ P, deblob p (psi p i gas ch ω μ).exitPc = some P ∧
      P.decode (psi p i gas ch ω μ).exitPc = some (.oneImm .ecalli h) := by
  unfold psi at hs ⊢
  cases hr : runFuel p (stepBound p i gas ch) i gas ch ω μ with
  | none => rw [hr] at hs; simp at hs
  | some r =>
    simp only [hr, Option.getD_some] at hs ⊢
    exact runFuel_host hr hs

end PVM
