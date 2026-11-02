import PVM.Logic.Steps

/-!
# Chains of gas-free steps through host calls

`FreeStepsH p R i ω μ x i' ω' μ' x'`: from (ı, ω, μ, x) the machine continues, through ordinary
steps and through host calls whose outcome the contract `R` allows (resuming at ı + 1 + skip(ı)),
to (ı', ω', μ', x'). It is to `FreeRunH` what `FreeSteps` is to `FreeRun`: chains compose and end
in a run (`FreeStepsH.run`), so a proof can follow a program across its host calls piece by piece.
-/

namespace PVM

variable {X : Type}

/-- Zero or more continuing steps, some of them host calls allowed by `R`. -/
inductive FreeStepsH (p : ByteArray) (R : HostRel X) :
    Nat → Regs → Memory → X → Nat → Regs → Memory → X → Prop where
  | refl {i ω μ x} : FreeStepsH p R i ω μ x i ω μ x
  | next {i ω μ x i' ω' μ' i'' ω'' μ'' x''} : FreeNext p i ω μ i' ω' μ' →
      FreeStepsH p R i' ω' μ' x i'' ω'' μ'' x'' → FreeStepsH p R i ω μ x i'' ω'' μ'' x''
  | host {i ω μ x P h j ω₁ μ₁ ω' μ' x' i'' ω'' μ'' x''} : deblob p i = some P →
      P.freeStep i ω μ = (.host h, j, ω₁, μ₁) → R h.toNat ω μ x .cont ω' μ' x' →
      FreeStepsH p R (P.next i) ω' μ' x' i'' ω'' μ'' x'' → FreeStepsH p R i ω μ x i'' ω'' μ'' x''

theorem blobNext_of_deblob {p : ByteArray} {i : Nat} {P : Program} (h : deblob p i = some P) :
    blobNext p i = P.next i := by
  simp [blobNext, (deblob_some h).1]

/-- A continuing step before a run with host calls. -/
theorem FreeRunH.cons_next {p : ByteArray} {R : HostRel X} {i ω μ x i' ω' μ' ε ω'' μ'' x''}
    (hn : FreeNext p i ω μ i' ω' μ') (hr : FreeRunH p R i' ω' μ' x ε ω'' μ'' x'') :
    FreeRunH p R i ω μ x ε ω'' μ'' x'' := by
  cases hr with
  | exit hrun hne => exact .exit (.next hn hrun) hne
  | host hrun hR hrest => exact .host (.next hn hrun) hR hrest
  | hostStop hrun hR hs => exact .hostStop (.next hn hrun) hR hs

namespace FreeStepsH

variable {p : ByteArray} {R : HostRel X}

theorem trans {i ω μ x i' ω' μ' x' i'' ω'' μ'' x''} (h₁ : FreeStepsH p R i ω μ x i' ω' μ' x')
    (h₂ : FreeStepsH p R i' ω' μ' x' i'' ω'' μ'' x'') : FreeStepsH p R i ω μ x i'' ω'' μ'' x'' := by
  induction h₁ with
  | refl => exact h₂
  | next hn _ ih => exact .next hn (ih h₂)
  | host hP hs hR _ ih => exact .host hP hs hR (ih h₂)

/-- A chain of ordinary steps is a chain. -/
theorem of_steps {i ω μ i' ω' μ'} (x : X) (h : FreeSteps p i ω μ i' ω' μ') :
    FreeStepsH p R i ω μ x i' ω' μ' x := by
  induction h with
  | refl => exact .refl
  | next hn _ ih => exact .next hn ih

/-- **A chain followed by a run is a run.** -/
theorem run {i ω μ x i' ω' μ' x' ε ω'' μ'' x''} (h : FreeStepsH p R i ω μ x i' ω' μ' x')
    (hr : FreeRunH p R i' ω' μ' x' ε ω'' μ'' x'') : FreeRunH p R i ω μ x ε ω'' μ'' x'' := by
  induction h with
  | refl => exact hr
  | next hn _ ih => exact FreeRunH.cons_next hn (ih hr)
  | @host i ω μ x P h j ω₁ μ₁ ω' μ' x' i'' ω'' μ'' x'' hP hs hR _ ih =>
    have hexit : FreeRun p i ω μ (.host h) i ω μ := by
      have := FreeExit.step (p := p) hP hs (by simp)
      simpa using FreeRun.exit this
    exact .host hexit hR (by rw [blobNext_of_deblob hP]; exact ih hr)

/-- One ordinary step at an index whose instruction the code facts give (cf.
    `FreeSteps.step_decode`). -/
theorem step_decode {P : Program} {i : Nat} {ins : Instr} {n : Nat} {ω : Regs} {μ : Memory} {x : X}
    {i' : Nat} {ω' : Regs} {μ' : Memory} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : X}
    (hd : deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n)
    (hs : (let m := P.exec i ins ω μ
           Program.finalState .cont i ω μ m (memoryException μ m.reads m.writes)) = (.cont, i', ω', μ'))
    (rest : FreeStepsH p R i' ω' μ' x i'' ω'' μ'' x'') : FreeStepsH p R i ω μ x i'' ω'' μ'' x'' :=
  .next ⟨P, hd.1, by rw [Program.freeStep_of_decode ω μ hd.2.1]; exact hs⟩ rest

/-- A host call `ecalli h` at an index the code facts give, with an outcome `R` allows; the run
    resumes at ı + 1 + skip(ı) = n. -/
theorem host_decode {P : Program} {i : Nat} {h : UInt64} {n : Nat} {ω : Regs} {μ : Memory} {x : X}
    {ω' : Regs} {μ' : Memory} {x' : X} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : X}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli h) ∧ P.next i = n)
    (hR : R h.toNat ω μ x .cont ω' μ' x')
    (rest : FreeStepsH p R n ω' μ' x' i'' ω'' μ'' x'') : FreeStepsH p R i ω μ x i'' ω'' μ'' x'' := by
  refine .host (j := P.next i) (ω₁ := ω) (μ₁ := μ) hd.1 ?_ hR (hd.2.2 ▸ rest)
  rw [Program.freeStep_of_decode ω μ hd.2.1]
  simp [Program.exec, Program.finalState, memoryException]

end FreeStepsH

end PVM
