import PVM.Logic.Steps

/-!
# Chains of gas-free steps through host calls

`FreeStepsH p R i ω μ x i' ω' μ' x' n`: from (ı, ω, μ, x) the machine continues, through ordinary
steps and through host calls whose outcome the contract `R` allows (resuming at ı + 1 + skip(ı)),
to (ı', ω', μ', x'), in at most `n` steps (each ordinary step and each host call counts one), each
at an index whose basic block costs at most `stepCostCap` (`CostOk`). It
is to `FreeRunH` what `FreeSteps` is to `FreeRun`: chains compose and end in a run
(`FreeStepsH.run`), so a proof can follow a program across its host calls piece by piece. The
count is what bounds the gas a run needs (`PVM.Logic.GasBound`): each step charges at most one
block cost, at most `stepCostCap`, and each host call what its handler charges.
-/

namespace PVM

variable {X : Type}

/-- The basic block containing ı costs at most `stepCostCap`, if the program deblobs at ı. -/
def CostOk (p : ByteArray) (i : Nat) : Prop :=
  ∀ P, deblob p i = some P → P.blockCost (P.blockStartOf i) ≤ stepCostCap

theorem CostOk.of {p : ByteArray} {i : Nat} {P : Program} (hP : deblob p i = some P)
    (hc : P.blockCost (P.blockStartOf i) ≤ stepCostCap) : CostOk p i := by
  intro P' hP'
  rw [hP] at hP'
  cases hP'
  exact hc

/-- Zero or more continuing steps, some of them host calls allowed by `R`, at most `n` of them. -/
inductive FreeStepsH (p : ByteArray) (R : HostRel X) :
    Nat → Regs → Memory → X → Nat → Regs → Memory → X → Nat → Prop where
  | refl {i ω μ x} : FreeStepsH p R i ω μ x i ω μ x 0
  /-- A bound can be loosened. -/
  | pad {i ω μ x i' ω' μ' x' n} : FreeStepsH p R i ω μ x i' ω' μ' x' n →
      FreeStepsH p R i ω μ x i' ω' μ' x' (n + 1)
  | next {i ω μ x i' ω' μ' i'' ω'' μ'' x'' n} : FreeNext p i ω μ i' ω' μ' → CostOk p i →
      FreeStepsH p R i' ω' μ' x i'' ω'' μ'' x'' n → FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (n + 1)
  | host {i ω μ x P h j ω₁ μ₁ ω' μ' x' i'' ω'' μ'' x'' n} : deblob p i = some P →
      P.blockCost (P.blockStartOf i) ≤ stepCostCap →
      P.freeStep i ω μ = (.host h, j, ω₁, μ₁) → R h.toNat ω μ x .cont ω' μ' x' →
      FreeStepsH p R (P.next i) ω' μ' x' i'' ω'' μ'' x'' n → FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (n + 1)

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

/-- A bound on the steps can be raised. -/
theorem mono {i ω μ x i' ω' μ' x' n m} (h : FreeStepsH p R i ω μ x i' ω' μ' x' n) (hnm : n ≤ m) :
    FreeStepsH p R i ω μ x i' ω' μ' x' m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  clear hnm
  induction k with
  | zero => exact h
  | succ k ih => exact .pad ih

theorem trans {i ω μ x i' ω' μ' x' i'' ω'' μ'' x'' n₁ n₂} (h₁ : FreeStepsH p R i ω μ x i' ω' μ' x' n₁)
    (h₂ : FreeStepsH p R i' ω' μ' x' i'' ω'' μ'' x'' n₂) :
    FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (n₁ + n₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | pad _ ih => rw [Nat.add_right_comm]; exact .pad (ih h₂)
  | next hn hc _ ih => rw [Nat.add_right_comm]; exact .next hn hc (ih h₂)
  | host hP hc hs hR _ ih => rw [Nat.add_right_comm]; exact .host hP hc hs hR (ih h₂)

/-- A chain under a contract is one under any contract that allows at least its continuing host
    calls. -/
theorem weaken {R' : HostRel X}
    (hR : ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → R' h ω μ x .cont ω' μ' x')
    {i ω μ x i' ω' μ' x' n} (hs : FreeStepsH p R i ω μ x i' ω' μ' x' n) :
    FreeStepsH p R' i ω μ x i' ω' μ' x' n := by
  induction hs with
  | refl => exact .refl
  | pad _ ih => exact .pad ih
  | next hn hc _ ih => exact .next hn hc ih
  | host hP hc hs hr _ ih => exact .host hP hc hs (hR _ _ _ _ _ _ _ hr) ih

/-- `trans` with the counts the other way round, for a goal whose count ends in a literal. -/
theorem trans' {i ω μ x i' ω' μ' x' i'' ω'' μ'' x'' n₁ n₂} (h₁ : FreeStepsH p R i ω μ x i' ω' μ' x' n₁)
    (h₂ : FreeStepsH p R i' ω' μ' x' i'' ω'' μ'' x'' n₂) :
    FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (n₂ + n₁) := by
  rw [Nat.add_comm]; exact h₁.trans h₂

/-- **Call a summary**: a summary gives a run to `t` and a fact `Q` about the registers there; the
    proof continues from `t` for every register file with `Q`. -/
theorem bind {i ω μ x t μ' i'' ω'' μ'' x'' n₁ n₂} {Q : Regs → Prop}
    (h : ∃ ω', FreeStepsH p R i ω μ x t ω' μ' x n₁ ∧ Q ω')
    (k : ∀ ω', Q ω' → FreeStepsH p R t ω' μ' x i'' ω'' μ'' x'' n₂) :
    FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (n₁ + n₂) := by
  obtain ⟨ω', h₁, hq⟩ := h
  exact h₁.trans (k ω' hq)

/-- A chain, then a summary's existential conclusion from where it ends, within a bound `N`
    (the chain's and the summary's counts are found first; the bound is decided last). -/
theorem ex_trans {i ω μ x i₁ ω₁ μ₁ t n₁ n₂ N} {Q : Regs → Memory → Prop}
    (h₁ : FreeStepsH p R i ω μ x i₁ ω₁ μ₁ x n₁)
    (h₂ : ∃ ω' μ', FreeStepsH p R i₁ ω₁ μ₁ x t ω' μ' x n₂ ∧ Q ω' μ') (hle : n₁ + n₂ ≤ N) :
    ∃ ω' μ', FreeStepsH p R i ω μ x t ω' μ' x N ∧ Q ω' μ' := by
  obtain ⟨ω', μ', h, hq⟩ := h₂
  exact ⟨ω', μ', (h₁.trans h).mono (by omega), hq⟩

/-- **Call a summary** in an existential goal: the summary's run to `t` with `Q`, then for every
    register file with `Q` a run from `t` with the goal's property, within a bound `N`. -/
theorem bind_ex {i ω μ x t μ₁ t' n₁ n₂ N} {Q : Regs → Prop} {S : Regs → Memory → Prop}
    (h : ∃ ω₁, FreeStepsH p R i ω μ x t ω₁ μ₁ x n₁ ∧ Q ω₁)
    (k : ∀ ω₁, Q ω₁ → ∃ ω' μ', FreeStepsH p R t ω₁ μ₁ x t' ω' μ' x n₂ ∧ S ω' μ')
    (hle : n₁ + n₂ ≤ N) :
    ∃ ω' μ', FreeStepsH p R i ω μ x t' ω' μ' x N ∧ S ω' μ' := by
  obtain ⟨ω₁, h₁, hq⟩ := h
  obtain ⟨ω', μ', h₂, hs⟩ := k ω₁ hq
  exact ⟨ω', μ', (h₁.trans h₂).mono (by omega), hs⟩

/-- **A chain followed by a run is a run.** -/
theorem run {i ω μ x i' ω' μ' x' ε ω'' μ'' x'' n} (h : FreeStepsH p R i ω μ x i' ω' μ' x' n)
    (hr : FreeRunH p R i' ω' μ' x' ε ω'' μ'' x'') : FreeRunH p R i ω μ x ε ω'' μ'' x'' := by
  induction h with
  | refl => exact hr
  | pad _ ih => exact ih hr
  | next hn _ _ ih => exact FreeRunH.cons_next hn (ih hr)
  | @host i ω μ x P h j ω₁ μ₁ ω' μ' x' i'' ω'' μ'' x'' n hP _ hs hR _ ih =>
    have hexit : FreeRun p i ω μ (.host h) i ω μ := by
      have := FreeExit.step (p := p) hP hs (by simp)
      simpa using FreeRun.exit this
    exact .host hexit hR (by rw [blobNext_of_deblob hP]; exact ih hr)

/-- One ordinary step at an index whose instruction the code facts give (cf.
    `FreeSteps.step_decode`). -/
theorem step_decode {P : Program} {i : Nat} {ins : Instr} {n : Nat} {ω : Regs} {μ : Memory} {x : X}
    {i' : Nat} {ω' : Regs} {μ' : Memory} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : X} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hs : (let m := P.exec i ins ω μ
           Program.finalState .cont i ω μ m (memoryException μ m.reads m.writes)) = (.cont, i', ω', μ'))
    (rest : FreeStepsH p R i' ω' μ' x i'' ω'' μ'' x'' k) : FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (k + 1) :=
  .next ⟨P, hd.1, by rw [Program.freeStep_of_decode ω μ hd.2.1]; exact hs⟩ (.of hd.1 hd.2.2.2) rest

/-- A host call `ecalli h` at an index the code facts give, with an outcome `R` allows; the run
    resumes at ı + 1 + skip(ı) = n. -/
theorem host_decode {P : Program} {i : Nat} {h : UInt64} {n : Nat} {ω : Regs} {μ : Memory} {x : X}
    {ω' : Regs} {μ' : Memory} {x' : X} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : X} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli h) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (hR : R h.toNat ω μ x .cont ω' μ' x')
    (rest : FreeStepsH p R n ω' μ' x' i'' ω'' μ'' x'' k) : FreeStepsH p R i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  refine .host (j := P.next i) (ω₁ := ω) (μ₁ := μ) hd.1 hd.2.2.2 ?_ hR (hd.2.2.1 ▸ rest)
  rw [Program.freeStep_of_decode ω μ hd.2.1]
  simp [Program.exec, Program.finalState, memoryException]

end FreeStepsH

end PVM
