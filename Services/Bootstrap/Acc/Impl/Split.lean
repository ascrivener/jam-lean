import PVM.Logic.Det
import PVM.Logic.StepsH

/-!
# Runs through a known segment

Under a contract that pins down its own outcomes, a gas-free run with host calls is determined by
its start. So a run from a state that is known to go through a segment (`FreeStepsH`) continues,
from the segment's end, as a run with the same exit (`FreeRunH.of_steps`). This is how universal
statements ("every run from here …") are built from the segment lemmas, which give one run each.
-/

namespace PVM

variable {X : Type}

/-- A run from a state with a continuing step continues after it. -/
theorem FreeRun.uncons_next {p : ByteArray} {i ω μ i' ω' μ' ε e ω'' μ''}
    (hn : FreeNext p i ω μ i' ω' μ') (hr : FreeRun p i ω μ ε e ω'' μ'') : FreeRun p i' ω' μ' ε e ω'' μ'' := by
  cases hr with
  | exit he => exact (he.not_next hn).elim
  | next hn' hr' =>
    obtain ⟨rfl, rfl, rfl⟩ := hn.det hn'
    exact hr'

/-- A run with host calls from a state with a continuing step continues after it. -/
theorem FreeRunH.uncons_next {p : ByteArray} {R : HostRel X} {i ω μ x i' ω' μ' ε ω'' μ'' x''}
    (hn : FreeNext p i ω μ i' ω' μ') (hr : FreeRunH p R i ω μ x ε ω'' μ'' x'') :
    FreeRunH p R i' ω' μ' x ε ω'' μ'' x'' := by
  cases hr with
  | exit hrun hne => exact .exit (hrun.uncons_next hn) hne
  | host hrun hR hrest => exact .host (hrun.uncons_next hn) hR hrest
  | hostStop hrun hR hs => exact .hostStop (hrun.uncons_next hn) hR hs

/-- A run to a host call from a state whose step is that host call stops there, the state kept. -/
theorem FreeRun.at_host {p : ByteArray} {P : Program} {i ω μ h j ω₁ μ₁ ε e ω' μ'}
    (hP : deblob p i = some P) (hs : P.freeStep i ω μ = (.host h, j, ω₁, μ₁))
    (hr : FreeRun p i ω μ ε e ω' μ') : ε = .host h ∧ e = i ∧ ω' = ω ∧ μ' = μ := by
  cases hr with
  | exit he =>
    cases he with
    | invalid hn => rw [hP] at hn; cases hn
    | step hP' hs' hne =>
      rw [hP] at hP'; cases hP'
      rw [hs] at hs'; cases hs'
      simp
  | next hn _ =>
    obtain ⟨P', hP', hs'⟩ := hn
    rw [hP] at hP'; cases hP'
    rw [hs] at hs'; cases hs'

/-- **A run through a known segment continues from its end**, under a contract that pins itself. -/
theorem FreeRunH.of_steps {p : ByteArray} {R : HostRel X} (hR : R.Pins R)
    {i ω μ x i₁ ω₁ μ₁ x₁ n ε ω' μ' x'}
    (hs : FreeStepsH p R i ω μ x i₁ ω₁ μ₁ x₁ n) (hr : FreeRunH p R i ω μ x ε ω' μ' x') :
    FreeRunH p R i₁ ω₁ μ₁ x₁ ε ω' μ' x' := by
  induction hs with
  | refl => exact hr
  | pad _ ih => exact ih hr
  | next hn _ _ ih => exact ih (hr.uncons_next hn)
  | host hP _ hst hRs _ ih =>
    cases hr with
    | exit hrun hne =>
      obtain ⟨rfl, -⟩ := FreeRun.at_host hP hst hrun
      exact (hne _ rfl).elim
    | host hrun hR' hrest =>
      obtain ⟨hh, he, hω, hμ⟩ := FreeRun.at_host hP hst hrun
      cases hh; subst he; subst hω; subst hμ
      obtain ⟨-, rfl, rfl, rfl⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hRs hR'
      rw [blobNext_of_deblob hP] at hrest
      exact ih hrest
    | hostStop hrun hR' hst' =>
      obtain ⟨hh, he, hω, hμ⟩ := FreeRun.at_host hP hst hrun
      cases hh; subst hω; subst hμ
      obtain ⟨hs1, -⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hRs hR'
      exact (hst' hs1.symm).elim

end PVM
