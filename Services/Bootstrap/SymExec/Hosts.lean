import Services.Bootstrap.Acc.Contract
import Services.Bootstrap.SymExec.Prog

/-!
EXPERIMENTAL (symexec Phase 2, `docs/symexec-spike.md`): host calls the executor follows. A
`Prog` with `hosts := logHosts` follows `ecalli 100` (`log`, JIP-1), an id neither refine's
dispatcher (GP eq. `refinemutator`) nor accumulate's (GP eq. `accinvocation`) defines: it charges
𝖬_∅ and returns WHAT in ω₇, leaving memory and the context unchanged. `refine_logHosts` and
`acc_logHosts` prove the contracts allow it, for any cap of at least 𝖬_∅ = 1000.
-/

namespace Services.Bootstrap.SymExec

open PVM PVM.SymExec JAM Services.Bootstrap.Code

/-- `log` (id 100): ω₇ := WHAT. -/
def logHosts : NTree (List (Nat × Nat)) := .node .leaf 100 [(7, Result.WHAT)] .leaf

theorem hregs_log (ω : Regs) : hregs ω [(7, Result.WHAT)] = setR7 ω Result.WHAT := rfl

/-- Refine's contract, at any cap 𝖬_∅ ≤ cap < 2^64, allows `log`. -/
theorem refine_logHosts {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : RefineHost.Env) : HostOk (refineContractK cap env) logHosts := by
  refine ⟨fun ω μ x => ?_, trivial, trivial⟩
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hg : ¬((cap : Int) - Constants.Cgasunknown < 0) := by omega
  refine ⟨Or.inr (Or.inr (by decide)), ?_, ?_⟩ <;>
    simp [toHostFn, RefineHost.dispatch, RefineHost.unknown, hc, hg, hregs_log]

/-- Accumulate's contract, at any cap 𝖬_∅ ≤ cap < 2^64, allows `log`. -/
theorem acc_logHosts {cap : Nat} (h1 : Constants.Cgasunknown ≤ cap) (h2 : cap < 2 ^ 64)
    (env : AccEnv) : HostOk (Acc.accContractK cap env) logHosts := by
  refine ⟨fun ω μ x => ?_, trivial, trivial⟩
  have hc : (UInt64.ofNat cap).toNat = cap := by simp [Nat.mod_eq_of_lt h2]
  have hg : ¬((cap : Int) - Constants.Cgasunknown < 0) := by omega
  refine ⟨⟨by decide, by decide⟩, ?_, ?_⟩ <;>
    simp [accHostFn, AccHost.dispatch, hc, hg, hregs_log]

/-- Bootstrap's code table, following `log`. -/
def progLog : Prog := { prog with hosts := logHosts }

/-- Example: the `log` call at pc 4770 (BTail1 S49), through refine's contract. -/
theorem log4770_ok : check ⟨[], [], [], [], []⟩ progLog ⟨[], []⟩ ⟨[(7, .const Result.WHAT)], []⟩ []
    4770 4772 1 = true := by decide +kernel

theorem log4770 {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 4770 ω μ x 4772 ω' μ' x 1 ∧
      ω'[7] = UInt64.ofNat Result.WHAT := by
  obtain ⟨ω', μ', hrun, ⟨r7, -⟩, -⟩ :=
    check_sound log4770_ok (hyp (p := p) (P := P)) [] trivial trivial ω μ trivial trivial trivial
      trivial trivial x (refine_logHosts (cap := hostCostMax) (by decide) (by decide) env)
  exact ⟨ω', μ', hrun, r7⟩

end Services.Bootstrap.SymExec
