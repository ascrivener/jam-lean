import Services.Witness.Halt
import JAM.Theorems.RefineContract
import JAM.Theorems.HostGas

/-!
# From a gas-free run of witness's refine to Ψ_M

A gas-free run from Y's state to the halting step at 43609, with ω₇ and ω₈ naming the output and
its octets readable, determines Ψ_M: ∞, or exactly that output.
-/

namespace Services.Witness

open PVM JAM Services.Witness.Code

/-- A range whose octets are all readable passes Ψ_M's page-by-page check. -/
theorem rangeReadable_of {μ : Memory} {a n : Nat} (h : ∀ j, a ≤ j → j < a + n → μ.readable j = true)
    (hb : a + n ≤ 2 ^ 32) : μ.rangeReadable a n = true := by
  unfold Memory.rangeReadable
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n == 0) = false := by simp [hn]
  rw [hn', Bool.false_or, Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simp [hb], fun k hk => ?_⟩
  simp only [List.mem_range] at hk
  have hpg : pageSize = 4096 := rfl
  have hk' : (a / pageSize + k) * pageSize ≤ a + n - 1 := by
    rw [hpg] at hk ⊢
    have := Nat.div_mul_le_self (a + n - 1) 4096
    have : a / 4096 + k ≤ (a + n - 1) / 4096 := by omega
    calc (a / 4096 + k) * 4096 ≤ (a + n - 1) / 4096 * 4096 := Nat.mul_le_mul_right _ this
      _ ≤ a + n - 1 := by omega
  let j := max a ((a / pageSize + k) * pageSize)
  have hj : μ.readable j = true := h j (Nat.le_max_left _ _) (by simp only [j]; omega)
  have hpage : j / pageSize = a / pageSize + k := by
    simp only [j, hpg] at hk' ⊢
    rcases Nat.le_total a ((a / 4096 + k) * 4096) with h1 | h1
    · rw [Nat.max_eq_right h1]; simp
    · rw [Nat.max_eq_left h1]
      have : k = 0 := by omega
      subst this; simp
  simp only [Memory.readable] at hj ⊢
  rw [← hpage]
  simpa [hpg, Nat.mul_div_cancel] using hj

theorem psiM_of_run {p : ByteArray} {P : Program} [HasCode p P] (code a : ByteArray) (gas : UInt64)
    (env : RefineHost.Env) {ω₀ : Regs} {μ₀ : Memory}
    (hY : standardInit code a = some (p, ω₀, μ₀)) (o : Nat) (out : List UInt8) (N : Nat)
    (hrun : ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω₀ μ₀ ((∅, []) : RefineCtx) 43609 ω' μ' x' N ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat o ∧ ω'[8] = UInt64.ofNat out.length ∧
      o + out.length < 4294967296 ∧ out.length < 18446744073709551616 ∧
      μ'.readN o out.length = out ∧ (∀ j, o ≤ j → j < o + out.length → μ'.readable j = true)) :
    (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 =
        .ok ⟨out.toArray⟩ ∨
      (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 = .oog := by
  obtain ⟨ω', μ', x', hsteps, h0, h7, h8, hb, hb', hmem, hrd⟩ := hrun
  have hexit : FreeRunH p (refineContract env) 43609 ω' μ' x' .halt ω' μ' x' :=
    .exit (FreeRun.exit (halt_43609 (P := P) ω' μ' h0)) (by simp)
  have hfull := hsteps.run hexit
  rcases psiM_of_freeRunH code 0 gas a ((∅, []) : RefineCtx) _ (refineHostFn_gasNonIncreasing env)
      (refineContract env) (refineContract_pins env) hY hfull with h | h
  · right
    cases hm : (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 <;>
      simp_all [InvOutput.isOog]
  · left
    rw [show (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 =
      (freeOutput .halt ω' μ') from congrArg Prod.fst h]
    have h7' : (ω'.get 7).toNat = o := by
      rw [show ω'.get 7 = ω'[7] from rfl, h7]; simp; omega
    have h8' : (ω'.get 8).toNat = out.length := by
      rw [show ω'.get 8 = ω'[8] from rfl, h8]; simp; omega
    have hrr : μ'.rangeReadable o out.length = true := rangeReadable_of hrd (by omega)
    simp [freeOutput, h7', h8', hrr, hmem]


/-- **With enough gas, exactly that output.** As `psiM_of_run`, for a run of at most N steps (each in
    a block costing at most `stepCostCap`), and at least (N + 1)(`stepCostCap` + `hostCostMax`) gas:
    Ψ_M's output is `out`. -/
theorem psiM_exact_of_run {p : ByteArray} {P : Program} [HasCode p P] (code a : ByteArray)
    (gas : UInt64) (env : RefineHost.Env) {ω₀ : Regs} {μ₀ : Memory}
    (hY : standardInit code a = some (p, ω₀, μ₀)) (o : Nat) (out : List UInt8) (N : Nat)
    (hg : (N + 1) * (stepCostCap + hostCostMax) ≤ gas.toNat)
    (hrun : ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω₀ μ₀ ((∅, []) : RefineCtx) 43609 ω' μ' x' N ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat o ∧ ω'[8] = UInt64.ofNat out.length ∧
      o + out.length < 4294967296 ∧ out.length < 18446744073709551616 ∧
      μ'.readN o out.length = out ∧ (∀ j, o ≤ j → j < o + out.length → μ'.readable j = true)) :
    (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 =
      .ok ⟨out.toArray⟩ := by
  obtain ⟨ω', μ', x', hsteps, h0, h7, h8, hb, hb', hmem, hrd⟩ := hrun
  have h := psiM_of_stepsH code 0 gas a ((∅, []) : RefineCtx) _ (refineHostFn_gasNonIncreasing env)
    (refineContract env) hY (refineContract_cost env) hsteps (halt_43609 (P := P) ω' μ' h0)
    (CostOk.of (d_43609 (p := p)).1 (d_43609 (p := p)).2.2.2) hg
  rw [show (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 =
    (freeOutput .halt ω' μ') from congrArg Prod.fst h]
  have h7' : (ω'.get 7).toNat = o := by
    rw [show ω'.get 7 = ω'[7] from rfl, h7]; simp; omega
  have h8' : (ω'.get 8).toNat = out.length := by
    rw [show ω'.get 8 = ω'[8] from rfl, h8]; simp; omega
  have hrr : μ'.rangeReadable o out.length = true := rangeReadable_of hrd (by omega)
  simp [freeOutput, h7', h8', hrr, hmem]

end Services.Witness
