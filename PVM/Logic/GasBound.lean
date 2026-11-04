import PVM.Logic.Det
import PVM.Logic.StepsH
import PVM.Theorems.Invocation

/-!
# Enough gas: a gas-free run is Ψ's run

`psiM_of_freeRunH` says Ψ_M returns a gas-free run's output *or ∞*. This file gives the converse
bound: if the run takes at most n steps (`FreeStepsH … n`, each ordinary step and each host call
one, each in a block costing at most M = `stepCostCap`), and every host call the contract allows
costs at most H and does what the contract says whenever that much gas is left (`HostCostLe`),
then with at least (n + 1)(M + H) gas Ψ_M returns exactly the run's output.

Each continuing step of Ψ₁ charges at most one block cost (GP §A.9: ϱ^Δ at a block's start,
nothing inside it), so with ϱ ≥ M it continues as the gas-free step does
(`step_eq_of_gas`); Ψ_H* then follows the chain step by step (`psiHStar_of_steps`), and the
halting step needs M more.
-/

namespace PVM

variable {X : Type}

/-- Every host call the contract `R` allows continues, from any gas of at least `H`, with the
    outcome `R` gives, and charges at most `H`. -/
def HostCostLe (f : HostFn X) (R : HostRel X) (H : Nat) : Prop :=
  ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → ∀ g : UInt64, H ≤ g.toNat →
    (f h g ω μ x).status = .cont ∧ (f h g ω μ x).regs = ω' ∧ (f h g ω μ x).mem = μ' ∧
      (f h g ω μ x).ctx = x' ∧ g.toNat ≤ (f h g ω μ x).gas.toNat + H

/-- With at least the block's cost left, Ψ₁ does what the gas-free step does, and charges at most
    that cost. -/
theorem step_eq_of_gas {P : Program} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs} {μ : Memory}
    {M : Nat} (hM : P.blockCost (P.blockStartOf i) ≤ M) (hg : M ≤ gas.toNat) :
    ((P.step i gas ch ω μ).status, (P.step i gas ch ω μ).pc, (P.step i gas ch ω μ).regs,
      (P.step i gas ch ω μ).mem) = P.freeStep i ω μ ∧
      gas.toNat ≤ (P.step i gas ch ω μ).gas.toNat + M := by
  have hcont : (P.chargeGas i gas ch).1 = .cont ∧
      gas.toNat ≤ (P.chargeGas i gas ch).2.1.toNat + M := by
    unfold Program.chargeGas
    cases ch
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (by omega)]
      refine ⟨rfl, ?_⟩
      have hsz : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.toNat_ofNat_of_lt' (by have := gas.toNat_lt; omega)]
      omega
    · simp
  refine ⟨?_, ?_⟩
  · simp only [Program.step, Program.freeStep, hcont.1]
  · simpa [Program.step] using hcont.2

/-- **A continuing gas-free step, with at least M gas**: Ψ from here is Ψ from the next state,
    with at most M gas less. -/
theorem psi_next_of_gas {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {i' : Nat} {ω' : Regs}
    {μ' : Memory} (hn : FreeNext p i ω μ i' ω' μ') (hc : CostOk p i)
    (gas : UInt64) (ch : Bool) (hg : stepCostCap ≤ gas.toNat) :
    ∃ gas' ch', gas.toNat ≤ gas'.toNat + stepCostCap ∧ psi p i gas ch ω μ = psi p i' gas' ch' ω' μ' := by
  obtain ⟨P, hP, hf⟩ := hn
  obtain ⟨he, hle⟩ := step_eq_of_gas (ch := ch) (ω := ω) (μ := μ) (hc P hP) hg
  rw [hf] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hs, hpc, hr, hm⟩ := he
  refine ⟨(P.step i gas ch ω μ).gas, (P.step i gas ch ω μ).charged, hle, ?_⟩
  rw [psi_eq, hP]
  dsimp only
  rw [hs]
  dsimp only
  rw [hpc, hr, hm]

/-- **A host call, with at least M gas**: Ψ stops there with h̵ × h, the state before the call,
    and at most M gas less. -/
theorem psi_host_of_gas {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {P : Program} {h : UInt64}
    {j : Nat} {ω₁ : Regs} {μ₁ : Memory} {M : Nat} (hP : deblob p i = some P)
    (hM : P.blockCost (P.blockStartOf i) ≤ M)
    (hf : P.freeStep i ω μ = (.host h, j, ω₁, μ₁)) (gas : UInt64) (ch : Bool) (hg : M ≤ gas.toNat) :
    (psi p i gas ch ω μ).status = .host h ∧ (psi p i gas ch ω μ).pc = i ∧
      (psi p i gas ch ω μ).regs = ω ∧ (psi p i gas ch ω μ).mem = μ ∧
      gas.toNat ≤ (psi p i gas ch ω μ).gas.toNat + M := by
  obtain ⟨he, hle⟩ := step_eq_of_gas (ch := ch) (ω := ω) (μ := μ) hM hg
  rw [hf] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨hs, -, -, -⟩ := he
  rw [psi_eq, hP]
  dsimp only
  rw [hs]
  exact ⟨rfl, rfl, rfl, rfl, hle⟩

/-- **The halting step, with at least M gas**: Ψ halts with the gas-free step's registers and
    memory. -/
theorem psi_halt_of_gas {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {ω' : Regs} {μ' : Memory}
    (hx : FreeExit p i ω μ .halt ω' μ') (hc : CostOk p i) (gas : UInt64) (ch : Bool)
    (hg : stepCostCap ≤ gas.toNat) :
    (psi p i gas ch ω μ).status = .halt ∧ (psi p i gas ch ω μ).regs = ω' ∧
      (psi p i gas ch ω μ).mem = μ' := by
  cases hx with
  | step hP hf hne =>
    rename_i P j ω'' μ''
    obtain ⟨he, -⟩ := step_eq_of_gas (ch := ch) (ω := ω) (μ := μ) (hc P hP) hg
    rw [hf] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨hs, -, hr, hm⟩ := he
    rw [psi_eq, hP]
    dsimp only
    rw [hs]
    simp [hr, hm]

/-- Ψ_H* depends on its start only through Ψ's result there. -/
theorem psiHStar_congr_psi {p : ByteArray} {f : HostFn X} (hf : f.GasNonIncreasing) {i i' : Nat}
    {gas gas' : UInt64} {ch ch' : Bool} {ω ω' : Regs} {μ μ' : Memory} (x : X)
    (h : psi p i gas ch ω μ = psi p i' gas' ch' ω' μ') :
    psiHStar p i gas ch ω μ f x = psiHStar p i' gas' ch' ω' μ' f x := by
  rw [psiHStar_eq p i gas ch ω μ f hf x, psiHStar_eq p i' gas' ch' ω' μ' f hf x, h]

/-- **Ψ_H* follows a chain of at most n steps** from any gas of at least n(M + H): it equals Ψ_H*
    from the chain's end, with at most n(M + H) gas less. -/
theorem psiHStar_of_steps {p : ByteArray} {f : HostFn X} (hf : f.GasNonIncreasing) {R : HostRel X}
    {H : Nat} (hH : HostCostLe f R H) {i : Nat} {ω : Regs} {μ : Memory}
    {x : X} {e : Nat} {ω₁ : Regs} {μ₁ : Memory} {x₁ : X} {n : Nat}
    (hs : FreeStepsH p R i ω μ x e ω₁ μ₁ x₁ n) :
    ∀ (gas : UInt64) (ch : Bool), n * (stepCostCap + H) ≤ gas.toNat →
      ∃ gas' ch', gas.toNat ≤ gas'.toNat + n * (stepCostCap + H) ∧
        psiHStar p i gas ch ω μ f x = psiHStar p e gas' ch' ω₁ μ₁ f x₁ := by
  induction hs with
  | refl => intro gas ch _; exact ⟨gas, ch, by omega, rfl⟩
  | pad _ ih =>
    intro gas ch hg
    obtain ⟨gas', ch', hle, heq⟩ := ih gas ch (by rw [Nat.succ_mul] at hg; omega)
    exact ⟨gas', ch', by rw [Nat.succ_mul]; omega, heq⟩
  | @next i ω μ x i' ω' μ' i'' ω'' μ'' x'' n hn hc _ ih =>
    intro gas ch hg
    rw [Nat.succ_mul] at hg
    obtain ⟨g1, c1, hle1, hpsi⟩ := psi_next_of_gas hn hc gas ch (by omega)
    obtain ⟨gas', ch', hle, heq⟩ := ih g1 c1 (by omega)
    refine ⟨gas', ch', by rw [Nat.succ_mul]; omega, ?_⟩
    rw [psiHStar_congr_psi hf x hpsi]
    exact heq
  | @host i ω μ x P h j ω₁' μ₁' ω' μ' x' i'' ω'' μ'' x'' n hP hc hfs hR _ ih =>
    intro gas ch hg
    rw [Nat.succ_mul] at hg
    obtain ⟨hst, hpc, hreg, hmem, hle1⟩ := psi_host_of_gas hP hc hfs gas ch (by omega)
    obtain ⟨ys, yr, ym, yc, yle⟩ := hH h.toNat ω μ x ω' μ' x' hR (psi p i gas ch ω μ).gas (by omega)
    obtain ⟨gas', ch', hle, heq⟩ := ih (f h.toNat (psi p i gas ch ω μ).gas ω μ x).gas
      (psi p i gas ch ω μ).charged (by omega)
    refine ⟨gas', ch', by rw [Nat.succ_mul]; omega, ?_⟩
    rw [psiHStar_eq p i gas ch ω μ f hf x]
    dsimp only
    rw [hst]
    dsimp only
    rw [hreg, hmem, ys]
    dsimp only
    rw [hpc, yr, ym, yc, blobNext_of_deblob hP]
    exact heq

/-- **Ψ_M with enough gas returns the run's output.** From Y's initial state, a chain of at most
    n steps to an index where the program halts leaving ω', μ', in a block costing at most
    `stepCostCap`: with at least (n + 1)(`stepCostCap` + H) gas,
    Ψ_M's output is the octets ω'_7 … ω'_7 + ω'_8 of μ' (or [] if they are not readable), and its
    context the chain's. -/
theorem psiM_of_stepsH (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    (f : HostFn X) (hf : f.GasNonIncreasing) (R : HostRel X) {H : Nat}
    {p : ByteArray} {ω : Regs} {μ : Memory} (hY : standardInit b a = some (p, ω, μ))
    (hH : HostCostLe f R H)
    {e : Nat} {ω₁ : Regs} {μ₁ : Memory} {x₁ : X} {n : Nat} (hs : FreeStepsH p R i ω μ x e ω₁ μ₁ x₁ n)
    {ω' : Regs} {μ' : Memory} (hx : FreeExit p e ω₁ μ₁ .halt ω' μ') (hxc : CostOk p e)
    (hg : (n + 1) * (stepCostCap + H) ≤ gas.toNat) :
    (psiM b i gas a f x).2 = (freeOutput .halt ω' μ', x₁) := by
  obtain ⟨gas', ch', hle, heq⟩ := psiHStar_of_steps hf hH hs gas false
    (by rw [Nat.succ_mul] at hg; omega)
  have hg' : stepCostCap ≤ gas'.toNat := by rw [Nat.succ_mul] at hg; omega
  obtain ⟨hst, hr, hm⟩ := psi_halt_of_gas hx hxc gas' ch' hg'
  simp only [psiM, hY, psiH]
  rw [heq, psiHStar_eq p e gas' ch' ω₁ μ₁ f hf x₁]
  dsimp only
  rw [hst]
  simp only [invocationResult, freeOutput, hr, hm]
  split <;> rfl


/-! ## The block of an index -/

/-- `blockStartOf` finds a block start at or below its argument, or 0. -/
theorem blockStartFrom_cases (P : Program) (n : Nat) :
    P.blockStartFrom n = 0 ∨ (P.isBlockStart (P.blockStartFrom n) = true ∧ P.blockStartFrom n ≤ n) := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    unfold Program.blockStartFrom
    split
    · right; exact ⟨by assumption, Nat.le_refl _⟩
    · rcases ih with h | ⟨h1, h2⟩
      · left; exact h
      · right; exact ⟨h1, by omega⟩

end PVM
