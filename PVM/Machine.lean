import PVM.Exec
import PVM.Gas

/-!
# Single-step Ψ₁ and the full PVM Ψ (GP v0.8.1 §A.1, §A.4)
-/

namespace PVM

/-- The result of $\Psi_1$ (GP §A.4, eq. (A.7)): $(\varepsilon^{\ast}, \imath^{\ast}, \varrho^{\ast}, \tilde\varrho^{\ast}, \varphi^{\ast}, \mu^{\ast})$. -/
structure StepResult where
  /-- ε* -/
  status : Status
  /-- ı* -/
  pc : Nat
  /-- ϱ* -/
  gas : UInt64
  /-- ϱ̃*, the gas-charged flag. -/
  charged : Bool
  /-- ω* -/
  regs : Regs
  /-- μ* -/
  mem : Memory

namespace Program

/-- The gas stage of $\Psi_1$ (GP §A.4, eq. (A.8)): $(\varepsilon^\varrho, \varrho^{\ast}, \tilde\varrho') =$
    $(\blacktriangleright, \varrho, \top)$ if $\tilde\varrho = \top$;
    $(\blacktriangleright, \varrho - \varrho^\Delta(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)), \top)$ if $\varrho \ge \varrho^\Delta(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath))$;
    $(\infty, \varrho, \bot)$ otherwise. -/
def chargeGas (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) : Status × UInt64 × Bool :=
  if charged then (.cont, gas, true)
  else
    let cost := P.blockCost (P.blockStartOf i)
    if gas.toNat ≥ cost then (.cont, UInt64.ofNat (gas.toNat - cost), true) else (.oog, gas, false)

/-- ε* ∈ {▸} ∪ {ħ} × ℕ_R, the condition under which a terminator clears the charged flag. -/
def Status.continuesOrHost : Status → Bool
  | .cont | .host _ => true
  | _ => false

/-- $(\varepsilon^{\ast}, \imath^{\ast}, \varphi^{\ast}, \mu^{\ast})$ (GP §A.4, eq. (A.10)): $(\varepsilon^\varrho, \imath, \varphi, \mu)$ if
    $\varepsilon^\varrho \ne \blacktriangleright$; else $(\varepsilon^\mu, \imath, \varphi, \mu)$ if $\varepsilon^\mu \ne \blacktriangleright$; else
    $(\varepsilon, \imath', \varphi', \mu')$ from the regular execution `m`. -/
def finalState (εg : Status) (i : Nat) (ω : Regs) (μ : Memory) (m : Mutation)
    (εμ : Option (Option Nat)) : Status × Nat × Regs × Memory :=
  if εg ≠ .cont then (εg, i, ω, μ)
  else match εμ with
    | some none => (.panic, i, ω, μ)
    | some (some a) => (.fault (UInt64.ofNat a), i, ω, μ)
    | none => (m.status, m.pc, m.regs, m.mem)

/-- $\Psi_1(\mathbf{c}, \mathbf{k}, \mathbf{j}, \imath, \varrho, \tilde\varrho, \varphi, \mu)$ (GP §A.4, eq. (A.7)).

    $\Psi$ only calls $\Psi_1$ when $\mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath)$ holds, so $\zeta_{\imath} \in U$ and the
    instruction decodes; to keep $\Psi_1$ total we read an undecodable octet as `trap`. That default is unreachable at every
    step Ψ takes (`PVM.Program.step_decode` in `PVM.Theorems.ExecForms`). -/
def step (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) :
    StepResult :=
  -- (ε^ϱ, ϱ*, ϱ̃')
  let g := P.chargeGas i gas charged
  -- the regular execution (ε, ı', ω', μ') with its **r** and **w**
  let m := P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ
  let out := finalState g.1 i ω μ m (memoryException μ m.reads m.writes)
  { status := out.1, pc := out.2.1, gas := g.2.1, regs := out.2.2.1, mem := out.2.2.2
    -- ϱ̃* = ⊥ if ϱ̃' = ⊥ ∨ (**c**_ı ∈ T ∧ ε* ∈ {▸} ∪ {ħ} × ℕ_R), otherwise ⊤.
    charged := !(!g.2.2 || (isTerminator (P.zeta i) && Status.continuesOrHost out.1)) }

end Program

/-- The result of Ψ (GP §A.1): (ε, ı, ϱ, ϱ̃, ω, μ). -/
structure Result where
  /-- ε ∈ {∎, ☇, ∞} ∪ {F, ħ} × ℕ_R -/
  status : Status
  /-- ı: 0 on ∎ and ☇, otherwise the instruction that caused the exit. -/
  pc : Nat
  /-- ϱ -/
  gas : UInt64
  /-- ϱ̃ -/
  charged : Bool
  /-- ω -/
  regs : Regs
  /-- μ -/
  mem : Memory

/-- Ψ with at most `fuel` steps (GP §A.1); `none` if the fuel runs out first.

    Each step deblobs the program afresh, exactly as the paper writes it. -/
def runFuel (p : ByteArray) : Nat → Nat → UInt64 → Bool → Regs → Memory → Option Result
  | 0, _, _, _, _, _ => none
  | fuel + 1, i, gas, charged, ω, μ =>
    match deblob p i with
    | none =>
      -- ⟨☇, ı, ϱ, ϱ̃, ω, μ⟩ from the `where` clause, then the ☇ case of Ψ, which clears ϱ̃
      -- (GP v0.8.1 §A.1, #588).
      some { status := .panic, pc := 0, gas, charged := false, regs := ω, mem := μ }
    | some P =>
      let r := P.step i gas charged ω μ
      match r.status with
      | .cont => runFuel p fuel r.pc r.gas r.charged r.regs r.mem
      | .halt | .panic =>
        -- ⟨ε, 0, ϱ', ⊥, ω', μ'⟩: halting or panicking clears ϱ̃ (GP v0.8.1 §A.1, #588).
        some { status := r.status, pc := 0, gas := r.gas, charged := false,
               regs := r.regs, mem := r.mem }
      | _ =>
        some { status := r.status, pc := i, gas := r.gas, charged := r.charged,
               regs := ω, mem := μ }

/-- A termination measure for Ψ from (ı, ϱ, ϱ̃): every block charge costs at least 1 gas, and
    between charges ı strictly increases within **c** (non-terminators) or a terminator clears
    ϱ̃. With n = |**c**| + 1, the measure 2n·ϱ + (if ϱ̃ then n + |**c**| − ı else 0) strictly
    decreases on every continuing step (`PVM.step_measure_lt` in `PVM.Theorems.Termination`). -/
def runMeasure (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) : Nat :=
  match Blob.parse? p with
  | none => 0
  | some P =>
    let n := P.code.size + 1
    2 * n * gas.toNat + (if charged then n + P.code.size - i else 0)

/-- The number of steps after which Ψ has certainly exited. -/
def stepBound (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) : Nat :=
  runMeasure p i gas charged + 1

/-- $\Psi(\mathfrak{p}, \imath, \varrho, \tilde\varrho, \varphi, \mu)$ (GP §A.1). The fallback after `stepBound` steps is unreachable
    (`PVM.runFuel_stepBound_isSome` in `PVM.Theorems.Termination`). -/
def psi (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) : Result :=
  (runFuel p (stepBound p i gas charged) i gas charged ω μ).getD
    { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }

end PVM
