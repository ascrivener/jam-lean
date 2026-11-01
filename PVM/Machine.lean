import PVM.Exec
import PVM.Gas

/-!
# Single-step Ψ₁ and the full PVM Ψ (GP v0.8.0 §A.1, §A.4)
-/

namespace PVM

/-- The result of Ψ₁ (GP §A.4): (ε*, ı*, ϱ*, ϱ̃*, ω*, μ*). -/
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

/-- The gas stage of Ψ₁ (GP §A.4): (ε^ϱ, ϱ*, ϱ̃') =
    (▸, ϱ, ⊤) if ϱ̃ = ⊤; (▸, ϱ − ϱ^Δ(**c**, **k**, 𝔏(ı)), ⊤) if ϱ ≥ ϱ^Δ(**c**, **k**, 𝔏(ı)); (∞, ϱ, ⊥) otherwise. -/
def chargeGas (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) : Status × UInt64 × Bool :=
  if charged then (.cont, gas, true)
  else
    let cost := P.blockCost (P.blockStartOf i)
    if gas.toNat ≥ cost then (.cont, UInt64.ofNat (gas.toNat - cost), true) else (.oog, gas, false)

/-- ε* ∈ {▸} ∪ {h̵} × ℕ_R, the condition under which a terminator clears the charged flag. -/
def Status.continuesOrHost : Status → Bool
  | .cont | .host _ => true
  | _ => false

/-- Ψ₁(**c**, **k**, **j**, ı, ϱ, ϱ̃, ω, μ) (GP §A.4).

    Ψ only calls Ψ₁ when 𝔳_inst(**c**, **k**, ı) holds, so ζ_ı ∈ U and the instruction decodes;
    to keep Ψ₁ total we read an undecodable octet as `trap`. -/
def step (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) :
    StepResult :=
  let (εg, gas', charged') := P.chargeGas i gas charged
  let ins := (P.decode i).getD (.noArgs .trap)
  let m := P.exec i ins ω μ
  -- (ε*, ı*, ω*, μ*): the gas exception, else ε^μ, else the regular execution.
  let (ε, i', ω', μ') : Status × Nat × Regs × Memory :=
    if εg ≠ .cont then (εg, i, ω, μ)
    else match memoryException μ m.reads m.writes with
      | some none => (.panic, i, ω, μ)
      | some (some a) => (.fault (UInt64.ofNat a), i, ω, μ)
      | none => (m.status, m.pc, m.regs, m.mem)
  -- ϱ̃* = ⊥ if ϱ̃' = ⊥ ∨ (**c**_ı ∈ T ∧ ε* ∈ {▸} ∪ {h̵} × ℕ_R), otherwise ⊤.
  let charged'' := !(!charged' || (isTerminator (P.zeta i) && Status.continuesOrHost ε))
  { status := ε, pc := i', gas := gas', charged := charged'', regs := ω', mem := μ' }

end Program

/-- The result of Ψ (GP §A.1): (ε, ı, ϱ, ϱ̃, ω, μ), plus `exitPc`, the index of the instruction
    that caused the exit. Ψ itself returns ı = 0 on ∎ and ☇; the test vectors report `exitPc`. -/
structure Result where
  /-- ε ∈ {∎, ☇, ∞} ∪ {F, h̵} × ℕ_R -/
  status : Status
  /-- ı as returned by Ψ: 0 on ∎ and ☇, otherwise the exiting instruction. -/
  pc : Nat
  /-- The opcode index of the instruction whose step ended the run. -/
  exitPc : Nat
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
      -- ⟨☇, ı, ϱ, ϱ̃, ω, μ⟩ from the `where` clause, then the ☇ case of Ψ.
      some { status := .panic, pc := 0, exitPc := i, gas, charged, regs := ω, mem := μ }
    | some P =>
      let r := P.step i gas charged ω μ
      match r.status with
      | .cont => runFuel p fuel r.pc r.gas r.charged r.regs r.mem
      | .halt | .panic =>
        some { status := r.status, pc := 0, exitPc := i, gas := r.gas, charged := r.charged,
               regs := r.regs, mem := r.mem }
      | _ =>
        some { status := r.status, pc := i, exitPc := i, gas := r.gas, charged := r.charged,
               regs := ω, mem := μ }

/-- A bound on the number of steps of Ψ from (ı, ϱ, ϱ̃): every block charge costs at least 1 gas,
    and between charges ı strictly increases within **c** (non-terminators) or a terminator
    clears ϱ̃. With n = |**c**| + 1 the measure 2n·ϱ + (if ϱ̃ then n + |**c**| − ı else 0) strictly
    decreases on every continuing step (see `PVM.Theorems.Termination`). -/
def stepBound (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) : Nat :=
  match Blob.parse? p with
  | none => 1
  | some P =>
    let n := P.code.size + 1
    2 * n * gas.toNat + (if charged then n + P.code.size - i else 0) + 1

/-- Ψ(p, ı, ϱ, ϱ̃, ω, μ) (GP §A.1). The fallback after `stepBound` steps is unreachable
    (`PVM.psi_runFuel` in `PVM.Theorems.Termination`). -/
def psi (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) : Result :=
  (runFuel p (stepBound p i gas charged) i gas charged ω μ).getD
    { status := .panic, pc := 0, exitPc := i, gas, charged, regs := ω, mem := μ }

end PVM
