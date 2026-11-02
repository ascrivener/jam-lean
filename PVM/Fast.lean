import PVM.Machine

/-!
# A fast Ψ, proved equal to the paper's

`psi` follows GP §A.1 literally: every step deblobs the program afresh (parsing it and checking
𝔳_blob), and every block charge re-runs the gas simulation. That is fine for proofs and small
programs, but far too slow for real compiled services.

`psiFast` parses and validates the blob once, and reads block costs from a table of lazily
evaluated, memoized entries (`Thunk`), so each block is simulated at most once per run. Its
definition is otherwise the same as `psi`'s.

`psi_eq_psiFast : psi = psiFast` is registered with `@[csimp]`, which makes the compiler use
`psiFast` wherever compiled code calls `psi`. This is a proved replacement: `@[csimp]` requires
the equality theorem (unlike attributes that swap in unverified code), and the kernel and every
theorem still see the paper-literal `psi`.
-/

namespace PVM

/-- A program prepared for fast execution: 𝔳_blob checked once, block costs memoized. -/
structure Prepared where
  prog : Program
  valid : Bool
  costs : Array (Thunk Nat)

/-- Prepare a program: check 𝔳_blob once and set up a lazy cost table for every index. -/
def Program.prepare (P : Program) : Prepared :=
  { prog := P, valid := P.vBlob,
    costs := Array.ofFn (n := P.code.size) fun k => Thunk.mk fun _ => P.blockCost k.val }

namespace Prepared

/-- ϱ^Δ at `k`, from the memoized table. -/
def cost (Q : Prepared) (k : Nat) : Nat :=
  if h : k < Q.costs.size then Q.costs[k].get else Q.prog.blockCost k

theorem cost_prepare (P : Program) (k : Nat) : P.prepare.cost k = P.blockCost k := by
  unfold cost Program.prepare
  split
  · simp [Thunk.get]
  · rfl

/-- The gas stage of Ψ₁ with the memoized cost (cf. `Program.chargeGas`). -/
def chargeGas (Q : Prepared) (i : Nat) (gas : UInt64) (charged : Bool) : Status × UInt64 × Bool :=
  if charged then (.cont, gas, true)
  else
    let cost := Q.cost (Q.prog.blockStartOf i)
    if gas.toNat ≥ cost then (.cont, UInt64.ofNat (gas.toNat - cost), true) else (.oog, gas, false)

/-- Ψ₁ with the memoized cost (cf. `Program.step`). -/
def step (Q : Prepared) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) :
    StepResult :=
  let P := Q.prog
  let g := Q.chargeGas i gas charged
  let m := P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ
  let out := Program.finalState g.1 i ω μ m (memoryException μ m.reads m.writes)
  { status := out.1, pc := out.2.1, gas := g.2.1, regs := out.2.2.1, mem := out.2.2.2
    charged := !(!g.2.2 || (isTerminator (P.zeta i) && Program.Status.continuesOrHost out.1)) }

theorem step_prepare (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs)
    (μ : Memory) : P.prepare.step i gas charged ω μ = P.step i gas charged ω μ := by
  simp only [step, Program.step, chargeGas, Program.chargeGas, cost_prepare]
  rfl

/-- `runFuel` for a prepared program: deblob's checks reduce to the stored 𝔳_blob and 𝔳_inst. -/
def run (Q : Prepared) : Nat → Nat → UInt64 → Bool → Regs → Memory → Option Result
  | 0, _, _, _, _, _ => none
  | fuel + 1, i, gas, charged, ω, μ =>
    if !(Q.valid && Q.prog.vInst i) then
      some { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }
    else
      let r := Q.step i gas charged ω μ
      match r.status with
      | .cont => Q.run fuel r.pc r.gas r.charged r.regs r.mem
      | .halt | .panic =>
        some { status := r.status, pc := 0, gas := r.gas, charged := r.charged, regs := r.regs, mem := r.mem }
      | _ => some { status := r.status, pc := i, gas := r.gas, charged := r.charged, regs := ω, mem := μ }

end Prepared

@[simp] theorem prepare_prog (P : Program) : P.prepare.prog = P := rfl
@[simp] theorem prepare_valid (P : Program) : P.prepare.valid = P.vBlob := rfl

theorem deblob_of_parse {p : ByteArray} {P : Program} (h : Blob.parse? p = some P) (i : Nat) :
    deblob p i = if P.vBlob && P.vInst i then some P else none := by
  simp [deblob, h]

theorem run_prepare {p : ByteArray} {P : Program} (h : Blob.parse? p = some P) :
    ∀ n i gas ch ω μ, P.prepare.run n i gas ch ω μ = runFuel p n i gas ch ω μ := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i gas ch ω μ
    simp only [Prepared.run, runFuel, deblob_of_parse h, prepare_prog, prepare_valid,
      Prepared.step_prepare]
    by_cases hv : (P.vBlob && P.vInst i) = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hs : (P.step i gas ch ω μ).status <;> simp [ih]
    · simp only [hv, Bool.not_false, ↓reduceIte, Bool.false_eq_true]

/-- Ψ, parsing the blob once and memoizing block costs. -/
def psiFast (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) : Result :=
  match Blob.parse? p with
  | none => { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }
  | some P =>
    (P.prepare.run (stepBound p i gas charged) i gas charged ω μ).getD
      { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }

/-- **The fast Ψ is the paper's Ψ.** Registered with `@[csimp]`: compiled code that calls `psi` runs
    `psiFast`. -/
@[csimp] theorem psi_eq_psiFast : @psi = @psiFast := by
  funext p i gas ch ω μ
  unfold psi psiFast
  cases h : Blob.parse? p with
  | none => simp [stepBound, runMeasure, h, runFuel, deblob]
  | some P => simp only [run_prepare h]

end PVM
