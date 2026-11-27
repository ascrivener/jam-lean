import PVM.Machine
import PVM.FastGas

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

`Prepared` also carries a lazily filled per-index table (`info`: the decoded instruction,
ı + 1 + skip(ı), 𝔳_inst, ζ_ı ∈ T, ı ∈ ϖ and ϱ^Δ(𝔏(ı))), with `infoAt_prepare`, `startAt_prepare`
and `chargeAt_prepare` stating that it agrees with the spec definitions.
`PVM.FastStep` uses them.
-/

namespace PVM

/-- The facts about index `i` of a program that each step needs: the decoded instruction (an
    undecodable octet read as `trap`, as in `Program.step`), ı + 1 + skip(ı), 𝔳_inst, whether
    ζ_ı ∈ T, whether ı ∈ ϖ, and the cost ϱ^Δ(𝔏(ı)) of the block containing ı (itself lazy: it is
    only needed when a block is entered). -/
structure InstrInfo where
  instr : Instr
  next : Nat
  valid : Bool
  term : Bool
  start : Bool
  charge : Thunk Nat

/-- The `InstrInfo` of index `i`, computed from the spec definitions. -/
def Program.info (P : Program) (i : Nat) : InstrInfo :=
  { instr := (P.decode i).getD (.noArgs .trap), next := P.next i, valid := P.vInst i,
    term := isTerminator (P.zeta i), start := P.isBlockStart i,
    charge := Thunk.mk fun _ => P.blockCost (P.blockStartOf i) }

/-- A program prepared for fast execution: 𝔳_blob checked once, block costs memoized, and, for
    every index of **c**, a lazily evaluated `InstrInfo` (so each instruction is decoded, and the
    block containing it found, once per program). -/
structure Prepared where
  prog : Program
  valid : Bool
  /-- The block-cost table of `Prepared.step`, built on first use (the fast path of
      `PVM.FastStep` does not use it). -/
  costs : Thunk (Array (Thunk Nat))
  info : Array (Thunk InstrInfo) := #[]

/-- Prepare a program: check 𝔳_blob once and set up the lazy tables for every index. -/
def Program.prepare (P : Program) : Prepared :=
  { prog := P, valid := P.vBlob,
    costs := Thunk.mk fun _ => Array.ofFn (n := P.code.size) fun k => Thunk.mk fun _ => P.blockCost k.val,
    info := Array.ofFn (n := P.code.size) fun k => Thunk.mk fun _ => P.info k.val }

namespace Prepared

/-- ϱ^Δ at `k`, from the memoized table. -/
def cost (Q : Prepared) (k : Nat) : Nat :=
  let cs := Q.costs.get
  if h : k < cs.size then cs[k].get else Q.prog.blockCost k

theorem cost_prepare (P : Program) (k : Nat) : P.prepare.cost k = P.blockCost k := by
  unfold cost Program.prepare
  simp only [Thunk.get]
  by_cases h : k < P.code.size
  · simp [h]
  · simp [h]

/-- The `InstrInfo` of index `i`, from the table. -/
@[inline] def infoAt (Q : Prepared) (i : Nat) : InstrInfo :=
  if h : i < Q.info.size then Q.info[i].get else Q.prog.info i

/-- ı ∈ ϖ, from the table. -/
@[inline] def startAt (Q : Prepared) (n : Nat) : Bool :=
  if h : n < Q.info.size then Q.info[n].get.start else Q.prog.isBlockStart n

/-- ϱ^Δ(𝔏(ı)), from the table. -/
@[inline] def chargeAt (Q : Prepared) (i : Nat) : Nat := (Q.infoAt i).charge.get

theorem infoAt_prepare (P : Program) (i : Nat) : P.prepare.infoAt i = P.info i := by
  unfold infoAt Program.prepare
  split
  · simp [Thunk.get]
  · rfl

theorem startAt_prepare (P : Program) (n : Nat) : P.prepare.startAt n = P.isBlockStart n := by
  unfold startAt Program.prepare
  split
  · simp [Thunk.get, Program.info]
  · rfl

theorem chargeAt_prepare (P : Program) (i : Nat) :
    P.prepare.chargeAt i = P.blockCost (P.blockStartOf i) := by
  simp [chargeAt, infoAt_prepare, Program.info, Thunk.get]

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
      some { status := .panic, pc := 0, gas, charged := false, regs := ω, mem := μ }
    else
      let r := Q.step i gas charged ω μ
      match r.status with
      | .cont => Q.run fuel r.pc r.gas r.charged r.regs r.mem
      | .halt | .panic =>
        some { status := r.status, pc := 0, gas := r.gas, charged := false, regs := r.regs, mem := r.mem }
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
  | none => { status := .panic, pc := 0, gas, charged := false, regs := ω, mem := μ }
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
