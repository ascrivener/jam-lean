import PVM.Fast
import PVM.FastMem
import PVM.FastAlu
import PVM.FastParse

/-!
# Ψ on the page-chunked memory, proved equal to the paper's

`psiFaster` runs Ψ on a prepared program (`Program.prepare`) with three changes from `psiFast`:

* RAM is a `FastMem` (the spec `Memory` with a page-chunked overlay of written octets,
  `PVM.FastMem`), so stores update a page in place instead of inserting into a tree;
* each step reads the decoded instruction, ı + 1 + skip(ı), 𝔳_inst, ζ_ı ∈ T and the block starts
  ϖ, and the block cost ϱ^Δ(𝔏(ı)), from the lazily filled per-index table of `Prepared` (each
  instruction decoded, and 𝔏 searched, once per program);
* ε^μ is checked before a store writes, so the memory is updated only when the step succeeds and
  is never shared with the pre-step state.

`fexec_eq` relates one step of the regular execution to `Program.exec` + `finalState`,
`fstep_eq` relates the step to `Program.step`, and `frun_eq` relates the run to
`Prepared.run`. They give `psiFast_eq_psiFaster : psiFast = psiFaster`, registered with
`@[csimp]`; together with `psi_eq_psiFast`, compiled code that calls `psi` runs `psiFaster`.
The kernel and every theorem still see the paper-literal `psi`.
-/

namespace PVM

open Num Exec

/-- The first `i ∈ [a, a + n)` with `¬ ok i`, if any. -/
def findBad (ok : Nat → Bool) : Nat → Nat → Option Nat
  | _, 0 => none
  | a, n + 1 => if ok a then findBad ok (a + 1) n else some a

/-- ε^μ for the least inaccessible index `m` (cf. `memoryException`). -/
@[inline] def excAt (m : Nat) : Option (Option Nat) :=
  let k := FastMem.mod32 m
  if k < 2 ^ 16 then some none else some (some (pageSize * (k / pageSize)))

/-- ε^μ of reading μ^↺_{a…+n}, without building index lists. -/
@[inline] def readExc (μ : Memory) (a n : Nat) : Option (Option Nat) :=
  match findBad (fun i => μ.readable (FastMem.mod32 i)) a n with
  | none => none
  | some m => excAt m

/-- ε^μ of writing μ^↺_{a…+n}, without building index lists. -/
@[inline] def writeExc (μ : Memory) (a n : Nat) : Option (Option Nat) :=
  match findBad (fun i => μ.writable (FastMem.mod32 i)) a n with
  | none => none
  | some m => excAt m

theorem indices_succ (a n : Nat) : indices a (n + 1) = a :: indices (a + 1) n := by
  simp only [indices, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro k _; simp only [Function.comp, Nat.succ_eq_add_one]; omega

theorem find?_indices (ok : Nat → Bool) (a n : Nat) :
    (indices a n).find? (fun i => !ok i) = findBad ok a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [indices_succ, List.find?_cons, findBad, ← ih]
    cases ok a <;> rfl

theorem min?_filter_indices (p : Nat → Bool) (a n : Nat) :
    ((indices a n).filter p).min? = (indices a n).find? p := by
  rw [List.min?_eq_head?, List.head?_filter]
  have h : (indices a n).Pairwise (· < ·) :=
    List.Pairwise.map _ (fun x y h => by omega) List.pairwise_lt_range
  exact (h.filter p).imp (fun h => Nat.min_eq_left (Nat.le_of_lt h))

theorem readExc_eq (μ : Memory) (a n : Nat) :
    memoryException μ (indices a n) [] = readExc μ a n := by
  simp only [memoryException, List.filter_nil, List.append_nil, min?_filter_indices,
    readExc, ← FastMem.mod32_eq]
  rw [find?_indices (fun i => μ.readable (FastMem.mod32 i))]
  rfl

theorem writeExc_eq (μ : Memory) (a n : Nat) :
    memoryException μ [] (indices a n) = writeExc μ a n := by
  simp only [memoryException, List.filter_nil, List.nil_append, min?_filter_indices,
    writeExc, ← FastMem.mod32_eq]
  rw [find?_indices (fun i => μ.writable (FastMem.mod32 i))]
  rfl

/-- (ε, ı', ω', μ') of one step on a `FastMem`. -/
structure FOut where
  status : Status
  pc : Nat
  regs : Regs
  mem : FastMem

namespace FOut

/-- The spec tuple of `finalState`. -/
def abs (o : FOut) : Status × Nat × Regs × Memory := (o.status, o.pc, o.regs, o.mem.toMemory)

/-- ε^μ ≠ ▸: (☇, ı, ω, μ) or (F × a, ı, ω, μ). -/
@[inline] def exc (i : Nat) (ω : Regs) (F : FastMem) : Option Nat → FOut
  | none => { status := .panic, pc := i, regs := ω, mem := F }
  | some a => { status := .fault (UInt64.ofNat a), pc := i, regs := ω, mem := F }

/-- A store of the `n`-octet encoding of `v` at `addr`, checked against ε^μ first. -/
@[inline] def store (nx i : Nat) (ω : Regs) (F : FastMem) (addr n v : Nat) : FOut :=
  match writeExc F.base addr n with
  | none => { status := .cont, pc := nx, regs := ω, mem := F.writeLE addr n v }
  | some e => exc i ω F e

/-- A load of `n` octets at `addr` into register `k`, checked against ε^μ first. -/
@[inline] def load (nx i : Nat) (ω : Regs) (F : FastMem) (k : RegIdx) (addr n : Nat)
    (f : Nat → Nat) : FOut :=
  match readExc F.base addr n with
  | none => { status := .cont, pc := nx, regs := ω.set k (UInt64.ofNat (f (F.readLE addr n))),
              mem := F }
  | some e => exc i ω F e

end FOut

namespace Prepared

/-- ı + 1 + skip(ı), from the table. -/
@[inline] def nextAt (Q : Prepared) (i : Nat) : Nat := (Q.infoAt i).next

/-- b ∈ ϖ for an integer `b`, from the table. -/
@[inline] def startAtInt (Q : Prepared) (b : Int) : Bool := if b < 0 then false else Q.startAt b.toNat

/-- sjump(b) with the tables (cf. `Program.sjump`). -/
def sjump (Q : Prepared) (i : Nat) (b : Int) : Status × Nat :=
  if Q.startAtInt b then (.cont, b.toNat) else (.panic, i)

/-- branch(b, C) with the tables (cf. `Program.branch`). -/
def branch (Q : Prepared) (i : Nat) (b : Int) (c : Bool) : Status × Nat :=
  if !Q.startAtInt b || !Q.startAt (Q.nextAt i) then (.panic, i)
  else if !c then (.cont, Q.nextAt i)
  else (.cont, b.toNat)

/-- djump(a) with the tables (cf. `Program.djump`). -/
def djump (Q : Prepared) (i : Nat) (a : Nat) : Status × Nat :=
  if a = 2 ^ 32 - 2 ^ 16 then (.halt, i)
  else if a = 0 ∨ a > Q.prog.jumpTable.size * 2 ∨ a % 2 ≠ 0 then (.panic, i)
  else
    let t := Q.prog.jumpTable.getD (a / 2 - 1) 0
    if Q.startAt t then (.cont, t) else (.panic, i)

/-- The regular execution of `ins` at ı together with ε^μ (cf. `Program.exec` and
    `Program.finalState`), on a `FastMem`. -/
def fexec (Q : Prepared) (i : Nat) (ins : Instr) (ω : Regs) (F : FastMem) : FOut :=
  let r (k : RegIdx) : Nat := (ω.get k).toNat
  let set (k : RegIdx) (v : Nat) : Regs := ω.set k (UInt64.ofNat v)
  let nx := Q.nextAt i
  match ins with
  | .noArgs .trap => { status := .panic, pc := nx, regs := ω, mem := F }
  | .noArgs .fallthrough =>
    let sp := Q.sjump i nx
    { status := sp.1, pc := sp.2, regs := ω, mem := F }
  | .noArgs .unlikely => { status := .cont, pc := nx, regs := ω, mem := F }
  | .oneImm .ecalli x => { status := .host x, pc := nx, regs := ω, mem := F }
  | .regExtImm .loadImm64 a x => { status := .cont, pc := nx, regs := set a x.toNat, mem := F }
  | .twoImm op x y => FOut.store nx i ω F x.toNat op.width (y.toNat % 2 ^ (8 * op.width))
  | .oneOffset .jump x =>
    let sp := Q.sjump i x
    { status := sp.1, pc := sp.2, regs := ω, mem := F }
  | .regImm op a x =>
    let xa := x.toNat
    match op with
    | .jumpInd =>
      let sp := Q.djump i ((r a + xa) % two32)
      { status := sp.1, pc := sp.2, regs := ω, mem := F }
    | .loadImm => { status := .cont, pc := nx, regs := set a xa, mem := F }
    | .loadU8 => FOut.load nx i ω F a xa 1 id
    | .loadI8 => FOut.load nx i ω F a xa 1 (sext 1)
    | .loadU16 => FOut.load nx i ω F a xa 2 id
    | .loadI16 => FOut.load nx i ω F a xa 2 (sext 2)
    | .loadU32 => FOut.load nx i ω F a xa 4 id
    | .loadI32 => FOut.load nx i ω F a xa 4 (sext 4)
    | .loadU64 => FOut.load nx i ω F a xa 8 id
    | .storeU8 => FOut.store nx i ω F xa 1 (r a % 2 ^ 8)
    | .storeU16 => FOut.store nx i ω F xa 2 (r a % 2 ^ 16)
    | .storeU32 => FOut.store nx i ω F xa 4 (r a % 2 ^ 32)
    | .storeU64 => FOut.store nx i ω F xa 8 (r a)
  | .regTwoImm op a x y => FOut.store nx i ω F (r a + x.toNat) op.width (y.toNat % 2 ^ (8 * op.width))
  | .regImmOffset .loadImmJump a x y =>
    let sp := Q.sjump i y
    { status := sp.1, pc := sp.2, regs := set a x.toNat, mem := F }
  | .regImmOffset op a x y =>
    let sp := Q.branch i y (regImmBranchCond op (r a) x.toNat)
    { status := sp.1, pc := sp.2, regs := ω, mem := F }
  | .twoReg op d a => { status := .cont, pc := nx, regs := set d (twoRegAlu op (r a)), mem := F }
  | .twoRegImm op a b x =>
    let addr := r b + x.toNat
    match op with
    | .storeIndU8 => FOut.store nx i ω F addr 1 (r a % 2 ^ 8)
    | .storeIndU16 => FOut.store nx i ω F addr 2 (r a % 2 ^ 16)
    | .storeIndU32 => FOut.store nx i ω F addr 4 (r a % 2 ^ 32)
    | .storeIndU64 => FOut.store nx i ω F addr 8 (r a)
    | .loadIndU8 => FOut.load nx i ω F a addr 1 id
    | .loadIndI8 => FOut.load nx i ω F a addr 1 (fun v => u64 (signed 1 v))
    | .loadIndU16 => FOut.load nx i ω F a addr 2 id
    | .loadIndI16 => FOut.load nx i ω F a addr 2 (fun v => u64 (signed 2 v))
    | .loadIndU32 => FOut.load nx i ω F a addr 4 id
    | .loadIndI32 => FOut.load nx i ω F a addr 4 (fun v => u64 (signed 4 v))
    | .loadIndU64 => FOut.load nx i ω F a addr 8 id
    | op => { status := .cont, pc := nx, regs := set a ((twoRegImmAlu op (r a) (r b) x.toNat).getD 0),
              mem := F }
  | .twoRegOffset op a b x =>
    let sp := Q.branch i x (twoRegBranchCond op (r a) (r b))
    { status := sp.1, pc := sp.2, regs := ω, mem := F }
  | .twoRegTwoImm .loadImmJumpInd a b x y =>
    let sp := Q.djump i ((r b + y.toNat) % two32)
    { status := sp.1, pc := sp.2, regs := set a x.toNat, mem := F }
  | .threeReg op a b d =>
    { status := .cont, pc := nx, regs := set d (threeRegAlu op (r a) (r b) (r d)), mem := F }

/-- Ψ₁ result on a `FastMem`. -/
structure FStep where
  status : Status
  pc : Nat
  gas : UInt64
  charged : Bool
  regs : Regs
  mem : FastMem

/-- The spec `StepResult`. -/
def FStep.abs (r : FStep) : StepResult :=
  { status := r.status, pc := r.pc, gas := r.gas, charged := r.charged, regs := r.regs,
    mem := r.mem.toMemory }

/-- Ψ₁ with the tables and a `FastMem` (cf. `Prepared.step`). -/
def fstep (Q : Prepared) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (F : FastMem) :
    FStep :=
  let inf := Q.infoAt i
  if charged then
    let o := Q.fexec i inf.instr ω F
    { status := o.status, pc := o.pc, gas, regs := o.regs, mem := o.mem,
      charged := !(inf.term && Program.Status.continuesOrHost o.status) }
  else
    let cost := Q.chargeAt i
    if gas.toNat ≥ cost then
      let o := Q.fexec i inf.instr ω F
      { status := o.status, pc := o.pc, gas := UInt64.ofNat (gas.toNat - cost), regs := o.regs,
        mem := o.mem, charged := !(inf.term && Program.Status.continuesOrHost o.status) }
    else { status := .oog, pc := i, gas, regs := ω, mem := F, charged := false }

/-- The result of Ψ on a `FastMem`. -/
structure FResult where
  status : Status
  pc : Nat
  gas : UInt64
  charged : Bool
  regs : Regs
  mem : FastMem

/-- The spec `Result`. -/
def FResult.abs (r : FResult) : Result :=
  { status := r.status, pc := r.pc, gas := r.gas, charged := r.charged, regs := r.regs,
    mem := r.mem.toMemory }

/-- `Prepared.run` with the tables and a `FastMem`. On an exit that leaves the state unchanged
    (F, ∞, h̵) it returns the step's registers and memory, which are the pre-step ones
    (`fstep_keep`), so that the memory is never shared during a step. -/
def frun (Q : Prepared) : Nat → Nat → UInt64 → Bool → Regs → FastMem → Option FResult
  | 0, _, _, _, _, _ => none
  | fuel + 1, i, gas, charged, ω, F =>
    if !(Q.valid && (Q.infoAt i).valid) then
      some { status := .panic, pc := 0, gas, charged := false, regs := ω, mem := F }
    else
      let r := Q.fstep i gas charged ω F
      match r.status with
      | .cont => Q.frun fuel r.pc r.gas r.charged r.regs r.mem
      | .halt | .panic =>
        some { status := r.status, pc := 0, gas := r.gas, charged := false, regs := r.regs, mem := r.mem }
      | _ => some { status := r.status, pc := i, gas := r.gas, charged := r.charged, regs := r.regs,
                    mem := r.mem }

/-! ### Proofs -/

theorem nextAt_prepare (P : Program) (i : Nat) : P.prepare.nextAt i = P.next i := by
  simp [nextAt, infoAt_prepare, Program.info]

theorem sjump_prepare (P : Program) (i : Nat) (b : Int) : P.prepare.sjump i b = P.sjump i b := by
  simp [sjump, Program.sjump, startAtInt, Program.isBlockStartInt, startAt_prepare]

theorem branch_prepare (P : Program) (i : Nat) (b : Int) (c : Bool) :
    P.prepare.branch i b c = P.branch i b c := by
  simp [branch, Program.branch, startAtInt, Program.isBlockStartInt, startAt_prepare, nextAt_prepare]

theorem djump_prepare (P : Program) (i a : Nat) : P.prepare.djump i a = P.djump i a := by
  simp [djump, Program.djump, startAt_prepare]

theorem memoryException_toMemory (F : FastMem) (r w : List Nat) :
    memoryException F.toMemory r w = memoryException F.base r w :=
  memoryException_pages (FastMem.toMemory_pages F) r w

theorem store_eq (P : Program) (i : Nat) (ω : Regs) (F : FastMem) (addr n v : Nat) :
    (FOut.store (P.next i) i ω F addr n v).abs =
      Program.finalState .cont i ω F.toMemory
        { status := .cont, pc := P.next i, regs := ω, mem := F.toMemory.writeN addr (encodeLE n v),
          writes := indices addr n }
        (memoryException F.toMemory [] (indices addr n)) := by
  rw [memoryException_toMemory, writeExc_eq]
  simp only [FOut.store]
  split
  · rename_i h; simp [h, FOut.abs, Program.finalState, FastMem.writeLE_eq, FastMem.toMemory_writeN]
  · rename_i e h
    rw [h]; cases e <;> simp [FOut.exc, FOut.abs, Program.finalState]

theorem load_eq (P : Program) (i : Nat) (ω : Regs) (F : FastMem) (k : RegIdx) (addr n : Nat)
    (f : Nat → Nat) :
    (FOut.load (P.next i) i ω F k addr n f).abs =
      Program.finalState .cont i ω F.toMemory
        { status := .cont, pc := P.next i,
          regs := ω.set k (UInt64.ofNat (f (decodeLE (F.toMemory.readN addr n)))),
          mem := F.toMemory, reads := indices addr n }
        (memoryException F.toMemory (indices addr n) []) := by
  rw [memoryException_toMemory, readExc_eq]
  simp only [FOut.load]
  split
  · rename_i h; simp [h, FOut.abs, Program.finalState, FastMem.readLE_eq, FastMem.readN_eq]
  · rename_i e h
    rw [h]; cases e <;> simp [FOut.exc, FOut.abs, Program.finalState]

/-- **One step of the regular execution, with ε^μ, is the spec's.** -/
theorem fexec_eq (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (F : FastMem) :
    (P.prepare.fexec i ins ω F).abs =
      let m := P.exec i ins ω F.toMemory
      Program.finalState .cont i ω F.toMemory m (memoryException F.toMemory m.reads m.writes) := by
  have hnx := nextAt_prepare P i
  cases ins with
  | noArgs op =>
    cases op <;> simp [fexec, Program.exec, hnx, sjump_prepare, FOut.abs, Program.finalState,
      memoryException]
  | oneImm op x =>
    cases op; simp [fexec, Program.exec, hnx, FOut.abs, Program.finalState, memoryException]
  | regExtImm op a x =>
    cases op; simp [fexec, Program.exec, hnx, FOut.abs, Program.finalState, memoryException]
  | twoImm op x y => simp only [fexec, Program.exec, hnx]; exact store_eq ..
  | oneOffset op x =>
    cases op; simp [fexec, Program.exec, sjump_prepare, FOut.abs, Program.finalState, memoryException]
  | regImm op a x =>
    cases op
    all_goals first
      | (simp only [fexec, Program.exec, hnx]; exact store_eq ..)
      | (simp only [fexec, Program.exec, hnx]; exact load_eq ..)
      | simp [fexec, Program.exec, hnx, djump_prepare, FOut.abs, Program.finalState, memoryException]
  | regTwoImm op a x y => simp only [fexec, Program.exec, hnx]; exact store_eq ..
  | regImmOffset op a x y =>
    cases op <;> simp [fexec, Program.exec, sjump_prepare, branch_prepare, FOut.abs,
      Program.finalState, memoryException]
  | twoReg op d a => simp [fexec, Program.exec, hnx, FOut.abs, Program.finalState, memoryException]
  | twoRegImm op a b x =>
    cases op
    all_goals first
      | (simp only [fexec, Program.exec, hnx]; exact store_eq ..)
      | (simp only [fexec, Program.exec, hnx]; exact load_eq ..)
      | simp [fexec, Program.exec, hnx, FOut.abs, Program.finalState, memoryException]
  | twoRegOffset op a b x =>
    simp [fexec, Program.exec, branch_prepare, FOut.abs, Program.finalState, memoryException]
  | twoRegTwoImm op a b x y =>
    cases op; simp [fexec, Program.exec, djump_prepare, FOut.abs, Program.finalState, memoryException]
  | threeReg op a b d => simp [fexec, Program.exec, hnx, FOut.abs, Program.finalState, memoryException]

/-- **Ψ₁ with the tables and a `FastMem` is the spec's Ψ₁.** -/
theorem fstep_eq (P : Program) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (F : FastMem) :
    (P.prepare.fstep i gas ch ω F).abs = P.step i gas ch ω F.toMemory := by
  have hfe := fexec_eq P i ((P.decode i).getD (.noArgs .trap)) ω F
  simp only [fstep, Program.step, Program.chargeGas, infoAt_prepare, chargeAt_prepare, Program.info]
  generalize P.exec i ((P.decode i).getD (.noArgs .trap)) ω F.toMemory = m at hfe ⊢
  generalize P.prepare.fexec i ((P.decode i).getD (.noArgs .trap)) ω F = o at hfe ⊢
  cases ch
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hg : gas.toNat ≥ P.blockCost (P.blockStartOf i)
    · simp only [hg, ↓reduceIte]; rw [← hfe]; simp [FStep.abs, FOut.abs]
    · simp [hg, FStep.abs, Program.finalState]
  · simp only [↓reduceIte]; rw [← hfe]; simp [FStep.abs, FOut.abs]

theorem store_keep (nx i : Nat) (ω : Regs) (F : FastMem) (addr n v : Nat)
    (h : (FOut.store nx i ω F addr n v).status ≠ .cont) :
    (FOut.store nx i ω F addr n v).regs = ω ∧ (FOut.store nx i ω F addr n v).mem = F := by
  unfold FOut.store at h ⊢
  cases hme : writeExc F.base addr n with
  | none => simp [hme] at h
  | some e => cases e <;> simp [FOut.exc]

theorem load_keep (nx i : Nat) (ω : Regs) (F : FastMem) (k : RegIdx) (addr n : Nat) (f : Nat → Nat)
    (h : (FOut.load nx i ω F k addr n f).status ≠ .cont) :
    (FOut.load nx i ω F k addr n f).regs = ω ∧ (FOut.load nx i ω F k addr n f).mem = F := by
  unfold FOut.load at h ⊢
  cases hme : readExc F.base addr n with
  | none => simp [hme] at h
  | some e => cases e <;> simp [FOut.exc]

theorem sjump_status (Q : Prepared) (i : Nat) (b : Int) :
    (Q.sjump i b).1 = .cont ∨ (Q.sjump i b).1 = .halt ∨ (Q.sjump i b).1 = .panic := by
  unfold sjump; split <;> simp

theorem branch_status (Q : Prepared) (i : Nat) (b : Int) (c : Bool) :
    (Q.branch i b c).1 = .cont ∨ (Q.branch i b c).1 = .halt ∨ (Q.branch i b c).1 = .panic := by
  unfold branch; repeat' split
  all_goals simp

theorem djump_status (Q : Prepared) (i a : Nat) :
    (Q.djump i a).1 = .cont ∨ (Q.djump i a).1 = .halt ∨ (Q.djump i a).1 = .panic := by
  unfold djump; dsimp only; repeat' split
  all_goals simp

theorem not_ctl {s : Status} (h1 : s = .cont ∨ s = .halt ∨ s = .panic)
    (h2 : s ≠ .cont ∧ s ≠ .halt ∧ s ≠ .panic) : False := by
  rcases h1 with h1 | h1 | h1 <;> simp_all

/-- An exit other than ▸, ∎ and ☇ (that is F, ∞ or h̵) leaves the registers and the memory as
    they were. -/
theorem fexec_keep (Q : Prepared) (i : Nat) (ins : Instr) (ω : Regs) (F : FastMem)
    (h : (Q.fexec i ins ω F).status ≠ .cont ∧ (Q.fexec i ins ω F).status ≠ .halt ∧
      (Q.fexec i ins ω F).status ≠ .panic) :
    (Q.fexec i ins ω F).regs = ω ∧ (Q.fexec i ins ω F).mem = F := by
  cases ins with
  | noArgs op =>
    cases op
    · simp [fexec] at h
    · simp only [fexec] at h; exact absurd h (not_ctl (sjump_status ..))
    · simp [fexec] at h
  | oneImm op x => cases op; simp [fexec]
  | regExtImm op a x => cases op; simp [fexec] at h
  | twoImm op x y => exact store_keep _ _ _ _ _ _ _ h.1
  | oneOffset op x => cases op; simp only [fexec] at h; exact absurd h (not_ctl (sjump_status ..))
  | regImm op a x =>
    cases op
    all_goals first
      | exact store_keep _ _ _ _ _ _ _ h.1
      | exact load_keep _ _ _ _ _ _ _ _ h.1
      | (simp only [fexec] at h; exact absurd h (not_ctl (djump_status ..)))
      | simp [fexec] at h
  | regTwoImm op a x y => exact store_keep _ _ _ _ _ _ _ h.1
  | regImmOffset op a x y =>
    cases op
    all_goals first
      | (simp only [fexec] at h; exact absurd h (not_ctl (sjump_status ..)))
      | (simp only [fexec] at h; exact absurd h (not_ctl (branch_status ..)))
  | twoReg op d a => simp [fexec] at h
  | twoRegImm op a b x =>
    cases op <;> simp only [fexec] at h ⊢
    all_goals first
      | exact store_keep _ _ _ _ _ _ _ h.1
      | exact load_keep _ _ _ _ _ _ _ _ h.1
      | simp at h
  | twoRegOffset op a b x => simp only [fexec] at h; exact absurd h (not_ctl (branch_status ..))
  | twoRegTwoImm op a b x y =>
    cases op; simp only [fexec] at h; exact absurd h (not_ctl (djump_status ..))
  | threeReg op a b d => simp [fexec] at h

theorem fstep_keep (Q : Prepared) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (F : FastMem)
    (h : (Q.fstep i gas ch ω F).status ≠ .cont ∧ (Q.fstep i gas ch ω F).status ≠ .halt ∧
      (Q.fstep i gas ch ω F).status ≠ .panic) :
    (Q.fstep i gas ch ω F).regs = ω ∧ (Q.fstep i gas ch ω F).mem = F := by
  unfold fstep at h ⊢
  cases ch
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hg : (Q.chargeAt i ≤ gas.toNat)
    · simp only [ge_iff_le, hg, ↓reduceIte] at h ⊢
      exact fexec_keep Q i _ ω F h
    · simp [hg]
  · simp only [↓reduceIte] at h ⊢
    exact fexec_keep Q i _ ω F h

/-- **The run with the tables and a `FastMem` is `Prepared.run`.** -/
theorem frun_eq (P : Program) :
    ∀ n i gas ch ω F, (P.prepare.frun n i gas ch ω F).map FResult.abs =
      P.prepare.run n i gas ch ω F.toMemory := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i gas ch ω F
    have hv : (P.prepare.infoAt i).valid = P.vInst i := by
      simp [infoAt_prepare, Program.info]
    have hs := fstep_eq P i gas ch ω F
    have hk := fstep_keep P.prepare i gas ch ω F
    simp only [frun, run, hv, prepare_prog, prepare_valid, step_prepare]
    by_cases hc : (!(P.vBlob && P.vInst i)) = true
    · simp [hc, FResult.abs]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [← hs]
      generalize P.prepare.fstep i gas ch ω F = r at hk
      simp only [FStep.abs]
      cases hst : r.status with
      | cont => simp [ih]
      | halt => simp [FResult.abs]
      | panic => simp [FResult.abs]
      | oog =>
        obtain ⟨h1, h2⟩ := hk (by simp [hst])
        simp [FResult.abs, h1, h2]
      | fault a =>
        obtain ⟨h1, h2⟩ := hk (by simp [hst])
        simp [FResult.abs, h1, h2]
      | host a =>
        obtain ⟨h1, h2⟩ := hk (by simp [hst])
        simp [FResult.abs, h1, h2]

end Prepared

/-- Ψ with the tables and a `FastMem` (cf. `psiFast`). -/
def psiFaster (p : ByteArray) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) :
    Result :=
  match Blob.parse? p with
  | none => { status := .panic, pc := 0, gas, charged := false, regs := ω, mem := μ }
  | some P =>
    match P.prepare.frun (stepBound p i gas charged) i gas charged ω (FastMem.ofMemory μ) with
    | some r => r.abs
    | none => { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }

/-- **The page-chunked Ψ is `psiFast`, hence the paper's Ψ.** Registered with `@[csimp]`:
    compiled code that calls `psi` (via `psi_eq_psiFast`) or `psiFast` runs `psiFaster`. -/
@[csimp] theorem psiFast_eq_psiFaster : @psiFast = @psiFaster := by
  funext p i gas ch ω μ
  unfold psiFast psiFaster
  cases Blob.parse? p with
  | none => rfl
  | some P =>
    simp only
    have := Prepared.frun_eq P (stepBound p i gas ch) i gas ch ω (FastMem.ofMemory μ)
    rw [FastMem.toMemory_ofMemory] at this
    rw [← this]
    cases P.prepare.frun (stepBound p i gas ch) i gas ch ω (FastMem.ofMemory μ) <;> rfl

end PVM
