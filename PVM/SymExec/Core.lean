import PVM.Logic.StepsH
import PVM.Logic.Words

/-!
# A reflective symbolic executor for PVM code (spike)

EXPERIMENTAL (see `docs/symexec-spike.md`). One function, `srun`, runs a stretch of PVM code over a
*symbolic* state: registers hold symbolic values (`SVal`, terms over named naturals, the start
registers and the start memory), memory is a list of cells `μ.readN a n = ℰ_n(v)` at concrete
addresses, a list of dirty ranges (everything else reads as at the start), and the start memory's
readable and writable ranges. `srun_sound` proves once that what `srun` computes is what the
gas-free machine does (GP v0.8.0 §A.4–A.5, `Program.freeStep`, chained as `FreeStepsH`), so a
stretch is proved by evaluating `check … = true` in the kernel (`decide +kernel`), with no
per-step proof terms.

Supported: the ALU instructions of §A.5.9, §A.5.10 and §A.5.13 (through the paper's own mutation
functions, so no per-operation proof), loads and stores at register-relative addresses whose base
is concrete (§A.5.10), stores of immediates (§A.5.7), `load_imm`/`load_imm_64`, `jump`,
`load_imm_jump`, `fallthrough`, `unlikely`, and branches (§A.5.8, §A.5.11) whose condition
evaluates to a constant. Anything else (host calls, `jump_ind`, symbolic addresses, symbolic branch
conditions) makes `srun` fail, so `check` is `false` and nothing is proved.
-/

namespace PVM.SymExec

open Num Exec

/-! ## Symbolic values -/

/-- A symbolic natural number. -/
inductive SVal where
  /-- A literal. -/
  | const (n : Nat)
  /-- The `k`-th named natural of the environment. -/
  | var (k : Nat)
  /-- The start value of register `r`, as a natural. -/
  | reg0 (r : Nat)
  /-- ℰ⁻¹ of the `n` start octets at `a`. -/
  | mem0 (a n : Nat)
  /-- v mod m. -/
  | mod (v : SVal) (m : Nat)
  /-- §A.5.10's ALU function of ω_A, ω_B and ν_X. -/
  | alu2i (op : TwoRegImmOp) (a b : SVal) (x : Nat)
  /-- §A.5.13's function of ω_A, ω_B and ω_D. -/
  | alu3 (op : ThreeRegOp) (a b d : SVal)
  /-- §A.5.9's function of ω_A. -/
  | alu2 (op : TwoRegOp) (a : SVal)
  /-- 𝒵⁻¹_8(𝒵_k(v)) (a signed load of `k` octets). -/
  | sx (k : Nat) (v : SVal)
  deriving DecidableEq, Repr

def SVal.isConst : SVal → Bool
  | .const _ => true
  | _ => false

/-- What symbolic values denote: named naturals, and the start registers and memory. -/
structure Env where
  ρ : Nat → Nat
  ω : Regs
  μ : Memory

def SVal.eval (E : Env) : SVal → Nat
  | .const n => n
  | .var k => E.ρ k
  | .reg0 r => (E.ω.get (regIdx r)).toNat
  | .mem0 a n => decodeLE (E.μ.readN a n)
  | .mod v m => v.eval E % m
  | .alu2i op a b x => (twoRegImmAlu op (a.eval E) (b.eval E) x).getD 0
  | .alu3 op a b d => threeRegAlu op (a.eval E) (b.eval E) (d.eval E)
  | .alu2 op a => twoRegAlu op (a.eval E)
  | .sx k v => u64 (signed k (v.eval E))

/-- An exclusive upper bound of a value, given bounds of the named naturals. -/
def SVal.bnd (B : List Nat) : SVal → Option Nat
  | .const n => some (n + 1)
  | .var k => B[k]?
  | .reg0 _ => some two64
  | .mem0 _ n => some (256 ^ n)
  | .mod _ m => if 0 < m then some m else none
  | _ => none

/-- `v mod m`, simplified: folded on a literal, dropped when a bound shows it does nothing. -/
def mkMod (B : List Nat) (v : SVal) (m : Nat) : SVal :=
  match v with
  | .const n => .const (n % m)
  | v => match v.bnd B with
    | some b => if b ≤ m then v else .mod v m
    | none => .mod v m

/-- Whether §A.5.10's function reads ω_A (only `cmov_iz_imm`, `cmov_nz_imm`). -/
def usesA : TwoRegImmOp → Bool
  | .cmovIzImm | .cmovNzImm => true
  | _ => false

/-- Whether §A.5.13's function reads ω_D (only `cmov_iz`, `cmov_nz`). -/
def usesD : ThreeRegOp → Bool
  | .cmovIz | .cmovNz => true
  | _ => false

def foldAlu2i (op : TwoRegImmOp) (a b : SVal) (x : Nat) : SVal :=
  match a, b with
  | .const p, .const q => .const ((twoRegImmAlu op p q x).getD 0)
  | a, b => .alu2i op a b x

def mkAlu2i (op : TwoRegImmOp) (a b : SVal) (x : Nat) : SVal :=
  foldAlu2i op (if usesA op then a else .const 0) b x

def foldAlu3 (op : ThreeRegOp) (a b d : SVal) : SVal :=
  match a, b, d with
  | .const p, .const q, .const r => .const (threeRegAlu op p q r)
  | a, b, d => .alu3 op a b d

def mkAlu3 (op : ThreeRegOp) (a b d : SVal) : SVal :=
  foldAlu3 op a b (if usesD op then d else .const 0)

def mkAlu2 (op : TwoRegOp) (a : SVal) : SVal :=
  match a with
  | .const p => .const (twoRegAlu op p)
  | a => .alu2 op a

/-- A load's value: unchanged (`k = 0`) or sign-extended from `k` octets. -/
def mkSx (B : List Nat) (k : Nat) (v : SVal) : SVal :=
  if k = 0 then v else
  match v with
  | .const p => .const (u64 (signed k p))
  | v => match v.bnd B with
    | some b => if b ≤ 2 ^ (8 * k - 1) ∧ k ≤ 8 then v else .sx k v
    | none => .sx k v

/-! ## Symbolic states -/

/-- What the stretch may assume of its start state and keeps throughout: bounds of the named
    naturals, and readable and writable ranges `[lo, hi)` of the start memory. -/
structure Static where
  bounds : List Nat
  rd : List (Nat × Nat)
  wr : List (Nat × Nat)

/-- A symbolic state: the 13 registers, memory cells `(a, n, v)` (μ.readN a n = ℰ_n(v)), and the
    ranges written since the start. -/
structure SState where
  regs : List SVal
  cells : List (Nat × Nat × SVal)
  dirty : List (Nat × Nat)

/-- No range of `D` meets `[a, a + n)`. -/
def clear (D : List (Nat × Nat)) (a n : Nat) : Bool := D.all fun d => a + n ≤ d.1 || d.2 ≤ a

/-- `[a, a + n)` lies in one range of `L`. -/
def inR (L : List (Nat × Nat)) (a n : Nat) : Bool := L.any fun r => r.1 ≤ a && a + n ≤ r.2

/-- What `st` asserts of an environment. -/
def Pre (E : Env) (st : Static) : Prop :=
  (∀ k b, st.bounds[k]? = some b → E.ρ k < b) ∧
  (∀ r ∈ st.rd, ∀ a, r.1 ≤ a → a < r.2 → E.μ.readable a = true) ∧
  (∀ r ∈ st.wr, ∀ a, r.1 ≤ a → a < r.2 → E.μ.writable a = true)

/-- A machine state (ω, μ) is described by σ. -/
def Inv (E : Env) (σ : SState) (ω : Regs) (μ : Memory) : Prop :=
  σ.regs.length = 13 ∧
  (∀ r : Fin 13, ω.get r = UInt64.ofNat ((σ.regs.getD r.val (.const 0)).eval E)) ∧
  (∀ c ∈ σ.cells, c.1 + c.2.1 ≤ two32 ∧ μ.readN c.1 c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) ∧
  (∀ a, a < two32 → clear σ.dirty a 1 = true → μ.read a = E.μ.read a) ∧
  μ.pages = E.μ.pages

/-! ## Code -/

/-- An instruction fact: at `pc`, `ins`, and ı + 1 + skip(ı) = `next`. -/
structure CEntry where
  pc : Nat
  ins : Instr
  next : Nat

/-- The decode facts of a list of entries (each a `d_i` of the code facts). -/
def AllCode (p : ByteArray) (P : Program) : List CEntry → Prop
  | [] => True
  | e :: es => (deblob p e.pc = some P ∧ P.decode e.pc = some e.ins ∧ P.next e.pc = e.next ∧
      P.blockCost (P.blockStartOf e.pc) ≤ stepCostCap) ∧ AllCode p P es

/-- The block-start facts of a list (each a `bs_i` of the code facts). -/
def AllBS (P : Program) : List (Nat × Bool) → Prop
  | [] => True
  | b :: bs => P.isBlockStart b.1 = b.2 ∧ AllBS P bs

/-- Instruction facts as a search tree on pc. -/
inductive CTree where
  | leaf
  | node (l : CTree) (e : CEntry) (r : CTree)

def CTree.find : CTree → Nat → Option CEntry
  | .leaf, _ => none
  | .node l e r, pc => if pc < e.pc then l.find pc else if pc = e.pc then some e else r.find pc

/-- The decode facts of a tree of entries (each a `d_i` of the code facts). -/
def AllCodeT (p : ByteArray) (P : Program) : CTree → Prop
  | .leaf => True
  | .node l e r => (deblob p e.pc = some P ∧ P.decode e.pc = some e.ins ∧ P.next e.pc = e.next ∧
      P.blockCost (P.blockStartOf e.pc) ≤ stepCostCap) ∧ AllCodeT p P l ∧ AllCodeT p P r

/-- The jump-table entries of a list (each a `jte_k`): **j**_k = t. -/
def AllJT (P : Program) : List (Nat × Nat) → Prop
  | [] => True
  | j :: js => P.jumpTable.getD j.1 0 = j.2 ∧ AllJT P js

/-- The code a stretch runs through: instruction facts, block starts, jump-table entries and |**j**|. -/
structure Prog where
  code : CTree
  bs : List (Nat × Bool)
  jt : List (Nat × Nat)
  jsize : Nat

/-- The facts of a `Prog` hold of the program `p` deblobs to. -/
def ProgHyp (p : ByteArray) (P : Program) (G : Prog) : Prop :=
  AllCodeT p P G.code ∧ AllBS P G.bs ∧ AllJT P G.jt ∧ P.jumpTable.size = G.jsize

def findCode (code : List CEntry) (pc : Nat) : Option CEntry := code.find? (·.pc == pc)

def isBS (bs : List (Nat × Bool)) (n : Nat) : Bool := bs.any fun b => b.1 == n && b.2

/-! ## One step -/

/-- How §A.5.10 treats an operation: an ALU result, a store of `n` octets, or a load of `n`
    octets (sign-extended from `k` octets, or not when `k = 0`). -/
inductive TK where
  | alu
  | store (n : Nat)
  | load (n k : Nat)

def tkind : TwoRegImmOp → TK
  | .storeIndU8 => .store 1 | .storeIndU16 => .store 2 | .storeIndU32 => .store 4
  | .storeIndU64 => .store 8
  | .loadIndU8 => .load 1 0 | .loadIndI8 => .load 1 1 | .loadIndU16 => .load 2 0
  | .loadIndI16 => .load 2 2 | .loadIndU32 => .load 4 0 | .loadIndI32 => .load 4 4
  | .loadIndU64 => .load 8 0
  | _ => .alu

/-- How §A.5.6 treats a memory operation at the absolute address ν_X. -/
def rkind : RegImmOp → TK
  | .loadU8 => .load 1 0 | .loadU16 => .load 2 0 | .loadU32 => .load 4 0 | .loadU64 => .load 8 0
  | .storeU8 => .store 1 | .storeU16 => .store 2 | .storeU32 => .store 4 | .storeU64 => .store 8
  | _ => .alu

variable (st : Static)

/-- The value of register `r`, as `(ω_r).toNat`. -/
def rdv (σ : SState) (r : Nat) : SVal := mkMod st.bounds (σ.regs.getD r (.const 0)) two64

def setv (σ : SState) (r : Nat) (v : SVal) : SState := { σ with regs := σ.regs.set r v }

/-- Literal octets `[a, a + n)` assembled, left to right, from cells holding literals. -/
def assemble (cells : List (Nat × Nat × SVal)) : Nat → Nat → Nat → Option Nat
  | 0, _, n => if n = 0 then some 0 else none
  | fuel + 1, a, n =>
    if n = 0 then some 0 else
    match cells.find? (fun c => c.1 ≤ a && a < c.1 + c.2.1 && c.2.2.isConst) with
    | some (c, m, .const v) =>
      (assemble cells fuel (a + min (c + m - a) n) (n - min (c + m - a) n)).map fun r =>
        v / 256 ^ (a - c) % 256 ^ min (c + m - a) n + 256 ^ min (c + m - a) n * r
    | _ => none

/-- What survives of a literal cell that a store to `[a, a + n)` partly overwrites. -/
def frags (a n : Nat) : Nat × Nat × SVal → List (Nat × Nat × SVal)
  | (c, m, .const v) =>
    if c + m ≤ two32 && !(c + m ≤ a || a + n ≤ c) then
      (if c < a then [(c, a - c, .const v)] else []) ++
      (if a + n < c + m then [(a + n, c + m - (a + n), .const (v / 256 ^ (a + n - c)))] else [])
    else []
  | _ => []

/-- The value loaded from `[a, a + n)`: a cell recorded there, or the start memory when nothing
    has been written there since. -/
def loadVal (σ : SState) (a n : Nat) : Option SVal :=
  match σ.cells.find? (fun c => c.1 == a && c.2.1 == n) with
  | some c => some (mkMod st.bounds c.2.2 (2 ^ (8 * n)))
  | none =>
    -- from cells holding literals
    match assemble σ.cells n a n with
    | some w => some (.const (w % 256 ^ n))
    | none => if clear σ.dirty a n then some (.mem0 a n) else none

/-- Store ℰ_n(v) at `A` (an address in ℕ, read mod 2^32). -/
def sstore (σ : SState) (A n : Nat) (v : SVal) : Option SState :=
  let a := A % two32
  if a + n ≤ two32 && inR st.wr a n then
    some { regs := σ.regs
           cells := (a, n, v) :: (σ.cells.filter (fun c => c.1 + c.2.1 ≤ two32 &&
             (c.1 + c.2.1 ≤ a || a + n ≤ c.1)) ++ σ.cells.flatMap (frags a n))
           dirty := if inR σ.dirty a n then σ.dirty else (a, a + n) :: σ.dirty }
  else none

/-- Load `n` octets at `A` into register `d`, sign-extended from `k` octets unless `k = 0`. -/
def sload (σ : SState) (d : Nat) (A n k : Nat) : Option SState :=
  let a := A % two32
  if a + n ≤ two32 && (inR st.rd a n || inR st.wr a n) then
    (loadVal st σ a n).map fun v => setv σ d (mkSx st.bounds k v)
  else none

/-- djump(a) when it continues (GP eq. `jumptablealignment`): the target, if the facts show it. -/
def sdjump (G : Prog) (a : Nat) : Option Nat :=
  if a = 2 ^ 32 - 2 ^ 16 ∨ a = 0 ∨ a > G.jsize * 2 ∨ a % 2 ≠ 0 then none else
  match G.jt.lookup (a / 2 - 1) with
  | some t => if isBS G.bs t then some t else none
  | none => none

/-- One step from `pc`: the next pc and state, or `none` if the executor cannot follow it. -/
def sstep (G : Prog) (pc : Nat) (σ : SState) :
    Option (Nat × SState) :=
  match G.code.find pc with
  | none => none
  | some e =>
    match e.ins with
    | .noArgs .unlikely => some (e.next, σ)
    | .noArgs .fallthrough => if isBS G.bs e.next then some (e.next, σ) else none
    | .oneOffset .jump x =>
      if 0 ≤ x && isBS G.bs x.toNat then some (x.toNat, σ) else none
    | .regImm .loadImm a x => some (e.next, setv σ a.val (.const x.toNat))
    | .regImm .jumpInd a x =>
      match rdv st σ a.val with
      | .const v => (sdjump G ((v + x.toNat) % two32)).map (·, σ)
      | _ => none
    | .regImm op a x =>
      match rkind op with
      | .store n =>
        (sstore st σ x.toNat n (mkMod st.bounds (rdv st σ a.val) (2 ^ (8 * n)))).map (e.next, ·)
      | .load n _ => (sload st σ a.val x.toNat n 0).map (e.next, ·)
      | .alu => none
    | .regExtImm .loadImm64 a x => some (e.next, setv σ a.val (.const x.toNat))
    | .twoReg op d a => some (e.next, setv σ d.val (mkAlu2 op (rdv st σ a.val)))
    | .threeReg op a b d =>
      some (e.next, setv σ d.val (mkAlu3 op (rdv st σ a.val) (rdv st σ b.val) (rdv st σ d.val)))
    | .twoRegImm op a b x =>
      match tkind op with
      | .alu => some (e.next, setv σ a.val (mkAlu2i op (rdv st σ a.val) (rdv st σ b.val) x.toNat))
      | .store n =>
        match rdv st σ b.val with
        | .const base =>
          (sstore st σ (base + x.toNat) n (mkMod st.bounds (rdv st σ a.val) (2 ^ (8 * n)))).map
            (e.next, ·)
        | _ => none
      | .load n k =>
        match rdv st σ b.val with
        | .const base => (sload st σ a.val (base + x.toNat) n k).map (e.next, ·)
        | _ => none
    | .regTwoImm op a x y =>
      match rdv st σ a.val with
      | .const base =>
        (sstore st σ (base + x.toNat) op.width (.const (y.toNat % 2 ^ (8 * op.width)))).map
          (e.next, ·)
      | _ => none
    | .regImmOffset op a x y =>
      if op = .loadImmJump then
        if 0 ≤ y && isBS G.bs y.toNat then some (y.toNat, setv σ a.val (.const x.toNat)) else none
      else
        match rdv st σ a.val with
        | .const v =>
          if 0 ≤ y && isBS G.bs y.toNat && isBS G.bs e.next then
            some (if regImmBranchCond op v x.toNat then y.toNat else e.next, σ)
          else none
        | _ => none
    | .twoRegTwoImm .loadImmJumpInd a b x y =>
      match rdv st σ b.val with
      | .const v => (sdjump G ((v + y.toNat) % two32)).map (·, setv σ a.val (.const x.toNat))
      | _ => none
    | .twoRegOffset op a b x =>
      match rdv st σ a.val, rdv st σ b.val with
      | .const va, .const vb =>
        if 0 ≤ x && isBS G.bs x.toNat && isBS G.bs e.next then
          some (if twoRegBranchCond op va vb then x.toNat else e.next, σ)
        else none
      | _, _ => none
    | _ => none

/-- Run exactly `k` steps from `pc`, which must end at `target`: the final state. -/
def srun (G : Prog) (target : Nat) : Nat → Nat → SState → Option SState
  | 0, pc, σ => if pc = target then some σ else none
  | k + 1, pc, σ =>
    match sstep st G pc σ with
    | some (pc', σ') => srun G target k pc' σ'
    | none => none

end PVM.SymExec
