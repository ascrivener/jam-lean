import PVM.Logic.StepsH
import PVM.Logic.Words

/-!
# A reflective symbolic executor for PVM code (spike)

EXPERIMENTAL (see `docs/symexec-spike.md`). One function, `srun`, runs a stretch of PVM code over a
*symbolic* state, and `srun_sound` (`PVM.SymExec.Sound`) proves once that what it computes is what
the gas-free machine does (GP v0.8.0 §A.4–A.5, `Program.freeStep`, chained as `FreeStepsH`). A
stretch is then proved by evaluating `check … = true` in the kernel (`decide +kernel`).

* Registers hold symbolic values (`SVal`): terms over named naturals ρ_k, the start registers and
  the start memory, with the paper's own mutation functions as nodes (so no per-operation proof).
* Addresses are affine (`Aff`): a literal, or ρ_k + d for an integer offset d. Named naturals have
  lower and upper bounds, so an address has an interval; two regions are disjoint when they share a
  base and their offsets say so, when their intervals say so, or when a declared separation (a
  hypothesis of the stretch) says so.
* Memory is a list of cells `μ_{a…+n} = ℰ_n(v)`, a list of dirty regions (everything else reads as
  at the start), and the start memory's readable and writable regions (stores keep pages).

Supported: the ALU instructions of §A.5.9, §A.5.10 and §A.5.13, loads and stores at affine addresses
(§A.5.6, §A.5.7, §A.5.10), `load_imm`/`load_imm_64`, `jump`, `load_imm_jump`, `fallthrough`,
`unlikely`, branches (§A.5.8, §A.5.11) whose condition evaluates to a literal, and `jump_ind` /
`load_imm_jump_ind` to a literal address through the jump table. Anything else makes `srun` fail,
so `check` is `false` and nothing is proved.
-/

namespace PVM.SymExec

open Num Exec

/-! ## Values and addresses -/

/-- An affine address: ρ_k + off, or the literal `off` when `base = none`. -/
structure Aff where
  base : Option Nat
  off : Int
  deriving DecidableEq, Repr

/-- A symbolic natural number. -/
inductive SVal where
  /-- A literal. -/
  | const (n : Nat)
  /-- The `k`-th named natural of the environment. -/
  | var (k : Nat)
  /-- The start value of register `r`, as a natural. -/
  | reg0 (r : Nat)
  /-- ℰ⁻¹ of the `n` start octets at an address. -/
  | mem0 (a : Aff) (n : Nat)
  /-- v mod m. -/
  | mod (v : SVal) (m : Nat)
  /-- An affine value (an address). -/
  | addr (a : Aff)
  /-- §A.5.10's ALU function of ω_A, ω_B and ν_X. -/
  | alu2i (op : TwoRegImmOp) (a b : SVal) (x : Nat)
  /-- §A.5.13's function of ω_A, ω_B and ω_D. -/
  | alu3 (op : ThreeRegOp) (a b d : SVal)
  /-- §A.5.9's function of ω_A. -/
  | alu2 (op : TwoRegOp) (a : SVal)
  /-- 𝒵⁻¹_8(𝒵_k(v)) (a signed load of `k` octets). -/
  | sx (k : Nat) (v : SVal)
  /-- Entry `i` of a table of literals (0 past its end): an octet table the code indexes. -/
  | tbl (vs : List Nat) (i : SVal)
  deriving DecidableEq, Repr

def SVal.isConst : SVal → Bool
  | .const _ => true
  | _ => false

/-- What symbolic values denote: named naturals, and the start registers and memory. -/
structure Env where
  ρ : Nat → Nat
  ω : Regs
  μ : Memory

def Aff.eval (E : Env) (a : Aff) : Int :=
  (match a.base with | some k => (E.ρ k : Int) | none => 0) + a.off

def SVal.eval (E : Env) : SVal → Nat
  | .const n => n
  | .var k => E.ρ k
  | .reg0 r => (E.ω.get (regIdx r)).toNat
  | .mem0 a n => decodeLE (E.μ.readN (a.eval E).toNat n)
  | .mod v m => v.eval E % m
  | .addr a => (a.eval E).toNat
  | .alu2i op a b x => (twoRegImmAlu op (a.eval E) (b.eval E) x).getD 0
  | .alu3 op a b d => threeRegAlu op (a.eval E) (b.eval E) (d.eval E)
  | .alu2 op a => twoRegAlu op (a.eval E)
  | .sx k v => u64 (signed k (v.eval E))
  | .tbl vs i => vs.getD (i.eval E) 0

/-- `t` lies in the region of `n` octets at `a`. -/
def InReg (E : Env) (r : Aff × Nat) (t : Nat) : Prop := r.1.eval E ≤ t ∧ (t : Int) < r.1.eval E + r.2

/-! ## What a stretch assumes and keeps -/

/-- Bounds of the named naturals (`lb[k] ≤ ρ_k < ub[k]`), readable and writable regions of the
    start memory, and declared pairs of disjoint regions. -/
structure Static where
  ub : List Nat
  lb : List Nat
  rd : List (Aff × Nat)
  wr : List (Aff × Nat)
  sep : List ((Aff × Nat) × (Aff × Nat))

/-- The least value an address can have. -/
def Aff.lo (st : Static) (a : Aff) : Int :=
  (match a.base with | some k => ((st.lb[k]?.getD 0 : Nat) : Int) | none => 0) + a.off

/-- The greatest value an address can have, if the bounds give one. -/
def Aff.hi (st : Static) (a : Aff) : Option Int :=
  match a.base with
  | some k => st.ub[k]?.map fun u => (u : Int) - 1 + a.off
  | none => some a.off

/-- `n` octets at `a` lie within ℕ_{2^32}. -/
def valid (st : Static) (a : Aff) (n : Nat) : Bool :=
  decide (0 ≤ a.lo st) && match a.hi st with
    | some h => decide (h + n ≤ two32) && decide (h < two32)
    | none => false

/-- The region `(a, n)` lies within `r`. -/
def within (st : Static) (a : Aff) (n : Nat) (r : Aff × Nat) : Bool :=
  (a.base == r.1.base && decide (r.1.off ≤ a.off) && decide (a.off + n ≤ r.1.off + r.2)) ||
  (r.1.base == none && decide (r.1.off ≤ a.lo st) && match a.hi st with
    | some h => decide (h + n ≤ r.1.off + r.2)
    | none => false)

/-- The regions `(a, n)` and `(b, m)` are disjoint. -/
def disj (st : Static) (a : Aff) (n : Nat) (b : Aff) (m : Nat) : Bool :=
  n == 0 || m == 0 ||
  (a.base == b.base && (decide (a.off + n ≤ b.off) || decide (b.off + m ≤ a.off))) ||
  (match a.hi st with | some h => decide (h + n ≤ b.lo st) | none => false) ||
  (match b.hi st with | some h => decide (h + m ≤ a.lo st) | none => false) ||
  st.sep.any fun p => (within st a n p.1 && within st b m p.2) || (within st a n p.2 && within st b m p.1)

/-- An exclusive upper bound of a value. -/
def SVal.bnd (st : Static) : SVal → Option Nat
  | .const n => some (n + 1)
  | .var k => st.ub[k]?
  | .reg0 _ => some two64
  | .mem0 _ n => some (256 ^ n)
  | .mod _ m => if 0 < m then some m else none
  | .addr a => if 0 ≤ a.lo st then (a.hi st).map fun h => (h + 1).toNat else none
  | .sx _ _ => some two64
  | .alu2i op _ _ x =>
    if op = .shloLImm64 then some two64 else if op = .andImm then some (x + 1) else none
  | .tbl vs _ => some (vs.foldr max 0 + 1)
  | _ => none

/-- `v mod m`, simplified: folded on a literal, dropped when a bound shows it does nothing, and
    `𝒵⁻¹_8(𝒵_k(w)) mod 2^(8k) = w mod 2^(8k)` for k = 2, 4. -/
def mkMod (st : Static) (v : SVal) (m : Nat) : SVal :=
  match v with
  | .const n => .const (n % m)
  | .sx k w =>
    if (k = 2 ∨ k = 4) ∧ m = 256 ^ k ∧ (w.bnd st).any (· ≤ 2 ^ (8 * k)) then
      (if (w.bnd st).any (· ≤ m) then w else .mod w m)
    else (if ((SVal.sx k w).bnd st).any (· ≤ m) then .sx k w else .mod (.sx k w) m)
  | v => if (v.bnd st).any (· ≤ m) then v else .mod v m

/-- An affine reading of a value. -/
def asAff : SVal → Option Aff
  | .const n => some ⟨none, n⟩
  | .var k => some ⟨some k, 0⟩
  | .addr a => some a
  | _ => none

/-- x mod M read as a signed offset: negative when x mod M ≥ M/2. -/
def shift (x M : Nat) : Int := if x % M < M / 2 then ((x % M : Nat) : Int) else ((x % M : Nat) : Int) - M

/-- The bounds show that `a` and `a'` are at least 0 and `a'` is below M. -/
def affOk (st : Static) (a a' : Aff) (M : Nat) : Bool :=
  decide (0 ≤ a.lo st) && decide (0 ≤ a'.lo st) && (a'.hi st).any (fun h => decide (h < (M : Int)))

/-- (a + x) mod M as an affine value, when the bounds show it neither wraps below 0 nor reaches M. -/
def addAff (st : Static) (a : Aff) (x M : Nat) : Option Aff :=
  if affOk st a ⟨a.base, a.off + shift x M⟩ M = true then some ⟨a.base, a.off + shift x M⟩ else none

/-- An affine value, as a named natural when its offset is 0. -/
def affVal (a : Aff) : SVal :=
  if a.off = 0 then (match a.base with | some k => .var k | none => .const 0) else .addr a

/-- The value (v + x) mod 2^64 (`fallback` when it is not affine). -/
def addv (st : Static) (v : SVal) (x : Nat) (fallback : SVal) : SVal :=
  match v with
  | .const c => .const ((c + x) % two64)
  | v => match (asAff v).bind fun a => addAff st a x two64 with
    | some a' => affVal a'
    | none => fallback

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

/-- The zero-extension idiom: `add_imm_32 0` of a value below 2^31 is the value, and
    `shlo_r_imm_64 s` of `shlo_l_imm_64 s` of w is w when w·2^s < 2^64. -/
def zextRule (st : Static) (op : TwoRegImmOp) (b : SVal) (x : Nat) : Option SVal :=
  if op = .addImm32 then
    (if x = 0 ∧ (b.bnd st).any (· ≤ 2 ^ 31) then some b else none)
  else if op = .shloRImm64 then
    match b with
    | .alu2i op' _ w s =>
      if op' = .shloLImm64 ∧ s % 64 = x % 64 ∧ (w.bnd st).any (fun bw => bw * 2 ^ (x % 64) ≤ two64)
      then some w else none
    | _ => none
  else none

def mkAlu2i (st : Static) (op : TwoRegImmOp) (a b : SVal) (x : Nat) : SVal :=
  match zextRule st op b x with
  | some v => v
  | none =>
    if op = .addImm64 then addv st b x (foldAlu2i op (.const 0) b x)
    else foldAlu2i op (if usesA op then a else .const 0) b x

/-- A lower bound of a value. -/
def SVal.lob (st : Static) : SVal → Nat
  | .const n => n
  | .var k => st.lb[k]?.getD 0
  | .addr a => (a.lo st).toNat
  | _ => 0

/-- v ≤ w, by the bounds. -/
def leB (st : Static) (v w : SVal) : Bool := (v.bnd st).any (· ≤ w.lob st + 1)

def foldAlu3 (op : ThreeRegOp) (a b d : SVal) : SVal :=
  match a, b, d with
  | .const p, .const q, .const r => .const (threeRegAlu op p q r)
  | a, b, d => .alu3 op a b d

def mkAlu3 (st : Static) (op : ThreeRegOp) (a b d : SVal) : SVal :=
  let f := foldAlu3 op a b (if usesD op then d else .const 0)
  match op, b with
  | .add64, .const q => addv st a q f
  | .sub64, .const q => if q < two64 then addv st a (two64 - q) f else f
  | .minU, _ => if leB st a b then a else if leB st b a then b else f
  | .maxU, _ => if leB st a b then b else if leB st b a then a else f
  | _, _ => f

def mkAlu2 (op : TwoRegOp) (a : SVal) : SVal :=
  match op, a with
  | .moveReg, a => a
  | op, .const p => .const (twoRegAlu op p)
  | op, a => .alu2 op a

/-- A load's value: unchanged (`k = 0`) or sign-extended from `k` octets. -/
def mkSx (st : Static) (k : Nat) (v : SVal) : SVal :=
  if k = 0 then v else
  match v with
  | .const p => .const (u64 (signed k p))
  | v => match v.bnd st with
    | some b => if b ≤ 2 ^ (8 * k - 1) ∧ k ≤ 8 then v else .sx k v
    | none => .sx k v

/-! ## Symbolic states -/

/-- A symbolic state: the 13 registers, memory cells `(a, n, v)` (μ_{a…+n} = ℰ_n(v)), and the
    regions written since the start. -/
structure SState where
  regs : List SVal
  cells : List (Aff × Nat × SVal)
  dirty : List (Aff × Nat)

/-- What `st` asserts of an environment. -/
def Pre (E : Env) (st : Static) : Prop :=
  (∀ k b, st.ub[k]? = some b → E.ρ k < b) ∧
  (∀ k b, st.lb[k]? = some b → b ≤ E.ρ k) ∧
  (∀ r ∈ st.rd, ∀ t, InReg E r t → E.μ.readable t = true) ∧
  (∀ r ∈ st.wr, ∀ t, InReg E r t → E.μ.writable t = true) ∧
  (∀ p ∈ st.sep, ∀ t, InReg E p.1 t → ¬ InReg E p.2 t)

/-- A machine state (ω, μ) is described by σ. -/
def Inv (E : Env) (σ : SState) (ω : Regs) (μ : Memory) : Prop :=
  σ.regs.length = 13 ∧
  (∀ r : Fin 13, ω.get r = UInt64.ofNat ((σ.regs.getD r.val (.const 0)).eval E)) ∧
  (∀ c ∈ σ.cells, 0 ≤ c.1.eval E ∧ c.1.eval E + c.2.1 ≤ two32 ∧
    μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) ∧
  (∀ t, t < two32 → (∀ d ∈ σ.dirty, ¬ InReg E d t) → μ.read t = E.μ.read t) ∧
  μ.pages = E.μ.pages

/-! ## Code -/

/-- A search tree keyed by naturals. -/
inductive NTree (α : Type) where
  | leaf
  | node (l : NTree α) (k : Nat) (v : α) (r : NTree α)

def NTree.find {α : Type} : NTree α → Nat → Option α
  | .leaf, _ => none
  | .node l k v r, i => if i < k then l.find i else if i = k then some v else r.find i

/-- Every entry of a tree satisfies `Q`. -/
def NTree.All {α : Type} (Q : Nat → α → Prop) : NTree α → Prop
  | .leaf => True
  | .node l k v r => Q k v ∧ l.All Q ∧ r.All Q

/-- The effect of a host call when registers hold literals: when ω_r = v for each (r, v) in
    `pre`, it writes ℰ_n(v) at the literal address a for `wr = some (a, n, v)`, sets the
    registers in `out` to literals, and leaves the rest of memory and the context unchanged. -/
structure HostEff where
  pre : List (Nat × Nat) := []
  wr : Option (Nat × Nat × Nat) := none
  out : List (Nat × Nat)
  deriving Repr

/-- The code a stretch runs through: at each pc its instruction and ı + 1 + skip(ı) (the `d_i` of
    the code facts), block starts (`bs_i`), jump-table entries (`jte_k`) and |**j**| (`jts`). -/
structure Prog where
  code : NTree (Instr × Nat)
  bs : NTree Bool
  jt : NTree Nat
  jsize : Nat
  /-- Host calls the executor may follow, by id: the effects (`HostEff`) it may take, the first
      whose preconditions hold. Their outcomes are justified by `HostOk`. -/
  hosts : NTree (List HostEff) := .leaf

/-- The facts of a `Prog` hold of the program `p` deblobs to. -/
def ProgHyp (p : ByteArray) (P : Program) (G : Prog) : Prop :=
  G.code.All (fun pc e => deblob p pc = some P ∧ P.decode pc = some e.1 ∧ P.next pc = e.2 ∧
      P.blockCost (P.blockStartOf pc) ≤ stepCostCap) ∧
  G.bs.All (fun n b => P.isBlockStart n = b) ∧
  G.jt.All (fun k t => P.jumpTable.getD k 0 = t) ∧
  P.jumpTable.size = G.jsize

def isBS (bs : NTree Bool) (n : Nat) : Bool := bs.find n == some true

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
  | .loadI8 => .load 1 1 | .loadI16 => .load 2 2 | .loadI32 => .load 4 4
  | .storeU8 => .store 1 | .storeU16 => .store 2 | .storeU32 => .store 4 | .storeU64 => .store 8
  | _ => .alu

variable (st : Static)

/-- An unsigned comparison of a value in `[lo, hi)` with `x` (§A.5.8), when the interval decides it. -/
def decideCond (op : RegImmOffsetOp) (lo hi x : Nat) : Option Bool :=
  match op with
  | .branchEqImm => if x < lo ∨ hi ≤ x then some false else none
  | .branchNeImm => if x < lo ∨ hi ≤ x then some true else none
  | .branchLtUImm => if hi ≤ x then some true else if x ≤ lo then some false else none
  | .branchLeUImm => if hi ≤ x + 1 then some true else if x < lo then some false else none
  | .branchGeUImm => if x ≤ lo then some true else if hi ≤ x then some false else none
  | .branchGtUImm => if x < lo then some true else if hi ≤ x + 1 then some false else none
  | _ => none

/-- The unsigned comparison that a signed one (§A.5.8) equals on operands below 2^63. -/
def toU : RegImmOffsetOp → Option RegImmOffsetOp
  | .branchLtSImm => some .branchLtUImm
  | .branchLeSImm => some .branchLeUImm
  | .branchGeSImm => some .branchGeUImm
  | .branchGtSImm => some .branchGtUImm
  | _ => none

/-- A signed comparison of a value below 2^63 with a negative immediate (2^63 ≤ x < 2^64). -/
def negImm : RegImmOffsetOp → Bool
  | .branchGeUImm | .branchGtUImm => true
  | _ => false

/-- A branch condition against an immediate: computed on a literal, or decided by the bounds;
    a signed one on a value below 2^63. -/
def scond (op : RegImmOffsetOp) (v : SVal) (x : Nat) : Option Bool :=
  match v with
  | .const c => some (regImmBranchCond op c x)
  | v => (v.bnd st).bind fun hi =>
    match toU op with
    | none => decideCond op (v.lob st) hi x
    | some u =>
      if hi ≤ 2 ^ 63 then
        if x < 2 ^ 63 then decideCond u (v.lob st) hi x
        else if x < two64 then some (negImm u) else none
      else none

/-- Two addresses on a common base, both at least 0: their offsets. -/
def sameBase (v w : SVal) : Option (Int × Int) :=
  match v, w with
  | .addr a, .addr b =>
    if a.base == b.base && decide (0 ≤ a.lo st) && decide (0 ≤ b.lo st) then some (a.off, b.off)
    else none
  | _, _ => none

/-- v < w, when a common base or the bounds decide it. -/
def ltU (v w : SVal) : Option Bool :=
  match sameBase st v w with
  | some (p, q) => some (decide (p < q))
  | none =>
    if (v.bnd st).any (· ≤ w.lob st) then some true
    else if (w.bnd st).any (· ≤ v.lob st + 1) then some false
    else none

/-- v = w, when equal values, a common base or the bounds decide it. -/
def eqU (v w : SVal) : Option Bool :=
  if v == w then some true else
  match sameBase st v w with
  | some (p, q) => some (p == q)
  | none =>
    if (v.bnd st).any (· ≤ w.lob st) || (w.bnd st).any (· ≤ v.lob st) then some false else none

/-- A comparison of two registers (§A.5.11), when it is decided; signed ones on values below
    2^63, where they equal the unsigned ones. -/
def scond2 (op : TwoRegOffsetOp) (v w : SVal) : Option Bool :=
  let nn := (v.bnd st).any (· ≤ 2 ^ 63) && (w.bnd st).any (· ≤ 2 ^ 63)
  match op with
  | .branchEq => eqU st v w
  | .branchNe => (eqU st v w).map (!·)
  | .branchLtU => ltU st v w
  | .branchGeU => (ltU st v w).map (!·)
  | .branchLtS => if nn then ltU st v w else none
  | .branchGeS => if nn then (ltU st v w).map (!·) else none

/-- The value of register `r`, as `(ω_r).toNat`. -/
def rdv (σ : SState) (r : Nat) : SVal := mkMod st (σ.regs.getD r (.const 0)) two64

def setv (σ : SState) (r : Nat) (v : SVal) : SState := { σ with regs := σ.regs.set r v }

/-- The address (v + x) mod 2^32 of `n` octets, as an affine address in ℕ_{2^32}. -/
def mkAddr (v : SVal) (x n : Nat) : Option Aff :=
  let a? : Option Aff := match v with
    | .const c => some ⟨none, ((c + x) % two32 : Nat)⟩
    | v => (asAff v).bind fun a => addAff st a x two32
  match a? with
  | some a => if valid st a n then some a else none
  | none => none

/-- Literal octets of `n` at `a` assembled, left to right, from cells on the same base holding
    literals. -/
def assemble (cells : List (Aff × Nat × SVal)) : Nat → Aff → Nat → Option Nat
  | 0, _, n => if n = 0 then some 0 else none
  | fuel + 1, a, n =>
    if n = 0 then some 0 else
    match cells.find? (fun c => c.1.base == a.base && decide (c.1.off ≤ a.off) &&
        decide (a.off < c.1.off + c.2.1) && c.2.2.isConst) with
    | some (c, m, .const v) =>
      (assemble cells fuel ⟨a.base, a.off + (min (c.off + m - a.off).toNat n : Nat)⟩
          (n - min (c.off + m - a.off).toNat n)).map fun r =>
        v / 256 ^ (a.off - c.off).toNat % 256 ^ min (c.off + m - a.off).toNat n +
          256 ^ min (c.off + m - a.off).toNat n * r
    | _ => none

/-- What survives of a literal cell on the store's base that a store to `(a, n)` partly
    overwrites. -/
def frags (a : Aff) (n : Nat) : Aff × Nat × SVal → List (Aff × Nat × SVal)
  | (c, m, .const v) =>
    if c.base == a.base then
      (if c.off < a.off then [(c, (min (a.off - c.off) m).toNat, .const v)] else []) ++
      (if a.off + n < c.off + m then
        [(⟨a.base, max (a.off + n) c.off⟩, (c.off + m - max (a.off + n) c.off).toNat,
          .const (v / 256 ^ (max (a.off + n) c.off - c.off).toNat))] else [])
    else []
  | _ => []

/-- The value loaded from `(a, n)`: a cell recorded there, literal cells covering it, or the start
    memory when nothing written since may meet it. -/
def loadVal (σ : SState) (a : Aff) (n : Nat) : Option SVal :=
  match σ.cells.find? (fun c => c.1 == a && c.2.1 == n) with
  | some c => some (mkMod st c.2.2 (2 ^ (8 * n)))
  | none =>
    match assemble σ.cells n a n with
    | some w => some (.const (w % 256 ^ n))
    | none => if σ.dirty.all (fun d => disj st a n d.1 d.2) then some (.mem0 a n) else none

/-- Store ℰ_n(v) at `a`. -/
def sstore (σ : SState) (a : Aff) (n : Nat) (v : SVal) : Option SState :=
  if valid st a n && st.wr.any (within st a n) then
    some { regs := σ.regs
           cells := (a, n, v) :: (σ.cells.filter (fun c => disj st c.1 c.2.1 a n) ++
             (σ.cells.filter (fun c => !disj st c.1 c.2.1 a n)).flatMap (frags a n))
           dirty := if σ.dirty.any (within st a n) then σ.dirty else (a, n) :: σ.dirty }
  else none

/-- Load `n` octets at `a` into register `d`, sign-extended from `k` octets unless `k = 0`. -/
def sload (σ : SState) (d : Nat) (a : Aff) (n k : Nat) : Option SState :=
  if valid st a n && (st.rd.any (within st a n) || st.wr.any (within st a n)) then
    (loadVal st σ a n).map fun v => setv σ d (mkSx st k v)
  else none

/-- A table address: v = c + i (mod 2^64) by `add_64` or `add_imm_64` (§A.5.10, §A.5.13). -/
def idxOf1 : SVal → Option (Nat × SVal)
  | .alu3 .add64 i (.const c) _ => some (c, i)
  | .alu3 .add64 (.const c) i _ => some (c, i)
  | .alu2i .addImm64 _ i c => some (c, i)
  | _ => none

/-- `idxOf1`, also under a reduction mod 2^64. -/
def idxOf : SVal → Option (Nat × SVal)
  | .mod v m => if m = two64 then idxOf1 v else none
  | v => idxOf1 v

/-- The literals of `n` octets at a, a + 1, …, a + b − 1. -/
def tvals (σ : SState) (n : Nat) : Nat → Nat → Option (List Nat)
  | _, 0 => some []
  | a, b + 1 =>
    match loadVal st σ ⟨none, a⟩ n, tvals σ n (a + 1) b with
    | some (.const w), some vs => some (w :: vs)
    | _, _ => none

/-- Load `n` octets at v + x into `d` when v is a table base plus an index of at most 4096
    values, and the table's entries are literals: entry `i` of the table. -/
def tload (σ : SState) (d : Nat) (v : SVal) (x n k : Nat) : Option SState :=
  match idxOf v with
  | none => none
  | some (c, i) =>
    match i.bnd st with
    | none => none
    | some b =>
      if 0 < b && b ≤ 4096 && decide (c + x + (b - 1) + n ≤ two32) &&
          (st.rd.any (within st ⟨none, c + x⟩ (b - 1 + n)) ||
            st.wr.any (within st ⟨none, c + x⟩ (b - 1 + n))) then
        (tvals st σ n (c + x) b).map fun vs => setv σ d (mkSx st k (.tbl vs i))
      else none

/-- Load `n` octets at v + x into `d`: at an affine address, else from a table. -/
def ldv (σ : SState) (d : Nat) (v : SVal) (x n k : Nat) : Option SState :=
  match mkAddr st v x n with
  | some ad => sload st σ d ad n k
  | none => tload st σ d v x n k

/-- djump(a) when it continues (GP eq. `jumptablealignment`): the target, if the facts show it. -/
def sdjump (G : Prog) (a : Nat) : Option Nat :=
  if a = 2 ^ 32 - 2 ^ 16 ∨ a = 0 ∨ a > G.jsize * 2 ∨ a % 2 ≠ 0 then none else
  match G.jt.find (a / 2 - 1) with
  | some t => if isBS G.bs t then some t else none
  | none => none

/-- One step from `pc`: the next pc and state, or `none` if the executor cannot follow it. -/
def sstep (G : Prog) (pc : Nat) (σ : SState) : Option (Nat × SState) :=
  match G.code.find pc with
  | none => none
  | some e =>
    match e.1 with
    | .noArgs .unlikely => some (e.2, σ)
    | .noArgs .fallthrough => if isBS G.bs e.2 then some (e.2, σ) else none
    | .oneOffset .jump x =>
      if 0 ≤ x && isBS G.bs x.toNat then some (x.toNat, σ) else none
    | .regImm .loadImm a x => some (e.2, setv σ a.val (.const x.toNat))
    | .regImm .jumpInd a x =>
      match rdv st σ a.val with
      | .const v => (sdjump G ((v + x.toNat) % two32)).map (·, σ)
      | _ => none
    | .regImm op a x =>
      match rkind op with
      | .store n =>
        ((mkAddr st (.const 0) x.toNat n).bind fun ad =>
          sstore st σ ad n (mkMod st (rdv st σ a.val) (2 ^ (8 * n)))).map (e.2, ·)
      | .load n k =>
        (ldv st σ a.val (.const 0) x.toNat n k).map (e.2, ·)
      | .alu => none
    | .regExtImm .loadImm64 a x => some (e.2, setv σ a.val (.const x.toNat))
    | .twoImm op x y =>
      ((mkAddr st (.const 0) x.toNat op.width).bind fun ad =>
        sstore st σ ad op.width (.const (y.toNat % 2 ^ (8 * op.width)))).map (e.2, ·)
    | .twoReg op d a => some (e.2, setv σ d.val (mkAlu2 op (rdv st σ a.val)))
    | .threeReg op a b d =>
      some (e.2, setv σ d.val (mkAlu3 st op (rdv st σ a.val) (rdv st σ b.val) (rdv st σ d.val)))
    | .twoRegImm op a b x =>
      match tkind op with
      | .alu => some (e.2, setv σ a.val (mkAlu2i st op (rdv st σ a.val) (rdv st σ b.val) x.toNat))
      | .store n =>
        ((mkAddr st (rdv st σ b.val) x.toNat n).bind fun ad =>
          sstore st σ ad n (mkMod st (rdv st σ a.val) (2 ^ (8 * n)))).map (e.2, ·)
      | .load n k =>
        (ldv st σ a.val (rdv st σ b.val) x.toNat n k).map (e.2, ·)
    | .regTwoImm op a x y =>
      ((mkAddr st (rdv st σ a.val) x.toNat op.width).bind fun ad =>
        sstore st σ ad op.width (.const (y.toNat % 2 ^ (8 * op.width)))).map (e.2, ·)
    | .regImmOffset op a x y =>
      if op = .loadImmJump then
        if 0 ≤ y && isBS G.bs y.toNat then some (y.toNat, setv σ a.val (.const x.toNat)) else none
      else
        match scond st op (rdv st σ a.val) x.toNat with
        | some c =>
          if 0 ≤ y && isBS G.bs y.toNat && isBS G.bs e.2 then
            some (if c then y.toNat else e.2, σ)
          else none
        | none => none
    | .twoRegTwoImm .loadImmJumpInd a b x y =>
      match rdv st σ b.val with
      | .const v => (sdjump G ((v + y.toNat) % two32)).map (·, setv σ a.val (.const x.toNat))
      | _ => none
    | .twoRegOffset op a b x =>
      match scond2 st op (rdv st σ a.val) (rdv st σ b.val) with
      | some c =>
        if 0 ≤ x && isBS G.bs x.toNat && isBS G.bs e.2 then
          some (if c then x.toNat else e.2, σ)
        else none
      | none => none
    | _ => none

/-- Set registers to literals. -/
def hset (σ : SState) : List (Nat × Nat) → SState
  | [] => σ
  | (r, v) :: rs => hset (setv σ r (.const v)) rs

/-- The preconditions of a host effect hold of σ. -/
def hpre (σ : SState) (e : HostEff) : Bool :=
  e.pre.all fun p => decide (p.1 < 13) && rdv st σ p.1 == .const p.2

/-- The write of a host effect. -/
def hwr (σ : SState) : Option (Nat × Nat × Nat) → Option SState
  | none => some σ
  | some (a, n, v) => if a < two32 ∧ a + n ≤ two32 then sstore st σ ⟨none, a⟩ n (.const v) else none

/-- A host effect applied to σ. -/
def happly (σ : SState) (e : HostEff) : Option SState :=
  if e.out.all (·.1 < 13) then (hwr st σ e.wr).map (hset · e.out) else none

/-- A host call `ecalli h` (§A.5.2) whose id the host table lists: the next pc and state. -/
def hstep (G : Prog) (pc : Nat) (σ : SState) : Option (Nat × SState) :=
  match G.code.find pc with
  | some (.oneImm .ecalli h, n) =>
    match G.hosts.find h.toNat with
    | some es =>
      match es.find? (hpre st σ) with
      | some e => (happly st σ e).map (n, ·)
      | none => none
    | none => none
  | _ => none

/-- Run exactly `k` steps from `pc`, which must end at `target`: the final state. -/
def srun (G : Prog) (target : Nat) : Nat → Nat → SState → Option SState
  | 0, pc, σ => if pc = target then some σ else none
  | k + 1, pc, σ =>
    match sstep st G pc σ with
    | some (pc', σ') => srun G target k pc' σ'
    | none =>
      match hstep st G pc σ with
      | some (pc', σ') => srun G target k pc' σ'
      | none => none

end PVM.SymExec
