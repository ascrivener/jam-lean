import PVM.Instr
import PVM.Memory

/-!
# Instruction semantics: the mutation tables of GP v0.8.0 §A.5

`exec` gives, for one decoded instruction, the paper's (ε, ı', ω', μ') of the regular
execution, together with the index sets **r** and **w** by which μ is read and written. The
single-step function Ψ₁ (`PVM.Machine`) combines this with the gas charge and with ε^μ.

Unless an instruction says otherwise: ε = ▸, ı' = ı + 1 + skip(ı), ω' = ω, μ' = μ (§A.4).

All arithmetic follows the paper's formulas over ℕ and ℤ; register values are read with
`toNat` and written back with `UInt64.ofNat` (every result is already in ℕ_{2^64}).
-/

namespace PVM

/-- Exit reasons and the continuation marker ▸ (GP §A.1, §A.4):
    ▸ (`cont`), ∎ (`halt`), ☇ (`panic`), ∞ (`oog`), F × a (`fault a`), h̵ × h (`host h`). -/
inductive Status where
  | cont
  | halt
  | panic
  | oog
  | fault (addr : UInt64)
  | host (id : UInt64)
  deriving DecidableEq, Repr

/-- The regular-execution result of one instruction (GP §A.4–A.5): ε, ı', ω', μ', and the sets
    **r** (indices read) and **w** (indices written) used to compute ε^μ. -/
structure Mutation where
  /-- ε -/
  status : Status
  /-- ı' -/
  pc : Nat
  /-- ω' -/
  regs : Regs
  /-- μ' -/
  mem : Memory
  /-- **r** -/
  reads : List Nat := []
  /-- **w** -/
  writes : List Nat := []

/-- Width in octets of a store of §A.5.4. -/
def TwoImmOp.width : TwoImmOp → Nat
  | .storeImmU8 => 1 | .storeImmU16 => 2 | .storeImmU32 => 4 | .storeImmU64 => 8

/-- Width in octets of a store of §A.5.7. -/
def RegTwoImmOp.width : RegTwoImmOp → Nat
  | .storeImmIndU8 => 1 | .storeImmIndU16 => 2 | .storeImmIndU32 => 4 | .storeImmIndU64 => 8

namespace Exec

open Num

/-- The indices `a, a+1, …, a+n-1` of μ^↺_{a…+n}. -/
def indices (a n : Nat) : List Nat := (List.range n).map (a + ·)

/-- 𝒵_8 and 𝒵_8⁻¹, written `𝒵` and `𝒵⁻¹` without subscript in the paper. -/
abbrev s64 (a : Nat) : Int := signed 8 a
/-- 𝒵_8⁻¹. -/
abbrev u64 (a : Int) : Nat := unsigned 8 a

/-- Boolean as a register value (`set_*` instructions). -/
def ofBool (b : Bool) : Nat := if b then 1 else 0

/-- Bitwise operation on the 64-bit representations: ∀ i ∈ ℕ_64 : ℬ_8(r)_i = f(ℬ_8(a)_i, ℬ_8(b)_i). -/
def bitwise (f : Bool → Bool → Bool) (a b : Nat) : Nat := ofBits 64 fun i => f (bit a i) (bit b i)

/-- Two-register ALU operations, §A.5.9: ω'_D as a function of ω_A. -/
def twoRegAlu : TwoRegOp → Nat → Nat
  | .moveReg, a => a
  | .countSetBits64, a => popcount 64 a
  | .countSetBits32, a => popcount 32 (a % two32)
  | .leadingZeroBits64, a => leadingZeros 64 a
  | .leadingZeroBits32, a => leadingZeros 32 (a % two32)
  | .trailingZeroBits64, a => trailingZeros 64 a
  | .trailingZeroBits32, a => trailingZeros 32 (a % two32)
  | .signExtend8, a => u64 (signed 1 (a % 2 ^ 8))
  | .signExtend16, a => u64 (signed 2 (a % 2 ^ 16))
  | .zeroExtend16, a => a % 2 ^ 16
  | .reverseBytes, a => decodeLE (encodeLE 8 a).reverse

/-- The ALU operations of §A.5.10 (two registers and one immediate): ω'_A as a function of
    ω_A (used only by `cmov_*_imm`), ω_B and ν_X. `none` for the loads and stores. -/
def twoRegImmAlu : TwoRegImmOp → Nat → Nat → Nat → Option Nat
  | .addImm32, _, b, x => some <| sext 4 ((b + x) % two32)
  | .andImm, _, b, x => some <| bitwise (· && ·) b x
  | .xorImm, _, b, x => some <| bitwise (· ^^ ·) b x
  | .orImm, _, b, x => some <| bitwise (· || ·) b x
  | .mulImm32, _, b, x => some <| sext 4 ((b * x) % two32)
  | .setLtUImm, _, b, x => some <| ofBool (b < x)
  | .setLtSImm, _, b, x => some <| ofBool (s64 b < s64 x)
  | .shloLImm32, _, b, x => some <| sext 4 ((b * 2 ^ (x % 32)) % two32)
  | .shloRImm32, _, b, x => some <| sext 4 (b % two32 / 2 ^ (x % 32))
  | .sharRImm32, _, b, x => some <| u64 (floorShift (signed 4 (b % two32)) (x % 32))
  | .negAddImm32, _, b, x => some <| sext 4 (((x : Int) + two32 - b) % (two32 : Int)).toNat
  | .setGtUImm, _, b, x => some <| ofBool (b > x)
  | .setGtSImm, _, b, x => some <| ofBool (s64 b > s64 x)
  | .shloLImmAlt32, _, b, x => some <| sext 4 ((x * 2 ^ (b % 32)) % two32)
  | .shloRImmAlt32, _, b, x => some <| sext 4 (x % two32 / 2 ^ (b % 32))
  | .sharRImmAlt32, _, b, x => some <| u64 (floorShift (signed 4 (x % two32)) (b % 32))
  | .cmovIzImm, a, b, x => some <| if b = 0 then x else a
  | .cmovNzImm, a, b, x => some <| if b ≠ 0 then x else a
  | .addImm64, _, b, x => some <| (b + x) % two64
  | .mulImm64, _, b, x => some <| (b * x) % two64
  | .shloLImm64, _, b, x => some <| sext 8 ((b * 2 ^ (x % 64)) % two64)
  | .shloRImm64, _, b, x => some <| sext 8 (b / 2 ^ (x % 64))
  | .sharRImm64, _, b, x => some <| u64 (floorShift (s64 b) (x % 64))
  | .negAddImm64, _, b, x => some <| (x + two64 - b) % two64
  | .shloLImmAlt64, _, b, x => some <| (x * 2 ^ (b % 64)) % two64
  | .shloRImmAlt64, _, b, x => some <| x / 2 ^ (b % 64)
  | .sharRImmAlt64, _, b, x => some <| u64 (floorShift (s64 x) (b % 64))
  | .rotR64Imm, _, b, x => some <| rotr 64 b x
  | .rotR64ImmAlt, _, b, x => some <| rotr 64 x b
  | .rotR32Imm, _, b, x => some <| sext 4 (rotr 32 b x)
  | .rotR32ImmAlt, _, b, x => some <| sext 4 (rotr 32 x b)
  | _, _, _, _ => none

/-- Three-register operations, §A.5.13: ω'_D as a function of ω_A, ω_B and ω_D (the latter
    used only by `cmov_iz` and `cmov_nz`). -/
def threeRegAlu : ThreeRegOp → Nat → Nat → Nat → Nat
  | .add32, a, b, _ => sext 4 ((a + b) % two32)
  | .sub32, a, b, _ => sext 4 ((a + two32 - b % two32) % two32)
  | .mul32, a, b, _ => sext 4 ((a * b) % two32)
  | .divU32, a, b, _ => if b % two32 = 0 then two64 - 1 else sext 4 (a % two32 / (b % two32))
  | .divS32, a, b, _ =>
    let a' := signed 4 (a % two32)
    let b' := signed 4 (b % two32)
    if b' = 0 then two64 - 1
    else if a' = -2 ^ 31 ∧ b' = -1 then u64 a'
    else u64 (divRtz a' b')
  | .remU32, a, b, _ =>
    if b % two32 = 0 then sext 4 (a % two32) else sext 4 (a % two32 % (b % two32))
  | .remS32, a, b, _ =>
    let a' := signed 4 (a % two32)
    let b' := signed 4 (b % two32)
    if a' = -2 ^ 31 ∧ b' = -1 then 0 else u64 (smod a' b')
  | .shloL32, a, b, _ => sext 4 ((a * 2 ^ (b % 32)) % two32)
  | .shloR32, a, b, _ => sext 4 (a % two32 / 2 ^ (b % 32))
  | .sharR32, a, b, _ => u64 (floorShift (signed 4 (a % two32)) (b % 32))
  | .add64, a, b, _ => (a + b) % two64
  | .sub64, a, b, _ => (a + two64 - b) % two64
  | .mul64, a, b, _ => (a * b) % two64
  | .divU64, a, b, _ => if b = 0 then two64 - 1 else a / b
  | .divS64, a, b, _ =>
    if b = 0 then two64 - 1
    else if s64 a = -2 ^ 63 ∧ s64 b = -1 then a
    else u64 (divRtz (s64 a) (s64 b))
  | .remU64, a, b, _ => if b = 0 then a else a % b
  | .remS64, a, b, _ =>
    if s64 a = -2 ^ 63 ∧ s64 b = -1 then 0 else u64 (smod (s64 a) (s64 b))
  | .shloL64, a, b, _ => (a * 2 ^ (b % 64)) % two64
  | .shloR64, a, b, _ => a / 2 ^ (b % 64)
  | .sharR64, a, b, _ => u64 (floorShift (s64 a) (b % 64))
  | .and, a, b, _ => bitwise (· && ·) a b
  | .xor, a, b, _ => bitwise (· ^^ ·) a b
  | .or, a, b, _ => bitwise (· || ·) a b
  | .mulUpperSS, a, b, _ => u64 ((s64 a * s64 b).fdiv (2 ^ 64))
  | .mulUpperUU, a, b, _ => a * b / two64
  | .mulUpperSU, a, b, _ => u64 ((s64 a * (b : Int)).fdiv (2 ^ 64))
  | .setLtU, a, b, _ => ofBool (a < b)
  | .setLtS, a, b, _ => ofBool (s64 a < s64 b)
  | .cmovIz, a, b, d => if b = 0 then a else d
  | .cmovNz, a, b, d => if b ≠ 0 then a else d
  | .rotL64, a, b, _ => rotl 64 a b
  | .rotL32, a, b, _ => sext 4 (rotl 32 a b)
  | .rotR64, a, b, _ => rotr 64 a b
  | .rotR32, a, b, _ => sext 4 (rotr 32 a b)
  | .andInv, a, b, _ => bitwise (fun x y => x && !y) a b
  | .orInv, a, b, _ => bitwise (fun x y => x || !y) a b
  | .xnor, a, b, _ => bitwise (fun x y => !(x ^^ y)) a b
  | .max, a, b, _ => u64 (max (s64 a) (s64 b))
  | .maxU, a, b, _ => max a b
  | .min, a, b, _ => u64 (min (s64 a) (s64 b))
  | .minU, a, b, _ => min a b

/-- Branch conditions of §A.5.8 (`branch_*_imm`), comparing ω_A with ν_X. -/
def regImmBranchCond : RegImmOffsetOp → Nat → Nat → Bool
  | .loadImmJump, _, _ => false
  | .branchEqImm, a, x => a == x
  | .branchNeImm, a, x => a != x
  | .branchLtUImm, a, x => a < x
  | .branchLeUImm, a, x => a ≤ x
  | .branchGeUImm, a, x => a ≥ x
  | .branchGtUImm, a, x => a > x
  | .branchLtSImm, a, x => s64 a < s64 x
  | .branchLeSImm, a, x => s64 a ≤ s64 x
  | .branchGeSImm, a, x => s64 a ≥ s64 x
  | .branchGtSImm, a, x => s64 a > s64 x

/-- Branch conditions of §A.5.11, comparing ω_A with ω_B. -/
def twoRegBranchCond : TwoRegOffsetOp → Nat → Nat → Bool
  | .branchEq, a, b => a == b
  | .branchNe, a, b => a != b
  | .branchLtU, a, b => a < b
  | .branchLtS, a, b => s64 a < s64 b
  | .branchGeU, a, b => a ≥ b
  | .branchGeS, a, b => s64 a ≥ s64 b

end Exec

namespace Program

open Num Exec

/-- sjump(b) (GP §A.4): (☇, ı) if b ∉ ϖ, otherwise (▸, b). -/
def sjump (P : Program) (i : Nat) (b : Int) : Status × Nat :=
  if P.isBlockStartInt b then (.cont, b.toNat) else (.panic, i)

/-- branch(b, C) (GP §A.4): (☇, ı) if b ∉ ϖ ∨ ı + 1 + skip(ı) ∉ ϖ; (▸, ı + 1 + skip(ı)) if ¬C;
    otherwise (▸, b). -/
def branch (P : Program) (i : Nat) (b : Int) (c : Bool) : Status × Nat :=
  if !P.isBlockStartInt b || !P.isBlockStart (P.next i) then (.panic, i)
  else if !c then (.cont, P.next i)
  else (.cont, b.toNat)

/-- djump(a) (GP eq. `jumptablealignment`), with 𝖹_A = 2:
    (∎, ı) if a = 2^32 − 2^16; (☇, ı) if a = 0 ∨ a > |**j**|·𝖹_A ∨ a mod 𝖹_A ≠ 0 ∨ **j**_{a/𝖹_A − 1} ∉ ϖ;
    otherwise (▸, **j**_{a/𝖹_A − 1}). -/
def djump (P : Program) (i : Nat) (a : Nat) : Status × Nat :=
  if a = 2 ^ 32 - 2 ^ 16 then (.halt, i)
  else if a = 0 ∨ a > P.jumpTable.size * 2 ∨ a % 2 ≠ 0 then (.panic, i)
  else
    let t := P.jumpTable.getD (a / 2 - 1) 0
    if P.isBlockStart t then (.cont, t) else (.panic, i)

/-- The regular execution of instruction `ins` at `ı` (GP §A.4–A.5): (ε, ı', ω', μ') and the
    index sets **r** and **w**. -/
def exec (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (μ : Memory) : Mutation :=
  let r (k : RegIdx) : Nat := (ω.get k).toNat
  let set (k : RegIdx) (v : Nat) : Regs := ω.set k (UInt64.ofNat v)
  let dflt : Mutation := { status := .cont, pc := P.next i, regs := ω, mem := μ }
  let jumpTo (sp : Status × Nat) (regs : Regs) : Mutation := { dflt with status := sp.1, pc := sp.2, regs }
  let store (addr : Nat) (n : Nat) (v : Nat) : Mutation :=
    { dflt with mem := μ.writeN addr (encodeLE n v), writes := indices addr n }
  let load (k : RegIdx) (addr : Nat) (n : Nat) (f : Nat → Nat) : Mutation :=
    { dflt with regs := set k (f (decodeLE (μ.readN addr n))), reads := indices addr n }
  match ins with
  -- §A.5.1
  | .noArgs .trap => { dflt with status := .panic }
  | .noArgs .fallthrough => jumpTo (P.sjump i (P.next i)) ω
  | .noArgs .unlikely => dflt
  -- §A.5.2
  | .oneImm .ecalli x => { dflt with status := .host x }
  -- §A.5.3
  | .regExtImm .loadImm64 a x => { dflt with regs := set a x.toNat }
  -- §A.5.4: μ'^↺_{ν_X…+n} = ℰ_n(ν_Y mod 2^(8n))
  | .twoImm op x y => store x.toNat op.width (y.toNat % 2 ^ (8 * op.width))
  -- §A.5.5
  | .oneOffset .jump x => jumpTo (P.sjump i x) ω
  -- §A.5.6
  | .regImm op a x =>
    let xa := x.toNat
    match op with
    | .jumpInd => jumpTo (P.djump i ((r a + xa) % two32)) ω
    | .loadImm => { dflt with regs := set a xa }
    | .loadU8 => load a xa 1 id
    | .loadI8 => load a xa 1 (sext 1)
    | .loadU16 => load a xa 2 id
    | .loadI16 => load a xa 2 (sext 2)
    | .loadU32 => load a xa 4 id
    | .loadI32 => load a xa 4 (sext 4)
    | .loadU64 => load a xa 8 id
    | .storeU8 => store xa 1 (r a % 2 ^ 8)
    | .storeU16 => store xa 2 (r a % 2 ^ 16)
    | .storeU32 => store xa 4 (r a % 2 ^ 32)
    | .storeU64 => store xa 8 (r a)
  -- §A.5.7: μ'^↺_{ω_A+ν_X…+n} = ℰ_n(ν_Y mod 2^(8n))
  | .regTwoImm op a x y => store (r a + x.toNat) op.width (y.toNat % 2 ^ (8 * op.width))
  -- §A.5.8
  | .regImmOffset .loadImmJump a x y => jumpTo (P.sjump i y) (set a x.toNat)
  | .regImmOffset op a x y => jumpTo (P.branch i y (regImmBranchCond op (r a) x.toNat)) ω
  -- §A.5.9
  | .twoReg op d a => { dflt with regs := set d (twoRegAlu op (r a)) }
  -- §A.5.10
  | .twoRegImm op a b x =>
    let addr := r b + x.toNat
    match op with
    | .storeIndU8 => store addr 1 (r a % 2 ^ 8)
    | .storeIndU16 => store addr 2 (r a % 2 ^ 16)
    | .storeIndU32 => store addr 4 (r a % 2 ^ 32)
    | .storeIndU64 => store addr 8 (r a)
    | .loadIndU8 => load a addr 1 id
    | .loadIndI8 => load a addr 1 (fun v => u64 (signed 1 v))
    | .loadIndU16 => load a addr 2 id
    | .loadIndI16 => load a addr 2 (fun v => u64 (signed 2 v))
    | .loadIndU32 => load a addr 4 id
    | .loadIndI32 => load a addr 4 (fun v => u64 (signed 4 v))
    | .loadIndU64 => load a addr 8 id
    | op => { dflt with regs := set a ((twoRegImmAlu op (r a) (r b) x.toNat).getD 0) }
  -- §A.5.11
  | .twoRegOffset op a b x => jumpTo (P.branch i x (twoRegBranchCond op (r a) (r b))) ω
  -- §A.5.12: djump((ω_B + ν_Y) mod 2^32), ω'_A = ν_X
  | .twoRegTwoImm .loadImmJumpInd a b x y =>
    jumpTo (P.djump i ((r b + y.toNat) % two32)) (set a x.toNat)
  -- §A.5.13
  | .threeReg op a b d => { dflt with regs := set d (threeRegAlu op (r a) (r b) (r d)) }

end Program

end PVM
