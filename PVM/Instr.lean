import PVM.Blob

/-!
# Typed instructions and decoding

Decoding is kept separate from execution: `Program.decode` turns the octets at an opcode index
into an `Instr`, following the operand definitions at the head of each subsubsection of GP
v0.8.0 §A.5 (`sec:instructiontables`); `PVM.Exec` gives each `Instr` its meaning.

Immediates ν are stored already sign-extended (𝒳) as values in ℕ_{2^64}. Offsets (ı + 𝒵(…)) are
stored as integers, since the paper does not reduce them modulo anything.
-/

namespace PVM

/-- A decoded instruction: one constructor per argument format of GP §A.5, carrying the
    opcode (an enumeration generated from the paper) and the decoded operands. -/
inductive Instr where
  /-- §A.5.1, no arguments. -/
  | noArgs (op : NoArgsOp)
  /-- §A.5.2, one immediate ν_X. -/
  | oneImm (op : OneImmOp) (x : UInt64)
  /-- §A.5.3, one register r_A and one extended-width immediate ν_X. -/
  | regExtImm (op : RegExtImmOp) (a : RegIdx) (x : UInt64)
  /-- §A.5.4, two immediates ν_X, ν_Y. -/
  | twoImm (op : TwoImmOp) (x y : UInt64)
  /-- §A.5.5, one offset ν_X = ı + 𝒵(…). -/
  | oneOffset (op : OneOffsetOp) (x : Int)
  /-- §A.5.6, one register r_A and one immediate ν_X. -/
  | regImm (op : RegImmOp) (a : RegIdx) (x : UInt64)
  /-- §A.5.7, one register r_A and two immediates ν_X, ν_Y. -/
  | regTwoImm (op : RegTwoImmOp) (a : RegIdx) (x y : UInt64)
  /-- §A.5.8, one register r_A, one immediate ν_X and one offset ν_Y. -/
  | regImmOffset (op : RegImmOffsetOp) (a : RegIdx) (x : UInt64) (y : Int)
  /-- §A.5.9, two registers r_D, r_A. -/
  | twoReg (op : TwoRegOp) (d a : RegIdx)
  /-- §A.5.10, two registers r_A, r_B and one immediate ν_X. -/
  | twoRegImm (op : TwoRegImmOp) (a b : RegIdx) (x : UInt64)
  /-- §A.5.11, two registers r_A, r_B and one offset ν_X. -/
  | twoRegOffset (op : TwoRegOffsetOp) (a b : RegIdx) (x : Int)
  /-- §A.5.12, two registers r_A, r_B and two immediates ν_X, ν_Y. -/
  | twoRegTwoImm (op : TwoRegTwoImmOp) (a b : RegIdx) (x y : UInt64)
  /-- §A.5.13, three registers r_A, r_B, r_D. -/
  | threeReg (op : ThreeRegOp) (a b d : RegIdx)
  deriving DecidableEq, Repr

/-- The opcode ζ_ı of an instruction. -/
def Instr.opcode : Instr → Nat
  | .noArgs op => op.opcode
  | .oneImm op _ => op.opcode
  | .regExtImm op _ _ => op.opcode
  | .twoImm op _ _ => op.opcode
  | .oneOffset op _ => op.opcode
  | .regImm op _ _ => op.opcode
  | .regTwoImm op _ _ _ => op.opcode
  | .regImmOffset op _ _ _ => op.opcode
  | .twoReg op _ _ => op.opcode
  | .twoRegImm op _ _ _ => op.opcode
  | .twoRegOffset op _ _ _ => op.opcode
  | .twoRegTwoImm op _ _ _ _ => op.opcode
  | .threeReg op _ _ _ => op.opcode

/-- The paper's name of an instruction's opcode. -/
def Instr.name : Instr → String
  | .noArgs op => op.name
  | .oneImm op _ => op.name
  | .regExtImm op _ _ => op.name
  | .twoImm op _ _ => op.name
  | .oneOffset op _ => op.name
  | .regImm op _ _ => op.name
  | .regTwoImm op _ _ _ => op.name
  | .regImmOffset op _ _ _ => op.name
  | .twoReg op _ _ => op.name
  | .twoRegImm op _ _ _ => op.name
  | .twoRegOffset op _ _ _ => op.name
  | .twoRegTwoImm op _ _ _ _ => op.name
  | .threeReg op _ _ _ => op.name

namespace Program

/-- ζ_{start…+n}, the octets `start, …, start + n - 1` of ζ. -/
def zetaBytes (P : Program) (start n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (P.zeta (start + i))

/-- ℰ_n⁻¹(ζ_{start…+n}). -/
def zetaLE (P : Program) (start n : Nat) : Nat := Num.decodeLE (P.zetaBytes start n)

/-- 𝒳_n(ℰ_n⁻¹(ζ_{start…+n})), a sign-extended immediate. -/
def immAt (P : Program) (start n : Nat) : UInt64 := UInt64.ofNat (Num.sext n (P.zetaLE start n))

/-- ı + 𝒵_n(ℰ_n⁻¹(ζ_{start…+n})), an offset relative to the instruction at `i`. -/
def offsetAt (P : Program) (i start n : Nat) : Int := (i : Int) + Num.signed n (P.zetaLE start n)

/-- Decode the instruction at opcode index `ı` (GP §A.5), with ℓ = skip(ı). Returns `none`
    when ζ_ı ∉ U. -/
def decode (P : Program) (i : Nat) : Option Instr :=
  let op := P.zeta i
  let l := P.skip i
  let lo := regIdx (P.zeta (i + 1) % 16)          -- min(12, ζ_{ı+1} mod 16)
  let hi := regIdx (P.zeta (i + 1) / 16)          -- min(12, ⌊ζ_{ı+1} ÷ 16⌋)
  match formatOf? op with
  | none => none
  | some .noArgs => (NoArgsOp.ofOpcode? op).map .noArgs
  | some .oneImm =>
    -- l_X = min(4, ℓ), ν_X = 𝒳_{l_X}(ℰ⁻¹(ζ_{ı+1…+l_X}))
    let lX := min 4 l
    (OneImmOp.ofOpcode? op).map fun o => .oneImm o (P.immAt (i + 1) lX)
  | some .regExtImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), ν_X = ℰ_8⁻¹(ζ_{ı+2…+8})
    (RegExtImmOp.ofOpcode? op).map fun o => .regExtImm o lo (UInt64.ofNat (P.zetaLE (i + 2) 8))
  | some .twoImm =>
    -- l_X = min(4, ζ_{ı+1} mod 8), l_Y = min(4, max(0, ℓ − l_X − 1))
    let lX := min 4 (P.zeta (i + 1) % 8)
    let lY := min 4 (l - lX - 1)
    (TwoImmOp.ofOpcode? op).map fun o =>
      .twoImm o (P.immAt (i + 2) lX) (P.immAt (i + 2 + lX) lY)
  | some .oneOffset =>
    -- l_X = min(4, ℓ), ν_X = ı + 𝒵_{l_X}(ℰ⁻¹(ζ_{ı+1…+l_X}))
    let lX := min 4 l
    (OneOffsetOp.ofOpcode? op).map fun o => .oneOffset o (P.offsetAt i (i + 1) lX)
  | some .regImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), l_X = min(4, max(0, ℓ − 1))
    let lX := min 4 (l - 1)
    (RegImmOp.ofOpcode? op).map fun o => .regImm o lo (P.immAt (i + 2) lX)
  | some .regTwoImm =>
    -- l_X = min(4, ⌊ζ_{ı+1} ÷ 16⌋ mod 8), l_Y = min(4, max(0, ℓ − l_X − 1))
    let lX := min 4 (P.zeta (i + 1) / 16 % 8)
    let lY := min 4 (l - lX - 1)
    (RegTwoImmOp.ofOpcode? op).map fun o =>
      .regTwoImm o lo (P.immAt (i + 2) lX) (P.immAt (i + 2 + lX) lY)
  | some .regImmOffset =>
    -- as §A.5.7, but ν_Y = ı + 𝒵_{l_Y}(ℰ⁻¹(ζ_{ı+2+l_X…+l_Y}))
    let lX := min 4 (P.zeta (i + 1) / 16 % 8)
    let lY := min 4 (l - lX - 1)
    (RegImmOffsetOp.ofOpcode? op).map fun o =>
      .regImmOffset o lo (P.immAt (i + 2) lX) (P.offsetAt i (i + 2 + lX) lY)
  | some .twoReg =>
    -- r_D = min(12, ζ_{ı+1} mod 16), r_A = min(12, ⌊ζ_{ı+1} ÷ 16⌋)
    (TwoRegOp.ofOpcode? op).map fun o => .twoReg o lo hi
  | some .twoRegImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), r_B = min(12, ⌊ζ_{ı+1} ÷ 16⌋), l_X = min(4, max(0, ℓ − 1))
    let lX := min 4 (l - 1)
    (TwoRegImmOp.ofOpcode? op).map fun o => .twoRegImm o lo hi (P.immAt (i + 2) lX)
  | some .twoRegOffset =>
    let lX := min 4 (l - 1)
    (TwoRegOffsetOp.ofOpcode? op).map fun o => .twoRegOffset o lo hi (P.offsetAt i (i + 2) lX)
  | some .twoRegTwoImm =>
    -- l_X = min(4, ζ_{ı+2} mod 8), l_Y = min(4, max(0, ℓ − l_X − 2))
    let lX := min 4 (P.zeta (i + 2) % 8)
    let lY := min 4 (l - lX - 2)
    (TwoRegTwoImmOp.ofOpcode? op).map fun o =>
      .twoRegTwoImm o lo hi (P.immAt (i + 3) lX) (P.immAt (i + 3 + lX) lY)
  | some .threeReg =>
    -- r_A = min(12, ζ_{ı+1} mod 16), r_B = min(12, ⌊ζ_{ı+1} ÷ 16⌋), r_D = min(12, ζ_{ı+2})
    -- (the paper does not reduce ζ_{ı+2} mod 16 here; README, note 4)
    (ThreeRegOp.ofOpcode? op).map fun o => .threeReg o lo hi (regIdx (P.zeta (i + 2)))

end Program

end PVM

namespace PVM

/-- The host-call ids a program can ever request: the immediate ν_X of every `ecalli` at an
    opcode index where 𝔳_inst holds (GP §A.1, §A.5.2). Ψ only steps at such indices, so this
    syntactic scan bounds every host call (`PVM.psi_hostId_mem` in `PVM.Theorems.HostIds`). -/
def Program.hostCallIds (P : Program) : List Nat :=
  (List.range P.code.size).filterMap fun i =>
    if P.vInst i then
      match P.decode i with
      | some (.oneImm .ecalli x) => some x.toNat
      | _ => none
    else none

/-- `Program.hostCallIds` of a blob's program; empty if the blob does not parse (then Ψ panics
    on its first step and makes no host call). -/
def hostCallIdsOf (p : ByteArray) : List Nat :=
  match Blob.parse? p with
  | some P => P.hostCallIds
  | none => []

end PVM
