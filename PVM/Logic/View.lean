import PVM.Gas

/-!
# A program's code, seen through its reads

Everything Ψ and the gas model compute from a program's code reads it only through ζ (the
instruction octets), (**k** ⌢ [1, 1, …]), **k** with zeros beyond, |**c**| and |**k**|. A
`CodeView` is exactly those reads, and this file repeats, over a `CodeView`, the definitions of
`PVM.Blob`, `PVM.Instr` and `PVM.Gas` that use them: skip, 𝔳_inst, 𝔳_blob, ϖ, decoding, and the
block cost ϱ^Δ with its simulation 𝔛. Each repeat is the model's definition with `P.zeta` read
as `V.zeta` and so on, and `Program.view` makes the two agree by `rfl` (the `*_view` theorems
below), so nothing here is a second reading of the paper.

The point is evaluation: a program parsed from a blob holds its code in a `ByteArray`, which
the kernel can only index by walking a list. A `CodeView` whose reads are arithmetic on a few
large numbers (`PVM.Logic.ChunkBlob`) lets the kernel decide facts about a 200 kB program.
-/

namespace PVM

/-- The reads of a program's code (GP §A.1–A.3): ζ, (**k** ⌢ [1, 1, …]), **k** with zeros beyond,
    |**c**| and |**k**|. -/
structure CodeView where
  /-- ζ_i ≡ (**c** ⌢ [0, 0, …])_i. -/
  zeta : Nat → Nat
  /-- (**k** ⌢ [1, 1, …])_i. -/
  maskExt : Nat → Bool
  /-- **k**_i, 0 beyond **k**. -/
  maskAt : Nat → Bool
  /-- |**c**|. -/
  codeSize : Nat
  /-- |**k**|. -/
  maskSize : Nat

/-- A program's reads. -/
def Program.view (P : Program) : CodeView := ⟨P.zeta, P.maskExt, P.maskAt, P.code.size, P.mask.size⟩

namespace CodeView

/-- ζ at an integer index, 0 at negative indices (as `Program.zetaInt`). -/
def zetaInt (V : CodeView) (i : Int) : Nat := if i < 0 then 0 else V.zeta i.toNat

/-- skip(i) = min(24, j ∈ ℕ : (**k** ⌢ [1, 1, …])_{i+1+j} = 1) (GP eq. `skip`). -/
def skip (V : CodeView) (i : Nat) : Nat :=
  ((List.range 24).find? fun j => V.maskExt (i + 1 + j)).getD 24

/-- The index of the instruction following the one at `i`: i + 1 + skip(i). -/
def next (V : CodeView) (i : Nat) : Nat := i + 1 + V.skip i

/-- 𝔳_inst(**c**, **k**, ı) = |**k**| = |**c**| ∧ ı < |**k**| ∧ **k**_ı = 1 ∧ **c**_ı ∈ U (GP §A.1). -/
def vInst (V : CodeView) (i : Nat) : Bool :=
  V.maskSize == V.codeSize && decide (i < V.maskSize) && V.maskAt i && isValidOpcode (V.zeta i)

/-- 𝔳_blob(**c**, **k**, ı) (GP §A.1), with explicit fuel.

    Every recursive call has ı < |**k**| (from 𝔳_inst) and moves to ı + 1 + skip(ı) ≤ |**k**|, so
    the recursion makes at most |**k**| + 1 calls; `vBlob` supplies that much fuel
    (see `PVM.Program.vBlobAux_fuel` in `PVM.Theorems.Blob`). -/
def vBlobAux (V : CodeView) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if i > 0 && i == V.maskSize then true
    else if V.next i == V.maskSize && !isTerminator (V.zeta i) then false
    else if V.vInst i then V.vBlobAux fuel (V.next i)
    else false

/-- 𝔳_blob(**c**, **k**, 0) (GP §A.1). -/
def vBlob (V : CodeView) : Bool := V.vBlobAux (V.maskSize + 1) 0

/-- `n` is the opcode index of a valid instruction: **k**_n = 1 ∧ **c**_n ∈ U (GP §A.3). -/
def isInstrStart (V : CodeView) (n : Nat) : Bool :=
  decide (n < V.codeSize) && V.maskAt n && isValidOpcode (V.zeta n)

/-- `n` immediately follows a block terminator: ∃ m ∈ ℕ_{|c|}, **k**_m = 1 ∧ **c**_m ∈ T ∧
    m + 1 + skip(m) = n. Since skip(m) ≤ 24, the witness `m` lies in [n − 25, n − 1], so the
    search is over that window (see `PVM.Program.followsTerminator_iff`). -/
def followsTerminator (V : CodeView) (n : Nat) : Bool :=
  (List.range 25).any fun d =>
    decide (d + 1 ≤ n) &&
      (let m := n - 1 - d
       decide (m < V.codeSize) && V.maskAt m && isTerminator (V.zeta m) && V.next m == n)

/-- `n ∈ ϖ`, the basic-block starts (GP §A.3):
    ϖ ≡ ({0} ∪ {n + 1 + skip(n) | n ∈ ℕ_{|c|} ∧ **k**_n = 1 ∧ **c**_n ∈ T}) ∩ {n | **k**_n = 1 ∧ **c**_n ∈ U}. -/
def isBlockStart (V : CodeView) (n : Nat) : Bool :=
  (n == 0 || V.followsTerminator n) && V.isInstrStart n

/-- `b ∈ ϖ` for an integer jump target `b`; negative targets are never block starts. -/
def isBlockStartInt (V : CodeView) (b : Int) : Bool := if b < 0 then false else V.isBlockStart b.toNat

/-- Search downwards from `n` for the greatest block start `≤ n`; `0` if there is none. -/
def blockStartFrom (V : CodeView) : Nat → Nat
  | 0 => 0
  | n + 1 => if V.isBlockStart (n + 1) then n + 1 else V.blockStartFrom n

/-- 𝔏(ı) = max(j ∈ ϖ : j ≤ ı), the start of the basic block containing ı (GP §A.3).
    When ϖ has no element `≤ ı` (only possible for invalid programs, since 0 ∈ ϖ whenever
    𝔳_blob holds) we return 0. -/
def blockStartOf (V : CodeView) (i : Nat) : Nat := V.blockStartFrom i

/-- ζ_{start…+n}, the octets `start, …, start + n - 1` of ζ. -/
def zetaBytes (V : CodeView) (start n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (V.zeta (start + i))

/-- ℰ_n⁻¹(ζ_{start…+n}). -/
def zetaLE (V : CodeView) (start n : Nat) : Nat := Num.decodeLE (V.zetaBytes start n)

/-- 𝒳_n(ℰ_n⁻¹(ζ_{start…+n})), a sign-extended immediate. -/
def immAt (V : CodeView) (start n : Nat) : UInt64 := UInt64.ofNat (Num.sext n (V.zetaLE start n))

/-- ı + 𝒵_n(ℰ_n⁻¹(ζ_{start…+n})), an offset relative to the instruction at `i`. -/
def offsetAt (V : CodeView) (i start n : Nat) : Int := (i : Int) + Num.signed n (V.zetaLE start n)

/-- Decode the instruction at opcode index `ı` (GP §A.5), with ℓ = skip(ı). Returns `none`
    when ζ_ı ∉ U. -/
def decode (V : CodeView) (i : Nat) : Option Instr :=
  let op := V.zeta i
  let l := V.skip i
  let lo := regIdx (V.zeta (i + 1) % 16)          -- min(12, ζ_{ı+1} mod 16)
  let hi := regIdx (V.zeta (i + 1) / 16)          -- min(12, ⌊ζ_{ı+1} ÷ 16⌋)
  match formatOf? op with
  | none => none
  | some .noArgs => (NoArgsOp.ofOpcode? op).map .noArgs
  | some .oneImm =>
    -- l_X = min(4, ℓ), ν_X = 𝒳_{l_X}(ℰ⁻¹(ζ_{ı+1…+l_X}))
    let lX := min 4 l
    (OneImmOp.ofOpcode? op).map fun o => .oneImm o (V.immAt (i + 1) lX)
  | some .regExtImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), ν_X = ℰ_8⁻¹(ζ_{ı+2…+8})
    (RegExtImmOp.ofOpcode? op).map fun o => .regExtImm o lo (UInt64.ofNat (V.zetaLE (i + 2) 8))
  | some .twoImm =>
    -- l_X = min(4, ζ_{ı+1} mod 8), l_Y = min(4, max(0, ℓ − l_X − 1))
    let lX := min 4 (V.zeta (i + 1) % 8)
    let lY := min 4 (l - lX - 1)
    (TwoImmOp.ofOpcode? op).map fun o =>
      .twoImm o (V.immAt (i + 2) lX) (V.immAt (i + 2 + lX) lY)
  | some .oneOffset =>
    -- l_X = min(4, ℓ), ν_X = ı + 𝒵_{l_X}(ℰ⁻¹(ζ_{ı+1…+l_X}))
    let lX := min 4 l
    (OneOffsetOp.ofOpcode? op).map fun o => .oneOffset o (V.offsetAt i (i + 1) lX)
  | some .regImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), l_X = min(4, max(0, ℓ − 1))
    let lX := min 4 (l - 1)
    (RegImmOp.ofOpcode? op).map fun o => .regImm o lo (V.immAt (i + 2) lX)
  | some .regTwoImm =>
    -- l_X = min(4, ⌊ζ_{ı+1} ÷ 16⌋ mod 8), l_Y = min(4, max(0, ℓ − l_X − 1))
    let lX := min 4 (V.zeta (i + 1) / 16 % 8)
    let lY := min 4 (l - lX - 1)
    (RegTwoImmOp.ofOpcode? op).map fun o =>
      .regTwoImm o lo (V.immAt (i + 2) lX) (V.immAt (i + 2 + lX) lY)
  | some .regImmOffset =>
    -- as §A.5.7, but ν_Y = ı + 𝒵_{l_Y}(ℰ⁻¹(ζ_{ı+2+l_X…+l_Y}))
    let lX := min 4 (V.zeta (i + 1) / 16 % 8)
    let lY := min 4 (l - lX - 1)
    (RegImmOffsetOp.ofOpcode? op).map fun o =>
      .regImmOffset o lo (V.immAt (i + 2) lX) (V.offsetAt i (i + 2 + lX) lY)
  | some .twoReg =>
    -- r_D = min(12, ζ_{ı+1} mod 16), r_A = min(12, ⌊ζ_{ı+1} ÷ 16⌋)
    (TwoRegOp.ofOpcode? op).map fun o => .twoReg o lo hi
  | some .twoRegImm =>
    -- r_A = min(12, ζ_{ı+1} mod 16), r_B = min(12, ⌊ζ_{ı+1} ÷ 16⌋), l_X = min(4, max(0, ℓ − 1))
    let lX := min 4 (l - 1)
    (TwoRegImmOp.ofOpcode? op).map fun o => .twoRegImm o lo hi (V.immAt (i + 2) lX)
  | some .twoRegOffset =>
    let lX := min 4 (l - 1)
    (TwoRegOffsetOp.ofOpcode? op).map fun o => .twoRegOffset o lo hi (V.offsetAt i (i + 2) lX)
  | some .twoRegTwoImm =>
    -- l_X = min(4, ζ_{ı+2} mod 8), l_Y = min(4, max(0, ℓ − l_X − 2))
    let lX := min 4 (V.zeta (i + 2) % 8)
    let lY := min 4 (l - lX - 2)
    (TwoRegTwoImmOp.ofOpcode? op).map fun o =>
      .twoRegTwoImm o lo hi (V.immAt (i + 3) lX) (V.immAt (i + 3 + lX) lY)
  | some .threeReg =>
    -- r_A = min(12, ζ_{ı+1} mod 16), r_B = min(12, ⌊ζ_{ı+1} ÷ 16⌋), r_D = min(12, ζ_{ı+2})
    -- (the paper does not reduce ζ_{ı+2} mod 16 here; README, note 4)
    (ThreeRegOp.ofOpcode? op).map fun o => .threeReg o lo hi (regIdx (V.zeta (i + 2)))

/-- 𝔟(**c**, ı) (GP §A.10): 1 if ζ_{ı+1+skip(ı)} or ζ_{ı_target} is `unlikely` or `trap`, else 20. -/
def branchCost (V : CodeView) (i : Nat) (target : Int) : Nat :=
  let cheap (n : Nat) : Bool := n == unlikelyOpcode || n == trapOpcode
  if cheap (V.zeta (V.next i)) || cheap (V.zetaInt target) then 1 else 20

/-- Evaluate a cell of the cost table for the instruction `ins` at `ı`. -/
def evalCost (V : CodeView) (i : Nat) (ins : Instr) : CostExpr → Nat
  | .const n => n
  | .overlap a b => if ins.src.meets ins.dst then a else b
  | .overlapShift a b =>
    -- The paper writes ω_A = ω_D; the gas model has no register values, so we compare the
    -- register indices r_A = r_D (README, note 1).
    match ins.regsAD? with
    | some (ra, rd) => if ra = rd then a else b
    | none => b
  | .memory => memoryCost
  -- Only branches have a 𝔟 cell; the fallback target is never used.
  | .branch => V.branchCost i ((ins.branchTarget?).getD (-1))

/-- (č, ď, x̌) of the instruction at `ı` (GP §A.10), if ζ_ı ∈ U. -/
def instrCost? (V : CodeView) (i : Nat) : Option (Instr × InstrCost) := do
  let ins ← V.decode i
  let row ← costRow? (V.zeta i)
  let e := V.evalCost i ins
  return (ins, ⟨e row.cycles, e row.decodeSlots, ⟨e row.alu, e row.load, e row.store, e row.mul, e row.div⟩⟩)



namespace Sim

/-- 𝔛^mov (GP §A.9): `move_reg` is handled by the front end and renames registers. -/
def decodeMove (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) : SimState :=
  { x with
    pc := some (V.next i)
    decodeSlots := x.decodeSlots - 1
    rob := x.rob.map fun e =>
      { e with regs := if e.regs.meets ins.src then e.regs.union ins.dst else e.regs.diff ins.dst } }

/-- 𝔛^dec (GP §A.9): decode an instruction into a new reorder-buffer entry. -/
def decodeInstr (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  let deps := (x.rob.zipIdx.filter fun (e, _) => ins.src.meets e.regs).map (·.2)
  let rob := x.rob.map fun e => { e with regs := e.regs.diff ins.dst }
  { x with
    pc := if isTerminator (V.zeta i) then none else some (V.next i)
    decodeSlots := x.decodeSlots - cost.decodeSlots
    rob := rob ++ [⟨.dec, cost.cycles, deps, ins.dst, cost.units⟩] }

/-- 𝔛' (GP §A.9): `move_reg` (when ı < |**c**|) goes to 𝔛^mov, everything else to 𝔛^dec. -/
def decodeStep (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  if i < V.codeSize && V.zeta i == moveRegOpcode then decodeMove V x i ins
  else decodeInstr V x i ins cost


/-- One transition of 𝔛 (GP §A.9). `.inl x'` continues with x'; `.inr x` is the final state;
    `none` means ď(**x**_ı) is undefined because ζ at **x**_ı is not in U (impossible for the
    blocks of valid programs). The cases are tried in the paper's order: decode (𝔛') if
    **x**_ı ≠ ∅, ď(**x**_ı) ≤ **x**_d and l < 32; else start (𝔛'') if 𝔖(**x**) ≠ ∅ and **x**_e > 0;
    else stop if **x**_ı = ∅ and l = 0; else advance a cycle (𝔛'''). -/
def transition (V : CodeView) (x : SimState) : Option (SimState ⊕ SimState) := do
  let l := PVM.Sim.live x
  if let some i := x.pc then
    let (ins, c) ← V.instrCost? i
    if c.decodeSlots ≤ x.decodeSlots && l < 32 then
      return .inl (decodeStep V x i ins c)
  if let some n := PVM.Sim.readyToStart x then
    if x.startSlots > 0 then
      return .inl (PVM.Sim.startStep x n)
  if x.pc.isNone && l == 0 then
    return .inr x
  return .inl (PVM.Sim.cycleStep x)

/-- 𝔛 with at most `fuel` transitions; `none` if the fuel runs out or an invalid opcode is met. -/
def run (V : CodeView) : Nat → SimState → Option SimState
  | 0, _ => none
  | fuel + 1, x =>
    match transition V x with
    | some (.inl x') => run V fuel x'
    | some (.inr x') => some x'
    | none => none

/-- The fuel given to 𝔛: `256 · (|**c**| − ı + 2)` transitions, at least 256 per instruction of
    the block. Each instruction is decoded once and started once, and the longest single
    instruction (č = 60 for the divisions) keeps the pipeline busy for about 64 cycles, so the
    simulation should always finish well within this. **This bound is argued, not proved.**
    Over every block of the test vectors the simulation uses at most 54 transitions per
    instruction and under 5% of this fuel; `PVM.Program.blockCost?` returns `none` if the fuel
    is ever exhausted, and the gas checker reports it. -/
def fuel (V : CodeView) (i : Nat) : Nat := 256 * (V.codeSize - i + 2)


end Sim

/-- ϱ^Δ(**c**, **k**, ı) = max(**x**^final_c − 3, 1) (GP eq. `gascostforblock`); `none` if the
    simulation does not finish within its fuel or meets an opcode outside U. -/
def blockCost? (V : CodeView) (i : Nat) : Option Nat :=
  (Sim.run V (Sim.fuel V i) (Sim.init i)).map fun x => max (x.cycle - 3) 1

/-- ϱ^Δ as a total function: the simulated cost, or 1 in the cases where `blockCost?` has no
    value (which do not arise for the blocks of valid programs). -/
def blockCost (V : CodeView) (i : Nat) : Nat := (V.blockCost? i).getD 1

end CodeView

/-! ## The repeats agree with the model -/

namespace Program

variable (P : Program)

theorem zetaInt_view (i : Int) : P.zetaInt i = P.view.zetaInt i := rfl
theorem skip_view (i : Nat) : P.skip i = P.view.skip i := rfl
theorem next_view (i : Nat) : P.next i = P.view.next i := rfl
theorem vInst_view (i : Nat) : P.vInst i = P.view.vInst i := rfl
theorem vBlobAux_view : ∀ f i, P.vBlobAux f i = P.view.vBlobAux f i
  | 0, _ => by rw [Program.vBlobAux, CodeView.vBlobAux]
  | f + 1, i => by
    rw [Program.vBlobAux, CodeView.vBlobAux, vBlobAux_view f]
    rfl
theorem vBlob_view : P.vBlob = P.view.vBlob := vBlobAux_view P _ _
theorem isInstrStart_view (n : Nat) : P.isInstrStart n = P.view.isInstrStart n := rfl
theorem followsTerminator_view (n : Nat) : P.followsTerminator n = P.view.followsTerminator n := rfl
theorem isBlockStart_view (n : Nat) : P.isBlockStart n = P.view.isBlockStart n := rfl
theorem blockStartFrom_view : ∀ n, P.blockStartFrom n = P.view.blockStartFrom n
  | 0 => by rw [Program.blockStartFrom, CodeView.blockStartFrom]
  | n + 1 => by
    rw [Program.blockStartFrom, CodeView.blockStartFrom, blockStartFrom_view n]
    rfl
theorem blockStartOf_view (n : Nat) : P.blockStartOf n = P.view.blockStartOf n := blockStartFrom_view P n
theorem decode_view (i : Nat) : P.decode i = P.view.decode i := rfl
theorem instrCost?_view (i : Nat) : P.instrCost? i = P.view.instrCost? i := rfl
theorem transition_view (x : SimState) : Sim.transition P x = CodeView.Sim.transition P.view x := rfl
theorem run_view : ∀ f x, Sim.run P f x = CodeView.Sim.run P.view f x
  | 0, _ => by rw [Sim.run, CodeView.Sim.run]
  | f + 1, x => by
    rw [Sim.run, CodeView.Sim.run, transition_view]
    simp only [run_view f]
    generalize CodeView.Sim.transition P.view x = r
    rcases r with _ | _ | _ <;> rfl
theorem blockCost?_view (i : Nat) : P.blockCost? i = P.view.blockCost? i := by
  rw [Program.blockCost?, CodeView.blockCost?, run_view]
  rfl
theorem blockCost_view (i : Nat) : P.blockCost i = P.view.blockCost i := by
  rw [Program.blockCost, CodeView.blockCost, blockCost?_view]

end Program

end PVM
