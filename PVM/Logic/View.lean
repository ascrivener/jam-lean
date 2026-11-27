import PVM.Gas

/-!
# A program's code, seen through its reads

Everything $\Psi$ and the gas model compute from a program's code reads it only through $\zeta$ (the
instruction octets), $(\mathbf{k} \frown [1, 1, \dots])$, $\mathbf{k}$ with zeros beyond, $|\mathbf{c}|$ and $|\mathbf{k}|$. A
`CodeView` is exactly those reads, and this file repeats, over a `CodeView`, the definitions of
`PVM.Blob`, `PVM.Instr` and `PVM.Gas` that use them: skip, $\mathfrak{v}_{\text{inst}}$, $\mathfrak{v}_{\text{blob}}$, $\varpi$, decoding, and the
block cost $\varrho^\Delta$ with its simulation $\mathfrak{X}$. Each repeat is the model's definition with `P.zeta` read
as `V.zeta` and so on, and `Program.view` makes the two agree by `rfl` (the `*_view` theorems
below), so nothing here is a second reading of the paper.

The point is evaluation: a program parsed from a blob holds its code in a `ByteArray`, which
the kernel can only index by walking a list. A `CodeView` whose reads are arithmetic on a few
large numbers (`PVM.Logic.ChunkBlob`) lets the kernel decide facts about a 200 kB program.
-/

namespace PVM

/-- The reads of a program's code (GP §A.1–A.3): $\zeta$, $(\mathbf{k} \frown [1, 1, \dots])$, $\mathbf{k}$ with zeros beyond,
    $|\mathbf{c}|$ and $|\mathbf{k}|$. -/
structure CodeView where
  /-- $\zeta_i \equiv (\mathbf{c} \frown [0, 0, \dots])_i$. -/
  zeta : Nat → Nat
  /-- $(\mathbf{k} \frown [1, 1, \dots])_i$. -/
  maskExt : Nat → Bool
  /-- $\mathbf{k}_i$, 0 beyond $\mathbf{k}$. -/
  maskAt : Nat → Bool
  /-- $|\mathbf{c}|$. -/
  codeSize : Nat
  /-- $|\mathbf{k}|$. -/
  maskSize : Nat

/-- A program's reads. -/
def Program.view (P : Program) : CodeView := ⟨P.zeta, P.maskExt, P.maskAt, P.code.size, P.mask.size⟩

namespace CodeView

/-- $\zeta$ at an integer index, 0 at negative indices (as `Program.zetaInt`). -/
def zetaInt (V : CodeView) (i : Int) : Nat := if i < 0 then 0 else V.zeta i.toNat

/-- $\text{skip}(i) = \min(24, j \in \mathbb{N} : (\mathbf{k} \frown [1, 1, \dots])_{i+1+j} = 1)$ (GP eq. `skip`). -/
def skip (V : CodeView) (i : Nat) : Nat :=
  ((List.range 24).find? fun j => V.maskExt (i + 1 + j)).getD 24

/-- The index of the instruction following the one at `i`: $i + 1 + \text{skip}(i)$. -/
def next (V : CodeView) (i : Nat) : Nat := i + 1 + V.skip i

/-- $\mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath) = |\mathbf{k}| = |\mathbf{c}| \wedge \imath < |\mathbf{k}| \wedge \mathbf{k}_{\imath} = 1 \wedge \mathbf{c}_{\imath} \in U$ (GP §A.1). -/
def vInst (V : CodeView) (i : Nat) : Bool :=
  V.maskSize == V.codeSize && decide (i < V.maskSize) && V.maskAt i && isValidOpcode (V.zeta i)

/-- $\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, \imath)$ (GP §A.1), with explicit fuel.

    Every recursive call has $\imath < |\mathbf{k}|$ (from $\mathfrak{v}_{\text{inst}}$) and moves to $\imath + 1 + \text{skip}(\imath) \le |\mathbf{k}|$, so
    the recursion makes at most $|\mathbf{k}| + 1$ calls; `vBlob` supplies that much fuel
    (see `PVM.Program.vBlobAux_fuel` in `PVM.Theorems.Blob`). -/
def vBlobAux (V : CodeView) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if i > 0 && i == V.maskSize then true
    else if V.next i == V.maskSize && !isTerminator (V.zeta i) then false
    else if V.vInst i then V.vBlobAux fuel (V.next i)
    else false

/-- $\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, 0)$ (GP §A.1). -/
def vBlob (V : CodeView) : Bool := V.vBlobAux (V.maskSize + 1) 0

/-- `n` is the opcode index of a valid instruction: $\mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U$ (GP §A.3). -/
def isInstrStart (V : CodeView) (n : Nat) : Bool :=
  decide (n < V.codeSize) && V.maskAt n && isValidOpcode (V.zeta n)

/-- `n` immediately follows a block terminator: $\exists m \in \mathbb{N}_{|c|}, \mathbf{k}_m = 1 \wedge \mathbf{c}_m \in T \wedge$
    $m + 1 + \text{skip}(m) = n$. Since $\text{skip}(m) \le 24$, the witness `m` lies in $[n - 25, n - 1]$, so the
    search is over that window (see `PVM.Program.followsTerminator_iff`). -/
def followsTerminator (V : CodeView) (n : Nat) : Bool :=
  (List.range 25).any fun d =>
    decide (d + 1 ≤ n) &&
      (let m := n - 1 - d
       decide (m < V.codeSize) && V.maskAt m && isTerminator (V.zeta m) && V.next m == n)

/-- `n ∈ ϖ`, the basic-block starts (GP §A.3):
    $\varpi \equiv (\{0\} \cup \{n + 1 + \text{skip}(n) \mid n \in \mathbb{N}_{|c|} \wedge \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in T\}) \cap \{n \mid \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U\}$. -/
def isBlockStart (V : CodeView) (n : Nat) : Bool :=
  (n == 0 || V.followsTerminator n) && V.isInstrStart n

/-- `b ∈ ϖ` for an integer jump target `b`; negative targets are never block starts. -/
def isBlockStartInt (V : CodeView) (b : Int) : Bool := if b < 0 then false else V.isBlockStart b.toNat

/-- Search downwards from `n` for the greatest block start `≤ n`; `0` if there is none. -/
def blockStartFrom (V : CodeView) : Nat → Nat
  | 0 => 0
  | n + 1 => if V.isBlockStart (n + 1) then n + 1 else V.blockStartFrom n

/-- $\mathfrak{L}(\imath) = \max(j \in \varpi : j \le \imath)$, the start of the basic block containing $\imath$ (GP §A.3).
    When $\varpi$ has no element `≤ ı` (only possible for invalid programs, since $0 \in \varpi$ whenever
    $\mathfrak{v}_{\text{blob}}$ holds) we return 0. -/
def blockStartOf (V : CodeView) (i : Nat) : Nat := V.blockStartFrom i

/-- $\zeta_{\text{start} \dots + n}$, the octets `start, …, start + n - 1` of $\zeta$. -/
def zetaBytes (V : CodeView) (start n : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (V.zeta (start + i))

/-- $\mathcal{E}_n^{-1}(\zeta_{\text{start} \dots + n})$. -/
def zetaLE (V : CodeView) (start n : Nat) : Nat := Num.decodeLE (V.zetaBytes start n)

/-- $\mathcal{X}_n(\mathcal{E}_n^{-1}(\zeta_{\text{start} \dots + n}))$, a sign-extended immediate. -/
def immAt (V : CodeView) (start n : Nat) : UInt64 := UInt64.ofNat (Num.sext n (V.zetaLE start n))

/-- $\imath + \mathcal{Z}_n(\mathcal{E}_n^{-1}(\zeta_{\text{start} \dots + n}))$, an offset relative to the instruction at `i`. -/
def offsetAt (V : CodeView) (i start n : Nat) : Int := (i : Int) + Num.signed n (V.zetaLE start n)

/-- Decode the instruction at opcode index `ı` (GP §A.5), with $\ell = \text{skip}(\imath)$. Returns `none`
    when $\zeta_{\imath} \notin U$. -/
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
    -- r_A = min(12, ζ_{ı+1} mod 16), r_B = min(12, ⌊ζ_{ı+1} ÷ 16⌋),
    -- r_D = min(12, ζ_{ı+2} mod 16) (GP v0.8.1 §A.5.13, #554)
    (ThreeRegOp.ofOpcode? op).map fun o => .threeReg o lo hi (regIdx (V.zeta (i + 2) % 16))

/-- $\mathfrak{b}(\mathbf{c}, \imath)$ (GP §A.10): 1 if $\zeta_{\imath+1+\text{skip}(\imath)}$ or $\zeta_{\imath_{\text{target}}}$ is `unlikely` or `trap`, else 20. -/
def branchCost (V : CodeView) (i : Nat) (target : Int) : Nat :=
  let cheap (n : Nat) : Bool := n == unlikelyOpcode || n == trapOpcode
  if cheap (V.zeta (V.next i)) || cheap (V.zetaInt target) then 1 else 20

/-- Evaluate a cell of the cost table for the instruction `ins` at `ı`. -/
def evalCost (V : CodeView) (i : Nat) (ins : Instr) : CostExpr → Nat
  | .const n => n
  | .overlap a b => if ins.src.meets ins.dst then a else b
  | .overlapShift a b =>
    -- The paper writes ω_A = ω_D; the gas model has no register values, so we compare the
    -- register indices r_A = r_D (note 1 in docs/upstream-candidates.md#gray-paper-issues).
    match ins.regsAD? with
    | some (ra, rd) => if ra = rd then a else b
    | none => b
  | .memory => memoryCost
  -- Only branches have a 𝔟 cell; the fallback target is never used.
  | .branch => V.branchCost i ((ins.branchTarget?).getD (-1))

/-- $(\check{c}, \check{d}, \check{x})$ of the instruction at `ı` (GP §A.10), if $\zeta_{\imath} \in U$. -/
def instrCost? (V : CodeView) (i : Nat) : Option (Instr × InstrCost) := do
  let ins ← V.decode i
  let row ← costRow? (V.zeta i)
  let e := V.evalCost i ins
  return (ins, ⟨e row.cycles, e row.decodeSlots, ⟨e row.alu, e row.load, e row.store, e row.mul, e row.div⟩⟩)



namespace Sim

/-- $\mathfrak{X}^{\text{mov}}$ (GP §A.9): `move_reg` is handled by the front end and renames registers. -/
def decodeMove (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) : SimState :=
  { x with
    pc := some (V.next i)
    decodeSlots := x.decodeSlots - 1
    rob := x.rob.map fun e =>
      { e with regs := if e.regs.meets ins.src then e.regs.union ins.dst else e.regs.diff ins.dst } }

/-- $\mathfrak{X}^{\text{dec}}$ (GP §A.9): decode an instruction into a new reorder-buffer entry. -/
def decodeInstr (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  let deps := (x.rob.zipIdx.filter fun (e, _) => ins.src.meets e.regs).map (·.2)
  let rob := x.rob.map fun e => { e with regs := e.regs.diff ins.dst }
  { x with
    pc := if isTerminator (V.zeta i) then none else some (V.next i)
    decodeSlots := x.decodeSlots - cost.decodeSlots
    rob := rob ++ [⟨.dec, cost.cycles, deps, ins.dst, cost.units⟩] }

/-- $\mathfrak{X}'$ (GP §A.9): `move_reg` (when $\imath < |\mathbf{c}|$) goes to $\mathfrak{X}^{\text{mov}}$, everything else to $\mathfrak{X}^{\text{dec}}$. -/
def decodeStep (V : CodeView) (x : SimState) (i : Nat) (ins : Instr) (cost : InstrCost) : SimState :=
  if i < V.codeSize && V.zeta i == moveRegOpcode then decodeMove V x i ins
  else decodeInstr V x i ins cost


/-- One transition of $\mathfrak{X}$ (GP §A.9). `.inl x'` continues with x'; `.inr x` is the final state;
    `none` means $\check{d}(\mathbf{x}_{\imath})$ is undefined because $\zeta$ at $\mathbf{x}_{\imath}$ is not in $U$ (impossible for the
    blocks of valid programs). The cases are tried in the paper's order: decode ($\mathfrak{X}'$) if
    $\mathbf{x}_{\imath} \ne \emptyset$, $\check{d}(\mathbf{x}_{\imath}) \le \mathbf{x}_d$ and $l < 32$; else start ($\mathfrak{X}''$) if $\mathfrak{S}(\mathbf{x}) \ne \emptyset$ and $\mathbf{x}_e > 0$;
    else stop if $\mathbf{x}_{\imath} = \emptyset$ and $l = 0$; else advance a cycle ($\mathfrak{X}'''$). -/
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

/-- $\mathfrak{X}$ with at most `fuel` transitions; `none` if the fuel runs out or an invalid opcode is met. -/
def run (V : CodeView) : Nat → SimState → Option SimState
  | 0, _ => none
  | fuel + 1, x =>
    match transition V x with
    | some (.inl x') => run V fuel x'
    | some (.inr x') => some x'
    | none => none

/-- The fuel given to $\mathfrak{X}$: $256 \cdot (|\mathbf{c}| - \imath + 2)$ transitions, at least 256 per instruction of
    the block. Each instruction is decoded once and started once, and the longest single
    instruction ($\check{c} = 60$ for the divisions) keeps the pipeline busy for about 64 cycles, so the
    simulation should always finish well within this. **This bound is argued, not proved.**
    Over every block of the test vectors the simulation uses at most 54 transitions per
    instruction and under 5% of this fuel; `PVM.Program.blockCost?` returns `none` if the fuel
    is ever exhausted, and the gas checker reports it. -/
def fuel (V : CodeView) (i : Nat) : Nat := 256 * (V.codeSize - i + 2)


end Sim

/-- $\varrho^\Delta(\mathbf{c}, \mathbf{k}, \imath) = \max(\mathbf{x}^{\text{final}}_c - 3, 1)$ (GP eq. `gascostforblock`); `none` if the
    simulation does not finish within its fuel or meets an opcode outside $U$. -/
def blockCost? (V : CodeView) (i : Nat) : Option Nat :=
  (Sim.run V (Sim.fuel V i) (Sim.init i)).map fun x => max (x.cycle - 3) 1

/-- $\varrho^\Delta$ as a total function: the simulated cost, or 1 in the cases where `blockCost?` has no
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
