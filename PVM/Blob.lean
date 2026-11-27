import PVM.Basic
import PVM.Tables

/-!
# Program blobs, skip, $\zeta$ and basic blocks

GP v0.8.1 §A.1 (deblob, eq. `deblob`; $\mathfrak{v}_{\text{blob}}$, $\mathfrak{v}_{\text{inst}}$), §A.2 (`sec:programdecoding`: skip, $\zeta$) and
§A.3 (`sec:basicblocks`: $U$, $T$, $\varpi$, $\mathfrak{L}$).
-/

namespace PVM

/-- The components of a program blob (GP §A.1–A.2): the instruction data $\mathbf{c}$, the opcode
    bitmask $\mathbf{k}$ and the dynamic jump table $\mathbf{j}$. -/
structure Program where
  /-- $\mathbf{c}$, the instruction data. -/
  code : ByteArray
  /-- $\mathbf{k}$, the opcode bitmask. -/
  mask : Array Bool
  /-- $\mathbf{j}$, the dynamic jump table. -/
  jumpTable : Array Nat

/-- `n ∈ U`, the set of valid opcodes (GP §A.3), read from the instruction tables. -/
def isValidOpcode (n : Nat) : Bool := (formatOf? n).isSome

/-- `n ∈ T`, the block-termination opcodes (GP §A.3). -/
def isTerminator (n : Nat) : Bool := terminatorOpcodes.contains n

namespace Program

/-- $\zeta_i \equiv (\mathbf{c} \frown [0, 0, \dots])_i$ (GP eq. `instructions`). -/
def zeta (P : Program) (i : Nat) : Nat := P.code[i]?.map UInt8.toNat |>.getD 0

/-- $\zeta$ at an integer index. Negative indices are outside $\zeta$; we read them as `0` like the
    indices past the end of $\mathbf{c}$ (only used by the branch cost $\mathfrak{b}$, see `PVM.Gas`). -/
def zetaInt (P : Program) (i : Int) : Nat := if i < 0 then 0 else P.zeta i.toNat

/-- $(\mathbf{k} \frown [1, 1, \dots])_i$ (GP eq. `skip`). -/
def maskExt (P : Program) (i : Nat) : Bool := P.mask.getD i true

/-- $\mathbf{k}_i$, with indices outside $\mathbf{k}$ reading as 0. -/
def maskAt (P : Program) (i : Nat) : Bool := P.mask.getD i false

/-- $\text{skip}(i) = \min(24, j \in \mathbb{N} : (\mathbf{k} \frown [1, 1, \dots])_{i+1+j} = 1)$ (GP eq. `skip`). -/
def skip (P : Program) (i : Nat) : Nat :=
  ((List.range 24).find? fun j => P.maskExt (i + 1 + j)).getD 24

/-- The index of the instruction following the one at `i`: $i + 1 + \text{skip}(i)$. -/
def next (P : Program) (i : Nat) : Nat := i + 1 + P.skip i

/-- $\mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath) = |\mathbf{k}| = |\mathbf{c}| \wedge \imath < |\mathbf{k}| \wedge \mathbf{k}_{\imath} = 1 \wedge \mathbf{c}_{\imath} \in U$ (GP §A.1). -/
def vInst (P : Program) (i : Nat) : Bool :=
  P.mask.size == P.code.size && decide (i < P.mask.size) && P.maskAt i && isValidOpcode (P.zeta i)

/-- $\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, \imath)$ (GP §A.1), with explicit fuel.

    Every recursive call has $\imath < |\mathbf{k}|$ (from $\mathfrak{v}_{\text{inst}}$) and moves to $\imath + 1 + \text{skip}(\imath) \le |\mathbf{k}|$, so
    the recursion makes at most $|\mathbf{k}| + 1$ calls; `vBlob` supplies that much fuel
    (see `PVM.Program.vBlobAux_fuel` in `PVM.Theorems.Blob`). -/
def vBlobAux (P : Program) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if i > 0 && i == P.mask.size then true
    else if P.next i == P.mask.size && !isTerminator (P.zeta i) then false
    else if P.vInst i then P.vBlobAux fuel (P.next i)
    else false

/-- $\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, 0)$ (GP §A.1). -/
def vBlob (P : Program) : Bool := P.vBlobAux (P.mask.size + 1) 0

/-- `n` is the opcode index of a valid instruction: $\mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U$ (GP §A.3). -/
def isInstrStart (P : Program) (n : Nat) : Bool :=
  decide (n < P.code.size) && P.maskAt n && isValidOpcode (P.zeta n)

/-- `n` immediately follows a block terminator: $\exists m \in \mathbb{N}_{|c|}, \mathbf{k}_m = 1 \wedge \mathbf{c}_m \in T \wedge$
    $m + 1 + \text{skip}(m) = n$. Since $\text{skip}(m) \le 24$, the witness `m` lies in $[n - 25, n - 1]$, so the
    search is over that window (see `PVM.Program.followsTerminator_iff`). -/
def followsTerminator (P : Program) (n : Nat) : Bool :=
  (List.range 25).any fun d =>
    decide (d + 1 ≤ n) &&
      (let m := n - 1 - d
       decide (m < P.code.size) && P.maskAt m && isTerminator (P.zeta m) && P.next m == n)

/-- `n ∈ ϖ`, the basic-block starts (GP §A.3):
    $\varpi \equiv (\{0\} \cup \{n + 1 + \text{skip}(n) \mid n \in \mathbb{N}_{|c|} \wedge \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in T\}) \cap \{n \mid \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U\}$. -/
def isBlockStart (P : Program) (n : Nat) : Bool :=
  (n == 0 || P.followsTerminator n) && P.isInstrStart n

/-- `b ∈ ϖ` for an integer jump target `b`; negative targets are never block starts. -/
def isBlockStartInt (P : Program) (b : Int) : Bool := if b < 0 then false else P.isBlockStart b.toNat

/-- Search downwards from `n` for the greatest block start `≤ n`; `0` if there is none. -/
def blockStartFrom (P : Program) : Nat → Nat
  | 0 => 0
  | n + 1 => if P.isBlockStart (n + 1) then n + 1 else P.blockStartFrom n

/-- $\mathfrak{L}(\imath) = \max(j \in \varpi : j \le \imath)$, the start of the basic block containing $\imath$ (GP §A.3).
    When $\varpi$ has no element `≤ ı` (only possible for invalid programs, since $0 \in \varpi$ whenever
    $\mathfrak{v}_{\text{blob}}$ holds) we return 0. -/
def blockStartOf (P : Program) (i : Nat) : Nat := P.blockStartFrom i

end Program

/-! ## Deblobbing (GP §A.1, using the codec of Appendix C) -/

namespace Blob

/-- $\mathsf{Z}_C = 2^{25}$, the maximum size of the instruction data $\mathbf{c}$ of a program blob (GP v0.8.1
    definitions, eq. `deblob`; #559). -/
def maxCodeSize : Nat := 2 ^ 25

/-- $\mathsf{Z}_J = 2^{24}$, the maximum number of entries of the dynamic jump table $\mathbf{j}$ (GP v0.8.1
    definitions, eq. `deblob`; #559). -/
def maxJumpTableEntries : Nat := 2 ^ 24

/-- $\mathcal{E}$, the general natural-number serialization (GP (C), "general natural number
    serialization"). -/
def encodeNat (x : Nat) : List UInt8 :=
  if x = 0 then [0]
  else match (List.range 8).find? (fun l => 2 ^ (7 * l) ≤ x && x < 2 ^ (7 * (l + 1))) with
    | some l => UInt8.ofNat (2 ^ 8 - 2 ^ (8 - l) + x / 2 ^ (8 * l)) :: Num.encodeLE l (x % 2 ^ (8 * l))
    | none => 255 :: Num.encodeLE 8 x

/-- `bs[pos, pos + n)`, if in bounds. -/
def slice? (bs : ByteArray) (pos n : Nat) : Option (List UInt8) :=
  if pos + n ≤ bs.size then some ((bs.extract pos (pos + n)).toList) else none

/-- Number of leading one bits of an octet. -/
def leadingOnes (b : UInt8) : Nat :=
  ((List.range 8).find? fun i => !Num.bit b.toNat (7 - i)).getD 8

/-- $\mathcal{E}^{-1}$ at offset `pos`: the unique `x` with $\mathcal{E}(x)$ a prefix of `bs[pos, …)`, and the offset after
    it. Only canonical encodings are accepted, since the paper requires `bs` to *be* $\mathcal{E}(x)$. -/
def decodeNat? (bs : ByteArray) (pos : Nat) : Option (Nat × Nat) := do
  let b ← bs[pos]?
  let l := leadingOnes b
  let x ←
    if l = 8 then (Num.decodeLE ·) <$> slice? bs (pos + 1) 8
    else (fun rest => (b.toNat - (2 ^ 8 - 2 ^ (8 - l))) * 2 ^ (8 * l) + Num.decodeLE rest) <$>
      slice? bs (pos + 1) l
  let enc ← slice? bs pos (1 + (if l = 8 then 8 else l))
  if encodeNat x == enc then some (x, pos + 1 + (if l = 8 then 8 else l)) else none

/-- $\mathcal{E}^{-1}$ of a bit sequence of length `n` packed least-significant bit first (GP (C), "Bit
    Sequence Encoding"); the octets must be exactly $\lceil n/8 \rceil$ long with zero padding bits. -/
def decodeBits? (bs : List UInt8) (n : Nat) : Option (Array Bool) :=
  if bs.length ≠ (n + 7) / 8 then none
  else
    let ba := bs.toArray
    let bits := (List.range (8 * bs.length)).map fun i => Num.bit (ba.getD (i / 8) 0).toNat (i % 8)
    if (bits.drop n).all (· == false) then some (bits.take n).toArray else none

/-- The unique $(\mathbf{c}, \mathbf{k}, \mathbf{j}) \in (\mathbb{B}_{:\mathsf{Z}_C}, \mathbb{b}, [\![ \mathbb{N}_R ]\!]_{:\mathsf{Z}_J})$ with
    $p = \mathcal{E}(|\mathbf{j}|) \frown \mathcal{E}_1(z) \frown \mathcal{E}(|\mathbf{c}|) \frown \mathcal{E}_z(\mathbf{j}) \frown \mathcal{E}(\mathbf{c}) \frown \mathcal{E}(\mathbf{k})$, $z \le 4$ and
    $|\mathbf{k}| = |\mathbf{c}|$ (GP v0.8.1 eq. `deblob`, the encoding condition; the bounds on $|\mathbf{c}|$, $|\mathbf{j}|$
    and $z$ are new in v0.8.1, #559). -/
def parse? (p : ByteArray) : Option Program := do
  let (jLen, pos) ← decodeNat? p 0
  if jLen > maxJumpTableEntries then none
  let z ← p[pos]?.map UInt8.toNat
  if z > 4 then none
  let pos := pos + 1
  let (cLen, pos) ← decodeNat? p pos
  if cLen > maxCodeSize then none
  if p.size < pos + jLen * z then none
  let j := (List.range jLen).map fun i => Num.decodeLE ((p.extract (pos + i * z) (pos + i * z + z)).toList)
  let pos := pos + jLen * z
  let c ← slice? p pos cLen
  let pos := pos + cLen
  let k ← decodeBits? (p.extract pos p.size).toList cLen
  some { code := ⟨c.toArray⟩, mask := k, jumpTable := j.toArray }

end Blob

/-- $\text{deblob}(p, \imath)$ (GP v0.8.1 eq. `deblob`): the program $(\mathbf{c}, \mathbf{k}, \mathbf{j})$ if $p$ is a valid encoding,
    $\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, 0)$ and $\mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath)$; otherwise $\nabla$ (`none`). -/
def deblob (p : ByteArray) (i : Nat) : Option Program := do
  let P ← Blob.parse? p
  if P.vBlob && P.vInst i then some P else none

end PVM
