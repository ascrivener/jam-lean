import PVM.Basic
import PVM.Tables

/-!
# Program blobs, skip, ζ and basic blocks

GP v0.8.0 §A.1 (deblob, 𝔳_blob, 𝔳_inst), §A.2 (`sec:programdecoding`: skip, ζ) and
§A.3 (`sec:basicblocks`: U, T, ϖ, 𝔏).
-/

namespace PVM

/-- The components of a program blob (GP §A.1–A.2): the instruction data **c**, the opcode
    bitmask **k** and the dynamic jump table **j**. -/
structure Program where
  /-- **c**, the instruction data. -/
  code : ByteArray
  /-- **k**, the opcode bitmask. -/
  mask : Array Bool
  /-- **j**, the dynamic jump table. -/
  jumpTable : Array Nat

/-- `n ∈ U`, the set of valid opcodes (GP §A.3), read from the instruction tables. -/
def isValidOpcode (n : Nat) : Bool := (formatOf? n).isSome

/-- `n ∈ T`, the block-termination opcodes (GP §A.3). -/
def isTerminator (n : Nat) : Bool := terminatorOpcodes.contains n

namespace Program

/-- ζ_i ≡ (**c** ⌢ [0, 0, …])_i (GP eq. `instructions`). -/
def zeta (P : Program) (i : Nat) : Nat := P.code[i]?.map UInt8.toNat |>.getD 0

/-- ζ at an integer index. Negative indices are outside ζ; we read them as `0` like the
    indices past the end of **c** (only used by the branch cost 𝔟, see `PVM.Gas`). -/
def zetaInt (P : Program) (i : Int) : Nat := if i < 0 then 0 else P.zeta i.toNat

/-- (**k** ⌢ [1, 1, …])_i (GP eq. `skip`). -/
def maskExt (P : Program) (i : Nat) : Bool := P.mask.getD i true

/-- **k**_i, with indices outside **k** reading as 0. -/
def maskAt (P : Program) (i : Nat) : Bool := P.mask.getD i false

/-- skip(i) = min(24, j ∈ ℕ : (**k** ⌢ [1, 1, …])_{i+1+j} = 1) (GP eq. `skip`). -/
def skip (P : Program) (i : Nat) : Nat :=
  ((List.range 24).find? fun j => P.maskExt (i + 1 + j)).getD 24

/-- The index of the instruction following the one at `i`: i + 1 + skip(i). -/
def next (P : Program) (i : Nat) : Nat := i + 1 + P.skip i

/-- 𝔳_inst(**c**, **k**, ı) = |**k**| = |**c**| ∧ ı < |**k**| ∧ **k**_ı = 1 ∧ **c**_ı ∈ U (GP §A.1). -/
def vInst (P : Program) (i : Nat) : Bool :=
  P.mask.size == P.code.size && decide (i < P.mask.size) && P.maskAt i && isValidOpcode (P.zeta i)

/-- 𝔳_blob(**c**, **k**, ı) (GP §A.1), with explicit fuel.

    Every recursive call has ı < |**k**| (from 𝔳_inst) and moves to ı + 1 + skip(ı) ≤ |**k**|, so
    the recursion makes at most |**k**| + 1 calls; `vBlob` supplies that much fuel
    (see `PVM.Program.vBlobAux_fuel` in `PVM.Theorems.Blob`). -/
def vBlobAux (P : Program) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, i =>
    if i > 0 && i == P.mask.size then true
    else if P.next i == P.mask.size && !isTerminator (P.zeta i) then false
    else if P.vInst i then P.vBlobAux fuel (P.next i)
    else false

/-- 𝔳_blob(**c**, **k**, 0) (GP §A.1). -/
def vBlob (P : Program) : Bool := P.vBlobAux (P.mask.size + 1) 0

/-- `n` is the opcode index of a valid instruction: **k**_n = 1 ∧ **c**_n ∈ U (GP §A.3). -/
def isInstrStart (P : Program) (n : Nat) : Bool :=
  decide (n < P.code.size) && P.maskAt n && isValidOpcode (P.zeta n)

/-- `n` immediately follows a block terminator: ∃ m ∈ ℕ_{|c|}, **k**_m = 1 ∧ **c**_m ∈ T ∧
    m + 1 + skip(m) = n. Since skip(m) ≤ 24, the witness `m` lies in [n − 25, n − 1], so the
    search is over that window (see `PVM.Program.followsTerminator_iff`). -/
def followsTerminator (P : Program) (n : Nat) : Bool :=
  (List.range 25).any fun d =>
    decide (d + 1 ≤ n) &&
      (let m := n - 1 - d
       decide (m < P.code.size) && P.maskAt m && isTerminator (P.zeta m) && P.next m == n)

/-- `n ∈ ϖ`, the basic-block starts (GP §A.3):
    ϖ ≡ ({0} ∪ {n + 1 + skip(n) | n ∈ ℕ_{|c|} ∧ **k**_n = 1 ∧ **c**_n ∈ T}) ∩ {n | **k**_n = 1 ∧ **c**_n ∈ U}. -/
def isBlockStart (P : Program) (n : Nat) : Bool :=
  (n == 0 || P.followsTerminator n) && P.isInstrStart n

/-- `b ∈ ϖ` for an integer jump target `b`; negative targets are never block starts. -/
def isBlockStartInt (P : Program) (b : Int) : Bool := if b < 0 then false else P.isBlockStart b.toNat

/-- Search downwards from `n` for the greatest block start `≤ n`; `0` if there is none. -/
def blockStartFrom (P : Program) : Nat → Nat
  | 0 => 0
  | n + 1 => if P.isBlockStart (n + 1) then n + 1 else P.blockStartFrom n

/-- 𝔏(ı) = max(j ∈ ϖ : j ≤ ı), the start of the basic block containing ı (GP §A.3).
    When ϖ has no element `≤ ı` (only possible for invalid programs, since 0 ∈ ϖ whenever
    𝔳_blob holds) we return 0. -/
def blockStartOf (P : Program) (i : Nat) : Nat := P.blockStartFrom i

end Program

/-! ## Deblobbing (GP §A.1, using the codec of Appendix C) -/

namespace Blob

/-- ℰ, the general natural-number serialization (GP (C), "general natural number
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

/-- ℰ⁻¹ at offset `pos`: the unique `x` with ℰ(x) a prefix of `bs[pos, …)`, and the offset after
    it. Only canonical encodings are accepted, since the paper requires `bs` to *be* ℰ(x). -/
def decodeNat? (bs : ByteArray) (pos : Nat) : Option (Nat × Nat) := do
  let b ← bs[pos]?
  let l := leadingOnes b
  let x ←
    if l = 8 then (Num.decodeLE ·) <$> slice? bs (pos + 1) 8
    else (fun rest => (b.toNat - (2 ^ 8 - 2 ^ (8 - l))) * 2 ^ (8 * l) + Num.decodeLE rest) <$>
      slice? bs (pos + 1) l
  let enc ← slice? bs pos (1 + (if l = 8 then 8 else l))
  if encodeNat x == enc then some (x, pos + 1 + (if l = 8 then 8 else l)) else none

/-- ℰ⁻¹ of a bit sequence of length `n` packed least-significant bit first (GP (C), "Bit
    Sequence Encoding"); the octets must be exactly ⌈n/8⌉ long with zero padding bits. -/
def decodeBits? (bs : List UInt8) (n : Nat) : Option (Array Bool) :=
  if bs.length ≠ (n + 7) / 8 then none
  else
    let bits := (List.range (8 * bs.length)).map fun i => Num.bit (bs.getD (i / 8) 0).toNat (i % 8)
    if (bits.drop n).all (· == false) then some (bits.take n).toArray else none

/-- The unique (**c**, **k**, **j**) with
    p = ℰ(|**j**|) ⌢ ℰ_1(z) ⌢ ℰ(|**c**|) ⌢ ℰ_z(**j**) ⌢ ℰ(**c**) ⌢ ℰ(**k**) and |**k**| = |**c**|
    (GP §A.1, the encoding condition of deblob). -/
def parse? (p : ByteArray) : Option Program := do
  let (jLen, pos) ← decodeNat? p 0
  let z ← p[pos]?.map UInt8.toNat
  let pos := pos + 1
  let (cLen, pos) ← decodeNat? p pos
  if p.size < pos + jLen * z then none
  let j := (List.range jLen).map fun i => Num.decodeLE ((p.extract (pos + i * z) (pos + i * z + z)).toList)
  let pos := pos + jLen * z
  let c ← slice? p pos cLen
  let pos := pos + cLen
  let k ← decodeBits? (p.extract pos p.size).toList cLen
  some { code := ⟨c.toArray⟩, mask := k, jumpTable := j.toArray }

end Blob

/-- deblob(p, ı) (GP §A.1): the program (**c**, **k**, **j**) if p is a valid encoding,
    𝔳_blob(**c**, **k**, 0) and 𝔳_inst(**c**, **k**, ı); otherwise ∇ (`none`). -/
def deblob (p : ByteArray) (i : Nat) : Option Program := do
  let P ← Blob.parse? p
  if P.vBlob && P.vInst i then some P else none

end PVM
