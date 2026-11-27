import PVM.Invocation
import PVM.Logic.Bits

/-!
# Fast blob parsing, proved equal to the paper's

`Blob.parse?` (GP v0.8.1 eq. `deblob`) follows the paper literally. It copies $\mathbf{c}$ through a list,
and it decodes the opcode bitmask $\mathbf{k}$ (`Blob.decodeBits?`) through a list of all
$8\lceil |\mathbf{c}|/8 \rceil$ bits,
each computed with a big-number power. That is most of the cost of preparing a service blob.

`Blob.parseFast` takes $\mathbf{c}$ as a slice of the blob and decodes $\mathbf{k}$ straight from its octets
(`Blob.bitsFast`). `parse?_eq_parseFast` is registered with `@[csimp]`: compiled code that imports
this module, among it `psiFaster` and `psiHStarFaster`, uses `parseFast`.

Likewise `JamBlob.parseFast` slices the sections of a standard program blob (GP v0.8.1
eq. `jamblobformat`) instead of copying them through lists (`JamBlob.parse?_eq_parseFast`), and
`JamBlob.parseStd?`, `validJamBlob?` and Y (`standardInit`) are restated word for word so that
their compiled code uses it (each equality `rfl`, registered with `@[csimp]`; `psiMFast` calls
`standardInit`).
-/

namespace PVM

private theorem byteArray_toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  suffices h : ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i by
    simpa [ByteArray.toList] using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop, ite_eq_left h, ih]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.reverse_cons, List.append_assoc, List.drop_eq_getElem_cons hi]
    rw [List.singleton_append]
    have hb : bs.get! i = bs.data.toList[i] := by
      show bs.data[i]! = bs.data.toList[i]
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rw [hb]
  | case2 i r h =>
    rw [ByteArray.toList.loop, ite_eq_right h]
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.drop_eq_nil_of_le this]

theorem byteArray_mk_toList (bs : ByteArray) : (⟨bs.toList.toArray⟩ : ByteArray) = bs := by
  rw [byteArray_toList_eq_data, Array.toArray_toList]

namespace Blob

/-- Bit `i` (least significant first) of the octets of `p` from offset `s`. -/
@[inline] def bitAt (p : ByteArray) (s i : Nat) : Bool := p[s + i / 8]!.toNat.testBit (i % 8)

/-- `decodeBits? (p.extract s p.size).toList n`, read from `p` directly: the length check, the
    (at most 7) padding bits, and the n bits. -/
def bitsFast (p : ByteArray) (s n : Nat) : Option (Array Bool) :=
  let L := p.size - s
  if L ≠ (n + 7) / 8 then none
  else if (List.range (8 * L - n)).all (fun d => bitAt p s (n + d) == false) then
    some (Array.ofFn (n := n) fun i => bitAt p s i.val)
  else none

theorem drop_map_range' {α : Type} (f : Nat → α) (N n : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun k => f (n + k) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp

theorem take_map_range' {α : Type} (f : Nat → α) (N n : Nat) (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp

theorem decodeBits?_eq_bitsFast (p : ByteArray) (s n : Nat) :
    decodeBits? (p.extract s p.size).toList n = bitsFast p s n := by
  have hlen : (p.extract s p.size).toList.length = p.size - s := by
    rw [byteArray_toList_eq_data, Array.length_toList]
    simp [ByteArray.size_extract]
  unfold decodeBits? bitsFast
  rw [hlen]
  simp only
  by_cases hL : p.size - s = (n + 7) / 8
  · rw [if_neg (Decidable.not_not.mpr hL), if_neg (Decidable.not_not.mpr hL)]
    have hg : ∀ i, i < 8 * (p.size - s) →
        Num.bit ((p.extract s p.size).toList.toArray.getD (i / 8) 0).toNat (i % 8) = bitAt p s i := by
      intro i hi
      have hlt : i / 8 < (p.extract s p.size).size := by
        simp only [ByteArray.size_extract, Nat.min_self]; omega
      rw [byteArray_toList_eq_data, Array.toArray_toList, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem (by exact hlt), Option.getD_some,
        Num.bit_eq_testBit]
      unfold bitAt
      have h2 : s + i / 8 < p.size := by
        simp only [ByteArray.size_extract, Nat.min_self] at hlt; omega
      rw [getElem!_pos p _ h2]
      have := ByteArray.getElem_extract (b := p) (start := s) (stop := p.size) (i := i / 8) hlt
      rw [← this]; rfl
    have hmap : ((List.range (8 * (p.size - s))).map fun i =>
        Num.bit ((p.extract s p.size).toList.toArray.getD (i / 8) 0).toNat (i % 8)) =
        (List.range (8 * (p.size - s))).map fun i => bitAt p s i := by
      apply List.map_congr_left
      intro i hi
      exact hg i (List.mem_range.1 hi)
    rw [hmap, drop_map_range', take_map_range' _ _ _ (by omega)]
    have hall : (((List.range (8 * (p.size - s) - n)).map fun k => bitAt p s (n + k)).all
        (· == false)) = (List.range (8 * (p.size - s) - n)).all (fun d => bitAt p s (n + d) == false) := by
      simp [List.all_map, Function.comp_def]
    rw [hall]
    split
    · congr 1
      apply Array.ext
      · simp
      · intro i h1 h2
        simp
    · rfl
  · rw [if_pos hL, if_pos hL]

/-- The tail of `parse?`: $\mathbf{c}$ and $\mathbf{k}$. -/
def parseTail (p : ByteArray) (pos cLen : Nat) (j : Array Nat) : Option Program :=
  if pos + cLen ≤ p.size then
    match bitsFast p (pos + cLen) cLen with
    | some k => some { code := p.extract pos (pos + cLen), mask := k, jumpTable := j }
    | none => none
  else none

theorem parseTail_eq (p : ByteArray) (pos cLen : Nat) (j : Array Nat) :
    (do
      let c ← slice? p pos cLen
      let k ← decodeBits? (p.extract (pos + cLen) p.size).toList cLen
      some ({ code := ⟨c.toArray⟩, mask := k, jumpTable := j } : Program)) =
    parseTail p pos cLen j := by
  unfold parseTail slice?
  split
  · simp only [Option.bind_some, decodeBits?_eq_bitsFast, Option.bind_eq_bind]
    cases bitsFast p (pos + cLen) cLen <;> simp [byteArray_mk_toList]
  · rfl

/-- `parse?` with $\mathbf{c}$ sliced and $\mathbf{k}$ decoded from the octets. -/
def parseFast (p : ByteArray) : Option Program := do
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
  parseTail p pos cLen j.toArray

/-- **The fast blob parse is the paper's.** -/
@[csimp] theorem parse?_eq_parseFast : @parse? = @parseFast := by
  funext p
  unfold parse? parseFast
  simp only [parseTail_eq]

/-- `slice?` as a `ByteArray`. -/
@[inline] def sliceBA? (b : ByteArray) (pos n : Nat) : Option ByteArray :=
  if pos + n ≤ b.size then some (b.extract pos (pos + n)) else none

theorem slice?_eq (b : ByteArray) (pos n : Nat) :
    slice? b pos n = (sliceBA? b pos n).map ByteArray.toList := by
  unfold slice? sliceBA?; split <;> rfl

end Blob

/-- `JamBlob.parse?` with the sections sliced rather than copied through lists. -/
def JamBlob.parseFast (b : ByteArray) : Option JamBlob := do
  let fixed (pos n : Nat) : Option Nat := (Num.decodeLE ·) <$> Blob.slice? b pos n
  let oLen ← fixed 0 3
  let wLen ← fixed 3 3
  let z ← fixed 6 2
  let s ← fixed 8 3
  let pos := 11
  let o ← Blob.sliceBA? b pos oLen
  let pos := pos + oLen
  let w ← Blob.sliceBA? b pos wLen
  let pos := pos + wLen
  let pLen ← fixed pos 4
  let pos := pos + 4
  if pos + pLen ≠ b.size then none
  let p ← Blob.sliceBA? b pos pLen
  some ⟨o, w, z, s, p⟩

/-- **The fast standard-blob parse is the paper's.** -/
@[csimp] theorem JamBlob.parse?_eq_parseFast : @JamBlob.parse? = @JamBlob.parseFast := by
  funext b
  unfold JamBlob.parse? JamBlob.parseFast
  simp [Blob.slice?_eq, Option.bind_map, Function.comp_def, byteArray_mk_toList]

/-- `JamBlob.parseStd?`, restated so that its compiled code uses `JamBlob.parseFast`. -/
def JamBlob.parseStdFast (b : ByteArray) : Option JamBlob := (skipMetadata? b).bind JamBlob.parse?

@[csimp] theorem JamBlob.parseStd?_eq_parseStdFast : @JamBlob.parseStd? = @JamBlob.parseStdFast := rfl

/-- `validJamBlob?`, restated so that its compiled code uses `JamBlob.parseStdFast`. -/
def validJamBlobFast (b : ByteArray) (a : ByteArray) : Option JamBlob :=
  if a.size > inputSize then none
  else (JamBlob.parseStd? b).bind fun jb =>
    if 5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32 then none
    else some jb

@[csimp] theorem validJamBlob?_eq_validJamBlobFast : @validJamBlob? = @validJamBlobFast := rfl

/-- Y (`standardInit`), restated so that its compiled code uses `validJamBlobFast`. -/
def standardInitFast (b : ByteArray) (a : ByteArray) : Option (ByteArray × Regs × Memory) :=
  (validJamBlob? b a).map fun jb => (jb.code, initialRegs a, initialMemory jb a)

@[csimp] theorem standardInit_eq_standardInitFast : @standardInit = @standardInitFast := rfl

end PVM
