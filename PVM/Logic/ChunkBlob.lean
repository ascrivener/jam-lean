import PVM.Logic.View
import PVM.Invocation

/-!
# Blobs the kernel can read

A `ByteArray` holds its octets in a list, so the kernel can only reach octet j by walking j cells,
and a 200 kB blob is out of its reach. Here a blob is instead the base-256 digits of one number
N, least significant first: octet j is ⌊N / 2^(8j)⌋ mod 256 (`NatBlob.byte`), which the kernel
computes with its arbitrary-precision arithmetic. A check that reads a stretch of the blob can
cut that stretch out of N once and read it from the small number (`NatBlob.byte_window`).

`NatBlob.ba N o n` is the `ByteArray` of the n octets from octet o, and the lemmas below read the
model's parsers on such arrays without evaluating them: an octet (`getElem?_ba`), a slice
(`slice?_ba`, `extract_ba`), the opcode bitmask (`decodeBits?_bytes`). `parse?_ba` and
`jamParse?_ba` put them together: a blob whose header facts the kernel decides on a handful of
octets parses to sections at known offsets, and its program's `CodeView` is `NatBlob.view`,
arithmetic on N (`view_eq`).
-/

/-- `ByteArray.toList` lists the underlying array. -/
theorem ByteArray.toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
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

namespace PVM

namespace NatBlob

/-- Octet j of the blob whose octets are the base-256 digits of N, least significant first. -/
def byte (N j : Nat) : Nat := (N >>> (8 * j)) % 256

/-- Bit b of that blob, each octet read least significant bit first. -/
def bit (N b : Nat) : Bool := N.testBit b

/-- Reading octet j from the stretch of the blob from octet a. -/
theorem byte_window (N a w j : Nat) (h1 : a ≤ j) (h2 : j < a + w) :
    byte N j = byte ((N >>> (8 * a)) % 2 ^ (8 * w)) (j - a) := by
  simp only [byte]
  apply Nat.eq_of_testBit_eq
  intro k
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  rw [h256, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hk : k < 8
  · have e1 : 8 * (j - a) + k < 8 * w := by omega
    have e2 : 8 * a + (8 * (j - a) + k) = 8 * j + k := by omega
    simp only [hk, e1, e2, decide_true, Bool.true_and]
  · simp only [hk, decide_false, Bool.false_and]

/-- Reading bit b from the stretch of the blob from bit s. -/
theorem bit_window (N s w b : Nat) (h1 : s ≤ b) (h2 : b < s + w) :
    bit N b = bit ((N >>> s) % 2 ^ w) (b - s) := by
  simp only [bit, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  rw [show s + (b - s) = b by omega]
  simp [show b - s < w by omega]

theorem byte_lt (N j : Nat) : byte N j < 256 := Nat.mod_lt _ (by decide)

/-- Bit k of octet j is bit 8j + k. -/
theorem bit_eq (N j k : Nat) (hk : k < 8) : bit N (8 * j + k) = (byte N j).testBit k := by
  simp only [bit, byte]
  have : (256 : Nat) = 2 ^ 8 := rfl
  rw [this, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hk]

/-- The n octets from octet o. -/
def bytes (N : Nat) (o n : Nat) : List UInt8 :=
  (List.range n).map fun j => UInt8.ofNat (byte N (o + j))

/-- The n octets from octet o, as a `ByteArray`. -/
def ba (N : Nat) (o n : Nat) : ByteArray := ⟨(bytes N o n).toArray⟩

@[simp] theorem length_bytes (N : Nat) (o n : Nat) : (bytes N o n).length = n := by
  simp [bytes]

@[simp] theorem size_ba (N : Nat) (o n : Nat) : (ba N o n).size = n := by
  simp [ba, ByteArray.size]

theorem getElem_bytes (N : Nat) (o n j : Nat) (h : j < (bytes N o n).length) :
    (bytes N o n)[j] = UInt8.ofNat (byte N (o + j)) := by
  simp [bytes]

theorem getElem?_bytes (N : Nat) (o n j : Nat) :
    (bytes N o n)[j]? = if j < n then some (UInt8.ofNat (byte N (o + j))) else none := by
  split
  · rw [List.getElem?_eq_getElem (by simpa), getElem_bytes]
  · rw [List.getElem?_eq_none (by simp; omega)]

theorem getElem!_bytes (N o n k : Nat) :
    (bytes N o n)[k]! = if k < n then UInt8.ofNat (byte N (o + k)) else default := by
  rw [List.getElem!_eq_getElem?_getD, getElem?_bytes]
  split <;> rfl

theorem toNat_byte (N : Nat) (j : Nat) : (UInt8.ofNat (byte N j)).toNat = byte N j := by
  simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (byte_lt N j)]

/-- A `ByteArray` of a list reads as the list. -/
theorem getElem?_mk (l : List UInt8) (i : Nat) : (⟨l.toArray⟩ : ByteArray)[i]? = l[i]? := by
  by_cases h : i < l.length
  · rw [getElem?_pos (⟨l.toArray⟩ : ByteArray) i (by simpa [ByteArray.size] using h),
      List.getElem?_eq_getElem h]
    rfl
  · rw [getElem?_neg (⟨l.toArray⟩ : ByteArray) i (by simpa [ByteArray.size] using h),
      List.getElem?_eq_none (by omega)]

theorem getElem?_ba (N : Nat) (o n j : Nat) :
    (ba N o n)[j]? = if j < n then some (UInt8.ofNat (byte N (o + j))) else none := by
  rw [ba, getElem?_mk, getElem?_bytes]

theorem toList_ba (N : Nat) (o n : Nat) : (ba N o n).toList = bytes N o n := by
  rw [ByteArray.toList_eq_data]; rfl

/-- A slice of the octets from o is the octets from o + a. -/
theorem extract_bytes (N : Nat) (o n a b : Nat) :
    (bytes N o n).extract a b = bytes N (o + a) (min b n - a) := by
  apply List.ext_getElem
  · simp [List.extract_eq_take_drop]; omega
  · intro k h1 h2
    simp only [List.extract_eq_take_drop, List.getElem_take, List.getElem_drop, getElem_bytes]
    rw [Nat.add_assoc]

theorem extract_ba (N : Nat) (o n a b : Nat) :
    (ba N o n).extract a b = ba N (o + a) (min b n - a) := by
  have h : ((ba N o n).extract a b).data = (ba N (o + a) (min b n - a)).data := by
    rw [ByteArray.data_extract]
    apply Array.ext'
    simp only [ba, Array.toList_extract, extract_bytes]
  cases h1 : (ba N o n).extract a b
  rw [h1] at h
  simp only at h
  rw [h]

theorem slice?_ba (N : Nat) (o n pos m : Nat) :
    Blob.slice? (ba N o n) pos m = if pos + m ≤ n then some (bytes N (o + pos) m) else none := by
  simp only [Blob.slice?, size_ba]
  split
  · rw [extract_ba, toList_ba]
    congr 2
    omega
  · rfl

/-- n bits from bit b, as an array. -/
def bits (N : Nat) (b n : Nat) : Array Bool :=
  ((List.range n).map fun i => bit N (b + i)).toArray

theorem drop_map_range {α : Type} (f : Nat → α) (N n : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun k => f (n + k) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp

theorem take_map_range {α : Type} (f : Nat → α) (N n : Nat) (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp

/-- ℰ⁻¹ of the bitmask octets from octet o: the bits from bit 8o, if the padding bits are 0. -/
theorem decodeBits?_bytes (N : Nat) (o n : Nat) :
    Blob.decodeBits? (bytes N o ((n + 7) / 8)) n =
      if ((List.range (8 * ((n + 7) / 8) - n)).all fun k => !bit N (8 * o + n + k)) then
        some (bits N (8 * o) n)
      else none := by
  have hb : ∀ i, i < 8 * ((n + 7) / 8) →
      Num.bit ((bytes N o ((n + 7) / 8)).toArray.getD (i / 8) 0).toNat (i % 8) = bit N (8 * o + i) := by
    intro i hi
    have hlt : i / 8 < (bytes N o ((n + 7) / 8)).length := by simp; omega
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hlt,
      Option.getD_some, getElem_bytes, toNat_byte, Num.bit, ← Nat.testBit_eq_decide_div_mod_eq]
    rw [show 8 * o + i = 8 * (o + i / 8) + i % 8 by omega, bit_eq _ _ _ (Nat.mod_lt _ (by decide))]
  have hmap : ((List.range (8 * ((n + 7) / 8))).map fun i =>
      Num.bit ((bytes N o ((n + 7) / 8)).toArray.getD (i / 8) 0).toNat (i % 8)) =
      (List.range (8 * ((n + 7) / 8))).map fun i => bit N (8 * o + i) := by
    apply List.map_congr_left
    intro i hi
    exact hb i (List.mem_range.1 hi)
  simp only [Blob.decodeBits?, length_bytes, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hmap, drop_map_range, take_map_range _ _ _ (by omega)]
  have hall : (((List.range (8 * ((n + 7) / 8) - n)).map fun k => bit N (8 * o + (n + k))).all
      (· == false)) = ((List.range (8 * ((n + 7) / 8) - n)).all fun k => !bit N (8 * o + n + k)) := by
    rw [List.all_map]
    congr 1
    funext k
    simp [Nat.add_assoc]
  rw [hall]
  rfl

/-- **Deblobbing a tree blob** (GP §A.1): with its two length prefixes and the jump-table width
    read off the first octets (`h1`, `hz`, `h3`, decided by the kernel on a handful of octets), the
    blob's size accounting for the jump table, code and bitmask (`hsz`), and zero padding bits
    (`hpad`), it parses to the code, bitmask and jump table at the offsets the header gives. -/
theorem parse?_ba (N : Nat) (o n : Nat) {jLen p1 z cLen p2 : Nat}
    (h1 : Blob.decodeNat? (ba N o n) 0 = some (jLen, p1))
    (h2 : p1 < n) (hz : byte N (o + p1) = z)
    (h3 : Blob.decodeNat? (ba N o n) (p1 + 1) = some (cLen, p2))
    (hsz : n = p2 + jLen * z + cLen + (cLen + 7) / 8)
    (hpad : ((List.range (8 * ((cLen + 7) / 8) - cLen)).all fun k =>
      !bit N (8 * (o + p2 + jLen * z + cLen) + cLen + k)) = true) :
    Blob.parse? (ba N o n) = some ⟨ba N (o + p2 + jLen * z) cLen,
      bits N (8 * (o + p2 + jLen * z + cLen)) cLen,
      ((List.range jLen).map fun i => Num.decodeLE (bytes N (o + p2 + i * z) z)).toArray⟩ := by
  have hj : ((List.range jLen).map fun i =>
      Num.decodeLE ((ba N o n).extract (p2 + i * z) (p2 + i * z + z)).toList) =
      (List.range jLen).map fun i => Num.decodeLE (bytes N (o + p2 + i * z) z) := by
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.1 hi
    have : (i + 1) * z ≤ jLen * z := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    rw [extract_ba, toList_ba]
    congr 2 <;> omega
  have hk : ((ba N o n).extract (p2 + jLen * z + cLen) n).toList =
      bytes N (o + p2 + jLen * z + cLen) ((cLen + 7) / 8) := by
    rw [extract_ba, toList_ba]
    congr 1
    · omega
    · omega
  have hz' : (UInt8.ofNat (byte N (o + p1))).toNat = z := by rw [toNat_byte, hz]
  simp only [Blob.parse?, h1, getElem?_ba, h2, ↓reduceIte, Option.map_some, hz',
    Option.bind_eq_bind, Option.bind_some, h3, size_ba, hj]
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), slice?_ba, ite_eq_left_iff.2 (fun h => absurd (by omega) h)]
  simp only [Option.bind_some]
  rw [hk, decodeBits?_bytes, ite_eq_left hpad]
  simp only [Option.bind_some, ba, Nat.add_assoc]

/-- The reads of the program with the cLen code octets from octet oc and the bitmask from bit mb:
    arithmetic on the tree. -/
def view (N : Nat) (oc mb cLen : Nat) : CodeView where
  zeta i := if i < cLen then byte N (oc + i) else 0
  maskExt i := if i < cLen then bit N (mb + i) else true
  maskAt i := if i < cLen then bit N (mb + i) else false
  codeSize := cLen
  maskSize := cLen

theorem getD_bits (N : Nat) (b n i : Nat) (x : Bool) :
    (bits N b n).getD i x = if i < n then bit N (b + i) else x := by
  simp only [bits, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  split <;> simp_all

theorem view_eq (N : Nat) (oc mb cLen : Nat) (jt : Array Nat) :
    (⟨ba N oc cLen, bits N mb cLen, jt⟩ : Program).view = view N oc mb cLen := by
  simp only [Program.view, view, CodeView.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [Program.zeta, getElem?_ba]
    split
    · simp [byte_lt]
    · simp
  · funext i; simp only [Program.maskExt, getD_bits]
  · funext i; simp only [Program.maskAt, getD_bits]
  · simp
  · simp [bits]

/-- **A standard program blob from the tree** (GP eq. `conditions`): with the section lengths
    its header gives (decided by the kernel on 15 octets), it parses to the sections at those
    offsets. -/
theorem jamParse?_ba (N : Nat) (o n : Nat) {oLen wLen z s pLen : Nat}
    (ho : Num.decodeLE (bytes N o 3) = oLen) (hw : Num.decodeLE (bytes N (o + 3) 3) = wLen)
    (hz : Num.decodeLE (bytes N (o + 6) 2) = z) (hs : Num.decodeLE (bytes N (o + 8) 3) = s)
    (hp : Num.decodeLE (bytes N (o + 11 + oLen + wLen) 4) = pLen)
    (hn : n = 15 + oLen + wLen + pLen) :
    JamBlob.parse? (ba N o n) = some ⟨ba N (o + 11) oLen, ba N (o + 11 + oLen) wLen, z, s,
      ba N (o + 15 + oLen + wLen) pLen⟩ := by
  simp only [JamBlob.parse?, slice?_ba, Nat.add_zero]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
  simp only [Option.map_eq_map, Option.map_some, ho, hw, hz, hs, Option.bind_eq_bind, Option.bind_some]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  simp only [Option.bind_some]
  rw [ite_eq_left (by omega)]
  simp only [Option.map_some, Option.bind_some, ← Nat.add_assoc, hp, size_ba]
  rw [ite_eq_right_iff.2 (fun h => absurd hn (by omega)), ite_eq_left (by omega)]
  simp only [Option.bind_some, ba]
  rw [show o + 11 + oLen + wLen + 4 = o + 15 + oLen + wLen by omega]

end NatBlob

end PVM
