import PVM.Invocation

/-!
# The RAM Y builds, region by region

`initialMemory jb a` (GP §A.7, eq. `memlayout`) sets page access per section and writes the three
data sections. These lemmas read it back without evaluating it: the access of any page
(`initialMemory_pages`) and the octet at any address below 2^32 (`initialMemory_read`), as a case
split on which section the address lies in. They hold for every blob, so a proof about a large
program can reason about its starting memory from a few facts about its sections (their sizes,
the octets it reads) instead of the whole blob.
-/

/-- `ByteArray.toList` lists every octet. -/
theorem ByteArray.length_toList' (bs : ByteArray) : bs.toList.length = bs.size := by
  suffices h : ∀ i r, (ByteArray.toList.loop bs i r).length = r.length + (bs.size - i) by
    simpa [ByteArray.toList] using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih => rw [ByteArray.toList.loop]; simp only [h, ↓reduceIte, ih, List.length_cons]; omega
  | case2 i r h => rw [ByteArray.toList.loop]; simp only [h, ↓reduceIte, List.length_reverse]; omega

namespace PVM

namespace Memory

/-- Setting the access of pages `first, …, first + count − 1`. -/
theorem setPages_get? (μ : Memory) (first count : Nat) (acc : Option Access) (p : Nat) :
    (μ.setPages first count acc).pages.get? p =
      if first ≤ p ∧ p < first + count then acc else μ.pages.get? p := by
  unfold setPages
  induction count with
  | zero => simp; omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl _ μ.pages = m at ih ⊢
    have key : (if first ≤ p ∧ p < first + (n + 1) then acc else μ.pages.get? p) =
        (if first + n = p then acc else m.get? p) := by
      rw [ih]
      by_cases h1 : first + n = p
      · simp only [h1, ↓reduceIte]; split <;> first | rfl | omega
      · simp only [h1, ↓reduceIte]; split <;> split <;> first | rfl | omega
    rw [key]
    cases acc with
    | none =>
      simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase, Nat.compare_eq_eq]
    | some a =>
      simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq]

@[simp] theorem empty_get? (p : Nat) : Memory.empty.pages.get? p = none := by
  simp [Memory.empty, Std.ExtTreeMap.get?_eq_getElem?]

@[simp] theorem empty_read (i : Nat) : Memory.empty.read i = 0 := by
  simp [Memory.empty, Memory.read, Std.ExtTreeMap.getD_eq_getD_getElem?]

/-- The octet at `j` after writing `bs` at `a`, for writes and reads below 2^32. -/
theorem read_writeN (μ : Memory) (a : Nat) (bs : List UInt8) (j : Nat)
    (ha : a + bs.length ≤ two32) (hj : j < two32) :
    (μ.writeN a bs).read j = if a ≤ j ∧ j < a + bs.length then bs[j - a]! else μ.read j := by
  split
  · rename_i h
    have := read_writeN_at μ a bs (by omega) (j - a) (by omega)
    rw [show a + (j - a) = j by omega] at this
    rw [this, getElem!_pos bs (j - a) (by omega)]
  · rename_i h
    apply read_writeN_of_not_mem
    intro k hk
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hj]
    omega

end Memory

/-- **Page access of Y's RAM**, section by section (later sections take precedence where the
    paper's sections would overlap, which they do not for a valid blob). -/
theorem initialMemory_pages (jb : JamBlob) (a : ByteArray) (p : Nat) :
    (initialMemory jb a).pages.get? p =
      if argStart / pageSize ≤ p ∧ p < argStart / pageSize + roundPage a.size / pageSize then
        some .read
      else if (stackEnd - roundPage jb.stackSize) / pageSize ≤ p ∧
          p < (stackEnd - roundPage jb.stackSize) / pageSize + roundPage jb.stackSize / pageSize then
        some .write
      else if rwStart jb / pageSize ≤ p ∧
          p < rwStart jb / pageSize + (roundPage jb.rw.size / pageSize + jb.heapPages) then
        some .write
      else if roStart / pageSize ≤ p ∧ p < roStart / pageSize + roundPage jb.ro.size / pageSize then
        some .read
      else none := by
  simp only [initialMemory, Memory.writeN_pages, Memory.setPages_get?, Memory.empty_get?]

/-- **The octets of Y's RAM**: the arguments, the read-write data, the read-only data, and 0
    elsewhere (for a blob whose sections fit below 2^32). -/
theorem initialMemory_read (jb : JamBlob) (a : ByteArray) (j : Nat) (hj : j < two32)
    (hro : roStart + jb.ro.size ≤ two32) (hrw : rwStart jb + jb.rw.size ≤ two32)
    (harg : argStart + a.size ≤ two32) :
    (initialMemory jb a).read j =
      if argStart ≤ j ∧ j < argStart + a.size then a.toList[j - argStart]!
      else if rwStart jb ≤ j ∧ j < rwStart jb + jb.rw.size then jb.rw.toList[j - rwStart jb]!
      else if roStart ≤ j ∧ j < roStart + jb.ro.size then jb.ro.toList[j - roStart]!
      else 0 := by
  simp only [initialMemory]
  rw [Memory.read_writeN _ _ _ _ (by simpa [ByteArray.length_toList'] using harg) hj,
    Memory.read_writeN _ _ _ _ (by simpa [ByteArray.length_toList'] using hrw) hj,
    Memory.read_writeN _ _ _ _ (by simpa [ByteArray.length_toList'] using hro) hj]
  simp only [ByteArray.length_toList']
  have : ∀ (μ : Memory) (f c : Nat) (acc : Option Access) (i : Nat),
      (μ.setPages f c acc).read i = μ.read i := fun _ _ _ _ _ => rfl
  simp only [this, Memory.empty_read]

end PVM
