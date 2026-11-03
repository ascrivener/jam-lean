import PVM.Logic.Chase
import PVM.Theorems.InitMem
import PVM.Invocation

/-!
# The argument octets in memory

Reading a slice of an argument string that memory holds: refine's arguments are
ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ↕y ⌢ ℋ(p), and each decode reads one piece.
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

theorem Memory.readN_add (μ : Memory) (b m n : Nat) :
    μ.readN b (m + n) = μ.readN b m ++ μ.readN (b + m) n := by
  induction n with
  | zero => simp [Memory.readN]
  | succ n ih =>
    rw [← Nat.add_assoc, show m + n + 1 = (m + n) + 1 from rfl]
    simp only [Memory.readN, List.range_succ, List.map_append, List.map_cons, List.map_nil] at ih ⊢
    rw [ih]
    simp [Nat.add_assoc]

/-- A slice of what memory holds: if memory holds `l₁ ⌢ l₂ ⌢ l₃` at `b`, it holds `l₂` at
    `b + |l₁|`. -/
theorem Memory.readN_slice (μ : Memory) (b : Nat) (l₁ l₂ l₃ : List UInt8)
    (h : μ.readN b (l₁ ++ l₂ ++ l₃).length = l₁ ++ l₂ ++ l₃) :
    μ.readN (b + l₁.length) l₂.length = l₂ := by
  simp only [List.length_append, Memory.readN_add, List.append_assoc] at h
  have h1 := List.append_inj h (by simp [Memory.length_readN])
  have h2 := List.append_inj h1.2 (by simp [Memory.length_readN])
  exact h2.1

/-- Y's RAM holds the arguments at `argStart`. -/
theorem initialMemory_readN_args (jb : JamBlob) (a : ByteArray) (hro : roStart + jb.ro.size ≤ two32)
    (hrw : rwStart jb + jb.rw.size ≤ two32) (harg : argStart + a.size ≤ two32) :
    (initialMemory jb a).readN argStart a.size = a.toList := by
  apply List.ext_getElem (by simp [Memory.length_readN, ByteArray.length_toList'])
  intro j h1 h2
  simp only [Memory.length_readN] at h1
  simp only [Memory.readN, List.getElem_map, List.getElem_range]
  rw [initialMemory_read jb a (argStart + j) (by omega) hro hrw harg, if_pos (by omega)]
  simp [Nat.add_sub_cancel_left, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The arguments' pages of Y's RAM are readable. -/
theorem initialMemory_readable_args (jb : JamBlob) (a : ByteArray) (j : Nat) (h1 : argStart ≤ j)
    (h2 : j < argStart + a.size) : (initialMemory jb a).readable j = true := by
  simp only [Memory.readable, initialMemory_pages]
  rw [if_pos]
  · rfl
  · simp only [argStart, zoneSize, inputSize, roundPage, pageSize] at h1 h2 ⊢
    omega

end PVM
