import PVM.Logic.Chase
import PVM.Theorems.InitMem
import PVM.Invocation

/-!
# The argument octets in memory

Reading a slice of an argument string that memory holds: refine's arguments are
ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ↕y ⌢ ℋ(p), and each decode reads one piece.
-/

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
