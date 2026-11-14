import Services.Bootstrap.Prefix

/-!
# Y's RAM below the heap: the zeros and the read-only low memory

`StartMem` (`Prefix.lean`) lists only the octets the prefix reads before writing them. The
allocator's state after the start-up also needs the octets it never touches: every bin head, bitmap
word and field the prefix and the parameter chain leave alone still holds its initial value. In Y's
RAM (GP eq. `conditions`) the read-write zone is the blob's 184 data octets at 196608 … 196792,
then zeros up to the end of its pages and the 2 heap pages (208896). So:

- `zero`: every octet in [196792, 208896) is 0. That covers the allocator (`A0` = 196792 …
  206864), the gap to the heap base (206880) and the first chunk's header (206880 … 206896).
- `lowRO`: no octet below 196608 (the read-write zone's start) is writable.

`startMemZ_initial` proves both of Y's RAM, under the same `layoutOk` as `startMem_initial`.
-/

namespace Services.Bootstrap.Prefix

open PVM JAM

/-- What the allocator's state needs of the starting memory beyond `StartMem`. -/
structure StartMemZ (μ : Memory) : Prop where
  zero : ∀ a, 196792 ≤ a → a < 208896 → μ.read a = 0
  lowRO : ∀ a, a < 196608 → μ.writable a = false

/-- **Y's RAM is zero from the read-write data's end (196792) to 208896, and nothing below 196608
    is writable**, for a blob with the deployed section sizes and any arguments Y accepts. -/
theorem startMemZ_initial (jb : JamBlob) (a : ByteArray) (hl : layoutOk jb = true)
    (ha : a.size ≤ inputSize) : StartMemZ (initialMemory jb a) := by
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheap⟩, hstack⟩, -⟩, -⟩ := hl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  refine ⟨fun x h1 h2 => ?_, fun x h1 => ?_⟩
  · rw [initialMemory_read jb a x (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
      (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
    rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
      ite_eq_right (by rw [hrs, hrw]; omega), ite_eq_right (by simp only [roStart, zoneSize, hro]; omega)]
  · simp only [Memory.writable, initialMemory_pages, hstack, hrs, hrw, hro, hheap, argStart, stackEnd,
      roundPage, pageSize, zoneSize, inputSize, roStart]
    repeat' split
    all_goals first | rfl | omega

/-- The zeros on the range the allocator reads: [196792, 206896). -/
theorem StartMemZ.zero_alloc {μ : Memory} (h : StartMemZ μ) :
    ∀ a, 196792 ≤ a → a < 206896 → μ.read a = 0 :=
  fun a h1 h2 => h.zero a h1 (by omega)

end Services.Bootstrap.Prefix
