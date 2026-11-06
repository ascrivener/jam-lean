import Services.Picoalloc.Invariant

/-!
# The chunk walk, characterized

`chunks s` is the walk of the size words from the base. A list that tiles the address space, each
of whose chunks the state's size word encodes, is that walk (`chunks_eq`); conversely the walk's
chunks are encoded by their size words (`mem_walk_hdr`). The operations' proofs exhibit the new
chunk list and check it this way, without unfolding the walk.
-/

namespace Picoalloc

theorem wordSize_sizeWord (n : Nat) (b : Bool) : wordSize (sizeWord n b) = n := by
  cases b <;> simp [wordSize, sizeWord] <;> omega

theorem wordUsed_sizeWord (n : Nat) (b : Bool) : wordUsed (sizeWord n b) = b := by
  cases b <;> simp [wordUsed, sizeWord] <;> omega

theorem sizeWord_word (w : Nat) : sizeWord (wordSize w) (wordUsed w) = w := by
  unfold sizeWord wordSize wordUsed
  by_cases h : w % 2 = 1 <;> simp [h] <;> omega

/-- A tiling ends where it says, and its chunks lie inside it. -/
theorem Tiles.mem_lt {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) :
    ∀ c ∈ cs, a ≤ c.addr ∧ c.addr + 32 * c.size ≤ limit ∧ 0 < c.size := by
  induction cs generalizing a with
  | nil => simp
  | cons d cs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have hle : ∀ c ∈ cs, a + 32 * d.size ≤ c.addr ∧ c.addr + 32 * c.size ≤ limit ∧ 0 < c.size := ih h3
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨by omega, ?_, h2⟩
      cases cs with
      | nil => simp [Tiles] at h3; omega
      | cons e cs =>
        have := hle e (by simp)
        omega
    · have := hle c hc; omega

theorem Tiles.le {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) : a ≤ limit := by
  induction cs generalizing a with
  | nil => simp [Tiles] at h; omega
  | cons d cs ih => obtain ⟨_, _, h3⟩ := h; have := ih h3; omega

/-- A tiling has at most one chunk per unit. -/
theorem Tiles.length_le {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) :
    32 * cs.length ≤ limit - a := by
  induction cs generalizing a with
  | nil => simp
  | cons d cs ih =>
    obtain ⟨_, h2, h3⟩ := h
    have := ih h3
    have := h3.le
    simp only [List.length_cons]
    omega

/-- **A tiling encoded by the size words is the walk.** -/
theorem walk_eq {s : State} {a limit fuel : Nat} {cs : List Chunk} (h : Tiles a limit cs)
    (henc : ∀ c ∈ cs, (s.hdr c.addr).size = sizeWord c.size c.used) (hf : cs.length ≤ fuel) :
    walk s a limit fuel = cs := by
  induction cs generalizing a fuel with
  | nil =>
    simp [Tiles] at h; subst h
    cases fuel <;> simp [walk]
  | cons d cs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have hlt : a < limit := by have := h3.le; omega
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hd := henc d (by simp)
      subst h1
      simp only [walk, show ¬ (d.addr ≥ limit) from by omega, ↓reduceIte, hd, wordSize_sizeWord,
        wordUsed_sizeWord]
      rw [ih h3 (fun c hc => henc c (by simp [hc])) (by simp at hf; omega)]

/-- The walk's chunks are encoded by their size words. -/
theorem mem_walk_hdr {s : State} {a limit fuel : Nat} :
    ∀ c ∈ walk s a limit fuel, (s.hdr c.addr).size = sizeWord c.size c.used := by
  induction fuel generalizing a with
  | zero => simp [walk]
  | succ fuel ih =>
    intro c hc
    unfold walk at hc
    split at hc
    · simp at hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact (sizeWord_word _).symm
      · exact ih c hc

/-- **The heap's chunks, characterized**: a tiling of the address space that the size words
    encode. -/
theorem chunks_eq {s : State} {cs : List Chunk} (h : Tiles s.base s.top cs)
    (henc : ∀ c ∈ cs, (s.hdr c.addr).size = sizeWord c.size c.used) : chunks s = cs := by
  unfold chunks walkFuel
  apply walk_eq h henc
  have := h.length_le
  unfold State.top at this
  omega

theorem chunks_hdr {s : State} : ∀ c ∈ chunks s, (s.hdr c.addr).size = sizeWord c.size c.used := by
  unfold chunks; exact mem_walk_hdr

end Picoalloc
