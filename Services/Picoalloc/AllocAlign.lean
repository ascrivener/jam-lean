import Services.Picoalloc.First

/-!
# `alloc` with any alignment, on a well-formed heap

`Alloc.lean` treats alignment one unit. With `align` units (a power of two), `alloc` takes the
first chunk C of a marked bin for `minSize = r + align`, of S ≥ r + align units, and rounds the
data unit up to a multiple of `align` counted from address 0. C is cut into three parts:

* a free **left remainder** at C of `lhs = leftOf base C align < align` units (none if 0), pushed
  back to its bin;
* the allocated chunk at `A = C + 32 · lhs` of `r + 1` units, with `prev = lhs` when `lhs ≠ 0`;
* a free **right remainder** at `A + 32 · (r + 1)` of `S − lhs − r − 1` units, if any;

and the chunk after C gets the right `prev`. `allocPostL` is that state (`allocPostL … 0 … =
allocPost …`), `alloc_align_eq` the shape of a successful `alloc`, `allocPostL_chunks` the chunk list
after it, `allocPostL_lists` the free lists, `alloc_wf_align` the invariant kept, and
`alloc_ptr_align` the block's alignment.
-/

namespace Picoalloc

/-- `alloc`'s left remainder: the units between the chunk C and the allocated chunk, whose data
    unit, counted from address 0, is the first multiple of `align` after C's header. -/
def leftOf (base C align : Nat) : Nat :=
  (base / 32 + (C - base) / 32 + 1 + (align - 1)) / align * align - base / 32 - 1 - (C - base) / 32

/-- The left remainder is below `align`, and the allocated chunk's data unit is a multiple of
    `align`. -/
theorem leftOf_spec {base C align : Nat} (ha : 0 < align) :
    leftOf base C align < align ∧
    (base / 32 + (C - base) / 32 + 1 + (align - 1)) / align * align =
      base / 32 + ((C - base) / 32 + leftOf base C align) + 1 ∧
    (base / 32 + (C - base) / 32 + leftOf base C align + 1) % align = 0 := by
  unfold leftOf
  generalize base / 32 = u
  generalize (C - base) / 32 = c
  have hdm := Nat.div_add_mod (u + c + 1 + (align - 1)) align
  have hml := Nat.mod_lt (u + c + 1 + (align - 1)) ha
  have hmod : (u + c + 1 + (align - 1)) / align * align % align = 0 := Nat.mul_mod_left _ _
  rw [Nat.mul_comm] at hdm
  generalize (u + c + 1 + (align - 1)) / align * align = R at *
  generalize (u + c + 1 + (align - 1)) % align = m at *
  refine ⟨by omega, by omega, ?_⟩
  rw [show u + c + (R - u - 1 - c) + 1 = R by omega]; exact hmod

/-- The state `alloc` leaves, from the state `s1` after the space's growth, for the bin's first
    chunk C of size S and a left remainder of `lhs` units (`allocPost` when `lhs = 0`); `T` is the
    end of the address space. -/
def allocPostL (s1 : State) (bin r S lhs T : Nat) : State :=
  let C := s1.heads bin
  let A := s1.base + 32 * ((C - s1.base) / 32 + lhs)
  let s2 := unregisterFirst s1 C bin
  let ls := register s2 C (s1.hdr C).prev lhs
  let s3 := registerAlloc ls.1 A ls.2 (r + 1)
  let rs := register s3 (A + 32 * (1 + r)) (r + 1) (S - lhs - r - 1)
  if A + 32 * (1 + r) + 32 * (S - lhs - r - 1) < T
  then setHdr rs.1 (A + 32 * (1 + r) + 32 * (S - lhs - r - 1)) (fun h => { h with prev := rs.2 }) else rs.1

/-- Without a left remainder, `allocPostL` is the alignment-one `allocPost`. -/
theorem allocPostL_zero (s1 : State) (bin r S T : Nat) : allocPostL s1 bin r S 0 T = allocPost s1 bin r S T := by
  unfold allocPostL allocPost
  simp only [Nat.add_zero, Nat.sub_zero, register_zero]

/-- **A successful `alloc`'s shape**, with any alignment, on an initialized heap: a power-of-two
    `align`, a marked bin for `r + align` units whose first chunk has S ≥ r + align units, the left
    remainder `leftOf`, a grown allocated space covering the allocated chunk and the right
    remainder's header, the returned pointer, and the state `allocPostL`. -/
theorem alloc_align_eq {grow : Grow} {hb align r p : Nat} {s s' : State} (hbase : s.base ≠ 0)
    (h : alloc grow hb align r s = some (p, s')) :
    ∃ bin a1, 0 < align ∧ align &&& (align - 1) = 0 ∧
      (findFirst s (binUp (r + align))).or (findFirst s (binDown (r + align))) = some bin ∧
      r + align ≤ maxSize ∧ r + align ≤ wordSize (s.hdr (s.heads bin)).size ∧ s.allocated ≤ a1 ∧
      (s.heads bin - s.base) / 32 + leftOf s.base (s.heads bin) align + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - leftOf s.base (s.heads bin) align - r - 1 = 0 then 0 else 1)
          ≤ a1 ∧
      p = s.base + 32 * ((s.heads bin - s.base) / 32 + leftOf s.base (s.heads bin) align) + 32 ∧
      s' = allocPostL { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size)
        (leftOf s.base (s.heads bin) align) (s.base + 32 * maxSize) := by
  unfold alloc at h
  split at h
  · simp at h
  rename_i hal
  rw [init_self hbase] at h
  have ha : 0 < align := by omega
  have hpow : align &&& (align - 1) = 0 := by omega
  rw [show r + 1 + (align - 1) = r + align by omega] at h
  simp only [Option.bind_eq_bind, Option.bind_some, Option.orElse_eq_or] at h
  split at h
  · simp at h
  rename_i hmax
  cases hfb : (findFirst s (binUp (r + align))).or (findFirst s (binDown (r + align))) with
  | none => simp [hfb] at h
  | some bin =>
    simp only [hfb, Option.bind_some] at h
    split at h
    · simp at h
    rename_i hS
    refine ⟨bin, ?_⟩
    obtain ⟨hl1, hl2, -⟩ := leftOf_spec (base := s.base) (C := s.heads bin) ha
    have e0 : leftOf s.base (s.heads bin) align = (s.base / 32 + (s.heads bin - s.base) / 32 + 1 + (align - 1)) /
      align * align - s.base / 32 - 1 - (s.heads bin - s.base) / 32 := rfl
    generalize (s.base / 32 + (s.heads bin - s.base) / 32 + 1 + (align - 1)) / align * align = R at h hl2 e0
    generalize leftOf s.base (s.heads bin) align = L at h hl1 hl2 e0 ⊢
    generalize wordSize (s.hdr (s.heads bin)).size = S at h hS ⊢
    rw [← e0] at h
    rw [show R - s.base / 32 - 1 = (s.heads bin - s.base) / 32 + L by omega,
      show R - s.base / 32 = (s.heads bin - s.base) / 32 + L + 1 by omega,
      show S - r - L - 1 = S - L - r - 1 by omega] at h
    generalize hE : (s.heads bin - s.base) / 32 + L + 1 + r + (if S - L - r - 1 = 0 then 0 else 1) = E at h ⊢
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq, register_base, registerAlloc_base, unregisterFirst_base] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨E, ha, hpow, rfl, by omega, by omega, by omega, Nat.le_refl _, rfl, rfl⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq, register_base, registerAlloc_base, unregisterFirst_base] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s.allocated, ha, hpow, rfl, by omega, by omega, Nat.le_refl _, by omega, rfl, rfl⟩


/-- The size words `register` leaves. -/
theorem register_size {s : State} {n prev size : Nat} (x : Nat) :
    ((register s n prev size).1.hdr x).size = if x = n ∧ size ≠ 0 then sizeWord size false else (s.hdr x).size := by
  by_cases h : x = n ∧ size ≠ 0
  · obtain ⟨rfl, h0⟩ := h; rw [ite_eq_left ⟨rfl, h0⟩]; exact register_size_self h0
  · rw [ite_eq_right h]
    by_cases hx : x = n
    · subst hx
      have h0 : size = 0 := by omega
      subst h0; rw [register_zero]
    · exact (register_hdr_other hx).2.1

/-- The `prev` fields `register` leaves. -/
theorem register_prev {s : State} {n prev size : Nat} (x : Nat) :
    ((register s n prev size).1.hdr x).prev = if x = n ∧ size ≠ 0 then prev else (s.hdr x).prev := by
  by_cases h : x = n ∧ size ≠ 0
  · obtain ⟨rfl, h0⟩ := h; rw [ite_eq_left ⟨rfl, h0⟩]; exact register_prev_self h0
  · rw [ite_eq_right h]
    by_cases hx : x = n
    · subst hx
      have h0 : size = 0 := by omega
      subst h0; rw [register_zero]
    · exact (register_hdr_other hx).1

@[simp] theorem allocPostL_base {s1 : State} {bin r S lhs T : Nat} :
    (allocPostL s1 bin r S lhs T).base = s1.base := by
  unfold allocPostL; dsimp only; split
  · rw [setHdr_base, register_base, registerAlloc_base, register_base, unregisterFirst_base]
  · rw [register_base, registerAlloc_base, register_base, unregisterFirst_base]

@[simp] theorem allocPostL_allocated {s1 : State} {bin r S lhs T : Nat} :
    (allocPostL s1 bin r S lhs T).allocated = s1.allocated := by
  unfold allocPostL; dsimp only; split
  · rw [setHdr_allocated, register_allocated, registerAlloc_allocated, register_allocated,
      unregisterFirst_allocated]
  · rw [register_allocated, registerAlloc_allocated, register_allocated, unregisterFirst_allocated]

/-- `allocPostL` with the chunk's address named. -/
theorem allocPostL_unfold {s1 : State} {bin r S lhs C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) :
    allocPostL s1 bin r S lhs T =
      let ls := register (unregisterFirst s1 C bin) C (s1.hdr C).prev lhs
      let s3 := registerAlloc ls.1 (C + 32 * lhs) ls.2 (r + 1)
      let rs := register s3 (C + 32 * lhs + 32 * (1 + r)) (r + 1) (S - lhs - r - 1)
      if C + 32 * lhs + 32 * (1 + r) + 32 * (S - lhs - r - 1) < T
      then setHdr rs.1 (C + 32 * lhs + 32 * (1 + r) + 32 * (S - lhs - r - 1)) (fun h => { h with prev := rs.2 })
      else rs.1 := by
  unfold allocPostL
  dsimp only
  rw [hC, show s1.base + 32 * ((C - s1.base) / 32 + lhs) = C + 32 * lhs by omega]

/-- The size words `allocPostL` leaves. -/
theorem allocPostL_size {s1 : State} {bin r S lhs C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) (x : Nat) :
    ((allocPostL s1 bin r S lhs T).hdr x).size =
      if x = C + 32 * lhs then sizeWord (r + 1) true
      else if x = C + 32 * lhs + 32 * (1 + r) ∧ S - lhs - r - 1 ≠ 0 then sizeWord (S - lhs - r - 1) false
      else if x = C ∧ lhs ≠ 0 then sizeWord lhs false
      else (s1.hdr x).size := by
  rw [allocPostL_unfold hC hA]
  dsimp only
  have hpost : ∀ (t : State) (c : Prop) [Decidable c] (y p : Nat),
      ((if c then setHdr t y (fun h => { h with prev := p }) else t).hdr x).size = (t.hdr x).size := by
    intro t c _ y p; split
    · exact setHdr_prev_size
    · rfl
  rw [hpost, register_size, registerAlloc_hdr]
  by_cases h1 : x = C + 32 * lhs + 32 * (1 + r) ∧ S - lhs - r - 1 ≠ 0
  · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : x = C + 32 * lhs
    · rw [ite_eq_left h2, ite_eq_left h2]
    · rw [ite_eq_right h2, ite_eq_right h2, register_size, unregisterFirst_hdr.2.1]

/-- The `prev` fields `allocPostL` leaves. -/
theorem allocPostL_prev {s1 : State} {bin r S lhs C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) (hr : lhs + r + 1 ≤ S) (x : Nat) :
    ((allocPostL s1 bin r S lhs T).hdr x).prev =
      if x = C + 32 * S ∧ x < T then (if S - lhs - r - 1 = 0 then r + 1 else S - lhs - r - 1)
      else if x = C + 32 * lhs + 32 * (1 + r) ∧ S - lhs - r - 1 ≠ 0 then r + 1
      else if x = C + 32 * lhs ∧ lhs ≠ 0 then lhs
      else (s1.hdr x).prev := by
  rw [allocPostL_unfold hC hA]
  dsimp only
  rw [show C + 32 * lhs + 32 * (1 + r) + 32 * (S - lhs - r - 1) = C + 32 * S by omega]
  by_cases h0 : x = C + 32 * S ∧ x < T
  · obtain ⟨rfl, hxT⟩ := h0
    rw [ite_eq_left hxT, ite_eq_left ⟨rfl, hxT⟩, setHdr_prev_get, ite_eq_left rfl, register_snd]
  · rw [ite_eq_right h0]
    have hfin : ∀ (t : State) (p : Nat), ((if C + 32 * S < T then setHdr t (C + 32 * S)
        (fun h => { h with prev := p }) else t).hdr x).prev = (t.hdr x).prev := by
      intro t p; split
      · rename_i hT; rw [setHdr_prev_get, ite_eq_right (fun h => h0 ⟨h, h ▸ hT⟩)]
      · rfl
    rw [hfin, register_prev]
    by_cases h1 : x = C + 32 * lhs + 32 * (1 + r) ∧ S - lhs - r - 1 ≠ 0
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, registerAlloc_hdr]
      by_cases h2 : x = C + 32 * lhs
      · subst h2
        rw [ite_eq_left rfl, register_snd]
        by_cases hl : lhs = 0
        · rw [ite_eq_left hl, ite_eq_right (by omega)]
          simp only [hl, Nat.mul_zero, Nat.add_zero]
        · rw [ite_eq_right hl, ite_eq_left ⟨rfl, hl⟩]
      · rw [ite_eq_right h2, ite_eq_right (fun h => h2 h.1), register_prev]
        by_cases h3 : x = C ∧ lhs ≠ 0
        · rw [ite_eq_left h3, h3.1]
        · rw [ite_eq_right h3]; exact unregisterFirst_hdr.1


/-- The free left remainder before the allocated chunk, if any. -/
def leftChunk (C lhs : Nat) : List Chunk := if lhs = 0 then [] else [⟨C, lhs, false⟩]

/-- Splitting off a left remainder of `lhs` units keeps a tiling. -/
theorem Tiles.splitLeft {a top C S lhs : Nat} {pre post : List Chunk} (hl : lhs < S)
    (h : Tiles a top (pre ++ ⟨C, S, false⟩ :: post)) :
    Tiles a top ((pre ++ leftChunk C lhs) ++ ⟨C + 32 * lhs, S - lhs, false⟩ :: post) := by
  unfold leftChunk
  by_cases h0 : lhs = 0
  · subst h0; simpa using h
  · rw [ite_eq_right h0, List.append_assoc, List.singleton_append]
    exact Tiles.split (by omega) hl h

/-- The tiling after `alloc` with a left remainder. -/
theorem tiles_afterL {a top C S r lhs : Nat} {pre post : List Chunk} (hr : lhs + r + 1 ≤ S)
    (h : Tiles a top (pre ++ ⟨C, S, false⟩ :: post)) :
    Tiles a top (pre ++ leftChunk C lhs ++ ⟨C + 32 * lhs, r + 1, true⟩ ::
      (remChunk (C + 32 * lhs) r (S - lhs) ++ post)) := by
  exact tiles_after (by omega) (Tiles.splitLeft (by omega) h)

/-- Coalescing looks only at the chunks' `used` flags. -/
theorem Coalesced.relabel {c d : Chunk} {l : List Chunk} (h : Coalesced (c :: l)) (hu : c.used = d.used) :
    Coalesced (d :: l) := by
  cases l with
  | nil => trivial
  | cons e es => exact ⟨by rw [← hu]; exact h.1, h.2⟩

/-- Cutting a free chunk into a free left remainder (whose predecessor is allocated, as C was
    free), an allocated chunk and a free right remainder (whose successor is allocated) keeps a list
    coalesced. -/
theorem Coalesced.splitL {pre post : List Chunk} {C S A k lhs r S' : Nat}
    (h : Coalesced (pre ++ ⟨C, S, false⟩ :: post)) :
    Coalesced (pre ++ leftChunk C lhs ++ ⟨A, k, true⟩ :: (remChunk A r S' ++ post)) := by
  obtain ⟨hp, hcp, hlink⟩ := Coalesced.append.mp h
  have hmid : Coalesced (⟨A, k, true⟩ :: (remChunk A r S' ++ post)) := by
    have := Coalesced.split (pre := []) (C' := A + 32 * (r + 1)) (S' := S' - r - 1) (k := k) hcp
    simp only [List.nil_append] at this
    unfold remChunk
    split
    · exact Coalesced.relabel this.2 rfl
    · exact Coalesced.relabel this.1 rfl
  rw [List.append_assoc]
  refine Coalesced.append.mpr ⟨hp, ?_, fun x hx y _ => ?_⟩
  · unfold leftChunk
    split
    · exact hmid
    · exact ⟨by simp, hmid⟩
  · have := hlink x hx ⟨C, S, false⟩ (by simp)
    simp only [Bool.or_false] at this
    simp [this]

/-- The chunk list after `allocPostL`, from the tiling and size words before. -/
theorem allocPostL_chunks {s : State} {r bin a1 lhs C S : Nat} {pre post : List Chunk}
    (hcs : chunks s = pre ++ ⟨C, S, false⟩ :: post) (htl : Tiles s.base s.top (pre ++ ⟨C, S, false⟩ :: post))
    (hC : s.heads bin = C) (hA : s.base + 32 * ((C - s.base) / 32) = C) (hr : lhs + r + 1 ≤ S) :
    chunks (allocPostL { s with allocated := a1 } bin r S lhs s.top) =
      pre ++ leftChunk C lhs ++ ⟨C + 32 * lhs, r + 1, true⟩ ::
        (remChunk (C + 32 * lhs) r (S - lhs) ++ post) := by
  have hout : ∀ d ∈ pre ++ post, d.addr + 32 * d.size ≤ C ∨ C + 32 * S ≤ d.addr := by
    intro d hd
    obtain ⟨m, h1, h2, h3, h4⟩ := Tiles.append.mp htl
    simp only at h2 h3 h4
    rcases List.mem_append.mp hd with hd | hd
    · left; have := h1.mem_lt d hd; omega
    · right; have := h4.mem_lt d hd; omega
  have hpos : ∀ d ∈ pre ++ post, 0 < d.size := fun d hd => (htl.mem_lt d (by
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ hd
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hd))).2.2
  have hsz := fun x => allocPostL_size (s1 := { s with allocated := a1 }) (bin := bin) (r := r) (S := S)
    (lhs := lhs) (T := s.top) (C := C) hC hA x
  apply chunks_eq
  · unfold State.top at htl ⊢
    simp only [allocPostL_base]
    exact tiles_afterL hr htl
  · intro c hc
    rw [hsz]
    have hold : ∀ c ∈ pre ++ post, (s.hdr c.addr).size = sizeWord c.size c.used := by
      intro c hc
      apply chunks_hdr c
      rw [hcs]
      rcases List.mem_append.mp hc with hc | hc
      · exact List.mem_append_left _ hc
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)
    have other : ∀ c ∈ pre ++ post, ((if c.addr = C + 32 * lhs then sizeWord (r + 1) true
        else if c.addr = C + 32 * lhs + 32 * (1 + r) ∧ S - lhs - r - 1 ≠ 0 then sizeWord (S - lhs - r - 1) false
        else if c.addr = C ∧ lhs ≠ 0 then sizeWord lhs false
        else (s.hdr c.addr).size) = sizeWord c.size c.used) := by
      intro c hc
      have := hout c hc; have := hpos c hc
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hold c hc
    rw [List.append_assoc] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact other c (List.mem_append_left _ hc)
    rcases List.mem_append.mp hc with hc | hc
    · unfold leftChunk at hc
      split at hc
      · simp at hc
      · rename_i h0
        simp only [List.mem_singleton] at hc
        subst hc
        dsimp only
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨rfl, h0⟩]
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    rcases List.mem_append.mp hc with hc | hc
    · unfold remChunk at hc
      split at hc
      · simp at hc
      · rename_i h0
        simp only [List.mem_singleton] at hc
        subst hc
        dsimp only
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
    · exact other c (List.mem_append_right _ hc)


/-- **The free lists after `allocPostL`**: the bin's head `C` is popped, the left remainder (at `C`)
    and the right remainder pushed, each if nonempty. -/
theorem allocPostL_lists {s1 : State} {bin r S lhs C T : Nat} {F : Nat → Nat → Prop}
    (hF : FreeLists s1 F) (hd : Disj F) (hbits : BitsOk s1.secondary s1.primary s1.heads)
    (hbin : bin < binCount) (hC : s1.heads bin = C) (hC0 : C ≠ 0)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C)
    (hN : S - lhs - r - 1 ≠ 0 → ∀ b, ¬ F b (C + 32 * lhs + 32 * (1 + r))) :
    FreeLists (allocPostL s1 bin r S lhs T) (fun b a => ((F b a ∧ a ≠ C) ∨ (lhs ≠ 0 ∧ b = binDown lhs ∧ a = C)) ∨
        (S - lhs - r - 1 ≠ 0 ∧ b = binDown (S - lhs - r - 1) ∧ a = C + 32 * lhs + 32 * (1 + r))) ∧
      BitsOk (allocPostL s1 bin r S lhs T).secondary (allocPostL s1 bin r S lhs T).primary
        (allocPostL s1 bin r S lhs T).heads := by
  obtain ⟨p1, p2⟩ := pop_ok hF hd hbits hbin hC hC0
  rw [allocPostL_unfold hC hA]
  dsimp only
  generalize unregisterFirst s1 C bin = s2 at p1 p2 ⊢
  -- the left remainder
  have L : FreeLists (register s2 C (s1.hdr C).prev lhs).1
      (fun b a => (F b a ∧ a ≠ C) ∨ (lhs ≠ 0 ∧ b = binDown lhs ∧ a = C)) ∧
      BitsOk (register s2 C (s1.hdr C).prev lhs).1.secondary (register s2 C (s1.hdr C).prev lhs).1.primary
        (register s2 C (s1.hdr C).prev lhs).1.heads := by
    by_cases hl : lhs = 0
    · rw [hl, register_zero]
      exact ⟨p1.iff (fun b a _ => ⟨Or.inl, fun h => h.elim id (fun h => absurd rfl h.1)⟩), p2⟩
    · obtain ⟨u1, u2⟩ := push_ok (prev := (s1.hdr C).prev) p1 (fun b b' a h1 h2 => hd b b' a h1.1 h2.1) p2 hl
        (toBin_lt false (Nat.min_le_right _ _)) hC0 (fun b h => h.2 rfl)
      exact ⟨u1.iff (fun b a _ => ⟨fun h => h.elim Or.inl (fun h => Or.inr ⟨hl, h⟩),
        fun h => h.elim Or.inl (fun h => Or.inr h.2)⟩), u2⟩
  have hd1 : Disj (fun b a => (F b a ∧ a ≠ C) ∨ (lhs ≠ 0 ∧ b = binDown lhs ∧ a = C)) := by
    rintro b b' a (⟨h1, h1'⟩ | ⟨-, hb1, ha1⟩) (⟨h2, h2'⟩ | ⟨-, hb2, ha2⟩)
    · exact hd b b' a h1 h2
    · exact absurd ha2 h1'
    · exact absurd ha1 h2'
    · rw [hb1, hb2]
  generalize register s2 C (s1.hdr C).prev lhs = ls at L ⊢
  obtain ⟨q1, q2⟩ := L
  generalize hs3 : registerAlloc ls.1 (C + 32 * lhs) ls.2 (r + 1) = s3
  have hn3 : ∀ x, (s3.hdr x).next = (ls.1.hdr x).next ∧ (s3.hdr x).prevL = (ls.1.hdr x).prevL := by
    intro x; rw [← hs3, registerAlloc_hdr]
    split
    · rename_i h; subst h; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have q3 := q1.congr (s := ls.1) (t := s3) (by rw [← hs3, registerAlloc_heads]) (fun x => (hn3 x).1)
    (fun x => (hn3 x).2)
  have q4 : BitsOk s3.secondary s3.primary s3.heads := by
    rw [← hs3, registerAlloc_secondary, registerAlloc_primary, registerAlloc_heads]; exact q2
  have fin : ∀ (t : State) (G : Nat → Nat → Prop) (c : Prop) [Decidable c] (y : Nat) (f : Hdr → Hdr),
      (∀ h, (f h).next = h.next) → (∀ h, (f h).prevL = h.prevL) →
      FreeLists t G ∧ BitsOk t.secondary t.primary t.heads →
      FreeLists (if c then setHdr t y f else t) G ∧
        BitsOk (if c then setHdr t y f else t).secondary (if c then setHdr t y f else t).primary
          (if c then setHdr t y f else t).heads := by
    intro t G c _ y f hf1 hf2 ⟨h1, h2⟩
    split
    · exact ⟨h1.congr rfl (setHdr_next hf1) (setHdr_prevL hf2), h2⟩
    · exact ⟨h1, h2⟩
  by_cases hR : S - lhs - r - 1 = 0
  · rw [hR, register_zero]
    refine fin _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ⟨q3.iff (fun b a _ => ?_), q4⟩
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd rfl h.1)⟩
  · obtain ⟨u1, u2⟩ := push_ok (n := C + 32 * lhs + 32 * (1 + r)) (prev := r + 1) q3 hd1 q4 hR (toBin_lt false (Nat.min_le_right _ _))
      (by omega) (by
        rintro b (⟨h1, -⟩ | ⟨-, -, h2⟩)
        · exact hN hR b h1
        · omega)
    generalize register s3 (C + 32 * lhs + 32 * (1 + r)) (r + 1) (S - lhs - r - 1) = rs at u1 u2 ⊢
    refine fin _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ⟨u1.iff (fun b a _ => ?_), u2⟩
    exact ⟨fun h => h.elim Or.inl (fun h => Or.inr ⟨hR, h⟩), fun h => h.elim Or.inl (fun h => Or.inr h.2)⟩

/-- Taking the left remainder off a free chunk, against the free chunks. -/
theorem free_left {pre post : List Chunk} {C S lhs a b : Nat}
    (hpre : ∀ d ∈ pre, d.addr < C) (hpost : ∀ d ∈ post, C + 32 * S ≤ d.addr) (hl : lhs < S) :
    ((Fof (pre ++ ⟨C, S, false⟩ :: post) b a ∧ a ≠ C) ∨ (lhs ≠ 0 ∧ b = binDown lhs ∧ a = C)) ↔
      (Fof (pre ++ leftChunk C lhs ++ ⟨C + 32 * lhs, S - lhs, false⟩ :: post) b a ∧ a ≠ C + 32 * lhs) := by
  unfold leftChunk
  by_cases h0 : lhs = 0
  · subst h0
    simp only [ne_eq, not_true_eq_false, false_and, or_false, ↓reduceIte, List.append_nil, Nat.mul_zero,
      Nat.add_zero, Nat.sub_zero]
  · rw [ite_eq_right h0, List.append_assoc, List.singleton_append]
    constructor
    · rintro (⟨⟨c, hc, h1, h2, h3⟩, hne⟩ | ⟨-, hb, ha⟩)
      · rcases List.mem_append.mp hc with hc | hc
        · exact ⟨⟨c, List.mem_append_left _ hc, h1, h2, h3⟩, by have := hpre c hc; omega⟩
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact absurd h1.symm hne
          · exact ⟨⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)), h1, h2, h3⟩,
              by have := hpost c hc; omega⟩
      · exact ⟨⟨⟨C, lhs, false⟩, List.mem_append_right _ List.mem_cons_self, ha.symm, rfl, hb.symm⟩, by omega⟩
    · rintro ⟨⟨c, hc, h1, h2, h3⟩, hne⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl ⟨⟨c, List.mem_append_left _ hc, h1, h2, h3⟩, by have := hpre c hc; omega⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inr ⟨h0, h3.symm, h1.symm⟩
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact absurd h1.symm hne
          · exact Or.inl ⟨⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ hc), h1, h2, h3⟩,
              by have := hpost c hc; omega⟩


/-- **`allocPostL` keeps the heap well-formed**: from a bin found for some `k ≤ maxSize`, a left
    remainder of `lhs` units and an allocation of `r + 1` units fitting in its first chunk, and an
    allocated space covering the new chunk. -/
theorem allocPostL_wf {s : State} {k r bin a1 lhs : Nat} (hwf : WF s) (hk : 1 ≤ k) (hmax : k ≤ maxSize)
    (hbin : (findFirst s (binUp k)).or (findFirst s (binDown k)) = some bin)
    (hlr : lhs + r + 1 ≤ wordSize (s.hdr (s.heads bin)).size) (ha1 : s.allocated ≤ a1)
    (hend : (s.heads bin - s.base) / 32 + lhs + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - lhs - r - 1 = 0 then 0 else 1) ≤ a1) :
    WF (allocPostL { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) lhs s.top) := by
  have hbin' : (findFirst s (binUp (k - 1 + 1))).or (findFirst s (binDown (k - 1 + 1))) = some bin := by
    rw [Nat.sub_add_cancel hk]; exact hbin
  obtain ⟨hbc, hne, ⟨rest, hl, hbl, hnd, hex⟩, hbS, ⟨pre, post, hcs⟩, hCb, hCal⟩ :=
    bin_chunk hwf (by omega) hbin'
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold SpaceOk at hspace
  generalize hs' : allocPostL { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) lhs s.top
    = s'
  have hb' : s'.base = s.base := by rw [← hs', allocPostL_base]
  have ha' : s'.allocated = a1 := by rw [← hs', allocPostL_allocated]
  have ht' : s'.top = s.top := by unfold State.top; rw [hb']
  generalize hC : s.heads bin = C at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hA : s.base + 32 * ((C - s.base) / 32) = C := by omega
  rw [hcs] at htiles hcoal hspace
  have htl := htiles
  have hcs' := allocPostL_chunks (a1 := a1) (bin := bin) hcs htl hC hA hlr
  rw [hs'] at hcs'
  obtain ⟨hpa, hph, hpp, hpt⟩ := Tiles.around htl
  have hpre : ∀ d ∈ pre, d.addr < C := fun d hd => by
    have := hpa d hd
    have := (htl.mem_lt d (List.mem_append_left _ hd)).2.2
    omega
  have hpost : ∀ d ∈ post, C + 32 * S ≤ d.addr := fun d hd => (hpp d hd).1
  refine ⟨by rw [hb']; exact hb0, by rw [hb']; exact hbal, by rw [ht']; exact hfit, ?_, ?_, ?_, ?_, ?_⟩
  · -- tiling
    unfold TilesOk; rw [hcs', hb', ht']
    exact tiles_afterL hlr htl
  · -- coalesced
    unfold CoalOk; rw [hcs']
    exact Coalesced.splitL hcoal
  · -- prev links
    unfold PrevsOk; rw [hcs']
    unfold PrevsOk at hprev; rw [hcs] at hprev
    obtain ⟨hpre', hmid, hlink⟩ := PrevOk.append.mp hprev
    have hpv := fun x => allocPostL_prev (s1 := { s with allocated := a1 }) (bin := bin) (r := r) (S := S)
      (lhs := lhs) (T := s.top) (C := C) hC hA hlr x
    rw [hs'] at hpv
    generalize s.top = T at hpv hpp
    have keep : ∀ d ∈ pre ++ post.tail, (s'.hdr d.addr).prev = (s.hdr d.addr).prev := by
      intro d hd
      rw [hpv]
      have hcases : d.addr < C ∨ C + 32 * S < d.addr := by
        rcases List.mem_append.mp hd with hd | hd
        · exact Or.inl (hpre d hd)
        · exact Or.inr (hpt d hd)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    have hCp : (s'.hdr C).prev = (s.hdr C).prev := by
      rw [hpv, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    -- from the allocated chunk on
    have hpostOk : PrevOk s' post := by
      cases post with
      | nil => trivial
      | cons e es => exact hmid.2.congr (fun d hd => keep d (List.mem_append_right _ (by simpa using hd)))
    have hhead : ∀ d ∈ post.head?, (s'.hdr d.addr).prev =
        (if S - lhs - r - 1 = 0 then r + 1 else S - lhs - r - 1) := by
      intro d hd
      rw [hpv]
      have hda := hph d hd
      have hlt : d.addr < T := (hpp d (List.mem_of_mem_head? hd)).2
      rw [hda] at hlt ⊢
      rw [ite_eq_left ⟨rfl, hlt⟩]
    have hZ : PrevOk s' (⟨C + 32 * lhs, r + 1, true⟩ :: (remChunk (C + 32 * lhs) r (S - lhs) ++ post)) := by
      unfold remChunk
      split
      · rename_i h0
        simp only [List.nil_append]
        cases post with
        | nil => trivial
        | cons e es =>
          refine ⟨?_, hpostOk⟩
          have := hhead e (by simp)
          rw [ite_eq_left h0] at this
          exact this
      · rename_i h0
        simp only [List.singleton_append]
        refine ⟨?_, ?_⟩
        · have e1 : C + 32 * lhs + 32 * (r + 1) = C + 32 * lhs + 32 * (1 + r) := by omega
          have e2 : ¬ (C + 32 * lhs + 32 * (1 + r) = C + 32 * S ∧ C + 32 * lhs + 32 * (1 + r) < T) := by omega
          rw [Chunk.addr_mk', Chunk.size_mk', e1, hpv, ite_eq_right e2, ite_eq_left ⟨rfl, h0⟩]
        · cases post with
          | nil => trivial
          | cons e es =>
            refine ⟨?_, hpostOk⟩
            have := hhead e (by simp)
            rw [ite_eq_right h0] at this
            exact this
    rw [List.append_assoc]
    refine PrevOk.append.mpr ⟨hpre'.congr (fun d hd => keep d (List.mem_append_left _ (List.mem_of_mem_tail hd))),
      ?_, fun x hx y hy => ?_⟩
    · unfold leftChunk
      split
      · exact hZ
      · rename_i h0
        refine ⟨?_, hZ⟩
        rw [Chunk.addr_mk', Chunk.size_mk', hpv, ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left ⟨rfl, h0⟩]
    · -- the link from the last chunk before C
      have hyC : y.addr = C := by
        unfold leftChunk at hy
        split at hy
        · rename_i h0
          simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy; simp [h0]
        · simp only [List.singleton_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy; rfl
      rw [hyC, hCp]
      exact hlink x hx ⟨C, S, false⟩ (by simp)
  · -- free lists
    unfold ListsOk' at hlists ⊢
    rw [hcs] at hlists
    rw [hcs']
    have hF0 : FreeLists { s with allocated := a1 } (Fof (pre ++ ⟨C, S, false⟩ :: post)) :=
      FreeLists.congr (s := s) (fun b hb => hlists.lists b hb) rfl (fun _ => rfl) (fun _ => rfl)
    have hd0 : Disj (Fof (pre ++ ⟨C, S, false⟩ :: post)) := Fof_disj htl (fun _ h => h)
    have hN : S - lhs - r - 1 ≠ 0 → ∀ b, ¬ Fof (pre ++ ⟨C, S, false⟩ :: post) b (C + 32 * lhs + 32 * (1 + r)) := by
      rintro hR b ⟨c, hc, h1, -, -⟩
      rcases List.mem_append.mp hc with hc | hc
      · have := hpre c hc; omega
      · rcases List.mem_cons.mp hc with rfl | hc
        · simp only at h1; omega
        · have := hpost c hc; omega
    obtain ⟨hL, hB⟩ := allocPostL_lists (s1 := { s with allocated := a1 }) (T := s.top) hF0 hd0
      ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩ hbc hC hne hA hN
    rw [hs'] at hL hB
    obtain ⟨b1, b2, b3, b4⟩ := hB
    refine ⟨fun b hb => ?_, b1, b2, b3, b4⟩
    obtain ⟨l, h1, h2, h3, h4⟩ := hL b hb
    refine ⟨l, h1, h2, h3, fun a => (h4 a).trans ?_⟩
    show (_ ∨ _) ↔ _
    rw [free_left hpre hpost (by omega)]
    have := free_after (pre := pre ++ leftChunk C lhs) (post := post) (C := C + 32 * lhs) (S := S - lhs) (r := r)
      (a := a) (b := b) (fun d hd => by
        rcases List.mem_append.mp hd with hd | hd
        · have := hpre d hd; omega
        · unfold leftChunk at hd
          split at hd
          · simp at hd
          · rename_i h0
            simp only [List.mem_singleton] at hd
            subst hd; show C < C + 32 * lhs; omega)
      (fun d hd => by have := hpost d hd; omega) (by omega)
    exact this
  · -- space
    unfold SpaceOk; rw [hcs', ha', hb']
    intro c hc
    have hCs := (hspace ⟨C, S, false⟩ (List.mem_append_right _ List.mem_cons_self)).2
    simp only at hCs
    rw [List.append_assoc] at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨h1, h2⟩ := hspace c (List.mem_append_left _ hc)
      exact ⟨fun hu => by have := h1 hu; omega, by omega⟩
    rcases List.mem_append.mp hc with hc | hc
    · unfold leftChunk at hc
      split at hc
      · simp at hc
      · simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨fun h => by simp at h, by simp only; omega⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · simp only [forall_const]
      split at hend <;> omega
    rcases List.mem_append.mp hc with hc | hc
    · unfold remChunk at hc
      split at hc
      · simp at hc
      · rename_i h0
        simp only [List.mem_singleton] at hc
        subst hc
        simp only [Bool.false_eq_true, false_imp_iff, true_and]
        rw [ite_eq_right (by omega)] at hend
        omega
    · obtain ⟨h1, h2⟩ := hspace c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
      exact ⟨fun hu => by have := h1 hu; omega, by omega⟩


/-- **`alloc` keeps the heap well-formed**, with any alignment. -/
theorem alloc_wf_align {grow : Grow} {hb align r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb align r s = some (p, s')) : WF s' := by
  obtain ⟨bin, a1, ha, -, hbin, hmax, hS, ha1, hend, -, rfl⟩ := alloc_align_eq hwf.1 h
  have hl := (leftOf_spec (base := s.base) (C := s.heads bin) ha).1
  exact allocPostL_wf (k := r + align) hwf (by omega) hmax hbin (by omega) ha1 hend

/-- **The returned block is aligned to `32 · align` octets** in the address space. -/
theorem alloc_ptr_align {grow : Grow} {hb align r p : Nat} {s s' : State} (hbase : s.base ≠ 0)
    (h : alloc grow hb align r s = some (p, s')) : (p / 32) % align = 0 := by
  obtain ⟨bin, a1, ha, -, -, -, -, -, -, hp, -⟩ := alloc_align_eq hbase h
  have := (leftOf_spec (base := s.base) (C := s.heads bin) ha).2.2
  rw [hp, show (s.base + 32 * ((s.heads bin - s.base) / 32 + leftOf s.base (s.heads bin) align) + 32) / 32 =
    s.base / 32 + (s.heads bin - s.base) / 32 + leftOf s.base (s.heads bin) align + 1 by omega]
  exact this

/-- **`alloc`'s effect on the chunk list**, with any alignment, on a well-formed heap: the block
    `p` is the data of a chunk at `p − 32` cut from a free chunk C of S units, after a free left
    remainder of `lhs < align` units (none if `lhs = 0`); the allocated chunk has `r + 1` units, the
    right remainder, if any, is free, and every other chunk is as it was. -/
theorem alloc_chunks_align {grow : Grow} {hb align r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb align r s = some (p, s')) :
    ∃ pre post C S lhs, chunks s = pre ++ ⟨C, S, false⟩ :: post ∧ lhs < align ∧ r + align ≤ S ∧
      p - 32 = C + 32 * lhs ∧
      chunks s' = pre ++ leftChunk C lhs ++ ⟨p - 32, r + 1, true⟩ :: (remChunk (p - 32) r (S - lhs) ++ post) := by
  obtain ⟨bin, a1, ha, -, hbin, hmax, hS, -, -, hp, rfl⟩ := alloc_align_eq hwf.1 h
  have hl := (leftOf_spec (base := s.base) (C := s.heads bin) ha).1
  have hbin' : (findFirst s (binUp (r + align - 1 + 1))).or (findFirst s (binDown (r + align - 1 + 1))) =
      some bin := by rw [Nat.sub_add_cancel (by omega)]; exact hbin
  obtain ⟨-, -, -, -, ⟨pre, post, hcs⟩, hCb, hCal⟩ := bin_chunk hwf (by omega) hbin'
  have hA : s.base + 32 * ((s.heads bin - s.base) / 32) = s.heads bin := by omega
  have hpC : p - 32 = s.heads bin + 32 * leftOf s.base (s.heads bin) align := by rw [hp]; omega
  have htl := hwf.2.2.2.1
  unfold TilesOk at htl
  rw [hcs] at htl
  refine ⟨pre, post, _, _, _, hcs, hl, hS, hpC, ?_⟩
  rw [hpC]
  exact allocPostL_chunks hcs htl rfl hA (by omega)

/-- On a zeroed allocator, `alloc` runs on the state `init` leaves. -/
theorem alloc_after_init_align {grow : Grow} {hb align r : Nat} {s s0 : State} (hi : init grow hb s = some s0)
    (h0 : s0.base ≠ 0) : alloc grow hb align r s = alloc grow hb align r s0 := by
  unfold alloc
  rw [hi, init_self h0]

/-- **The first `alloc`**, with any alignment, on a zeroed allocator leaves a well-formed heap. -/
theorem alloc_wf_align_fresh {grow : Grow} {hb align r p : Nat} {s s' : State} (hb0 : hb ≠ 0)
    (hbal : hb % 32 = 0) (hfit : hb + 32 * maxSize < 2 ^ 32) (hs0 : s.base = 0) (hheads : ∀ b, s.heads b = 0)
    (hsec : ∀ p, s.secondary p = 0) (hpri : s.primary = 0) (h : alloc grow hb align r s = some (p, s')) :
    WF s' := by
  cases hi : init grow hb s with
  | none =>
    unfold alloc at h
    simp [hi] at h
  | some s0 =>
    have hw0 := (init_wf hb0 hbal hfit hs0 hheads hsec hpri hi).2
    rw [alloc_after_init_align hi hw0.1] at h
    exact alloc_wf_align hw0 h

/-- `alloc`, with any alignment, keeps the first chunk's `prev` zero. -/
theorem alloc_first_align {grow : Grow} {hb align r p : Nat} {s s' : State} (hwf : WF s) (h0 : FirstOk s)
    (h : alloc grow hb align r s = some (p, s')) : FirstOk s' := by
  obtain ⟨bin, a1, ha, -, hbin, hmax, hS, -, -, -, rfl⟩ := alloc_align_eq hwf.1 h
  have hl := (leftOf_spec (base := s.base) (C := s.heads bin) ha).1
  have hbin' : (findFirst s (binUp (r + align - 1 + 1))).or (findFirst s (binDown (r + align - 1 + 1))) =
      some bin := by rw [Nat.sub_add_cancel (by omega)]; exact hbin
  obtain ⟨-, -, -, -, -, hCb, hCal⟩ := bin_chunk hwf (by omega) hbin'
  unfold FirstOk at h0 ⊢
  rw [allocPostL_base, allocPostL_prev (s1 := { s with allocated := a1 }) rfl
    (show s.base + 32 * ((s.heads bin - s.base) / 32) = s.heads bin by omega) (by omega),
    ite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega)]
  exact h0

end Picoalloc
