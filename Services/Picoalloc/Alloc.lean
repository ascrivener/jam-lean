import Services.Picoalloc.Walk
import Services.Picoalloc.Lists
import Services.Picoalloc.Bits

/-!
# `alloc`, on a well-formed heap

With alignment one unit (every Rust allocation aligned to at most 32 octets), `alloc` on an
initialized heap is `alloc1`: take the first chunk C of a marked bin, of size S ≥ r + 1, grow the
allocated space if needed, pop C from its list, mark its first r + 1 units used, and push the
remaining S − r − 1 units, if any, as a free chunk.
-/

namespace Picoalloc

/-- `alloc` with alignment 1 on an initialized heap. -/
def alloc1 (grow : Grow) (r : Nat) (s : State) : Option (Nat × State) := do
  if r + 1 > maxSize then none
  let bin ← (findFirst s (binUp (r + 1))).orElse (fun _ => findFirst s (binDown (r + 1)))
  let C := s.heads bin
  let S := wordSize (s.hdr C).size
  if S < r + 1 then none
  let A := s.base + 32 * ((C - s.base) / 32)
  let rhs := S - r - 1
  let endOff := (C - s.base) / 32 + 1 + r + (if rhs = 0 then 0 else 1)
  let s ← if s.allocated < endOff then
      (if grow s.base endOff then some { s with allocated := endOff } else none)
    else some s
  let prev := (s.hdr C).prev
  let s := unregisterFirst s C bin
  let s := registerAlloc s A prev (r + 1)
  let (s, pr) := register s (A + 32 * (1 + r)) (r + 1) rhs
  let final := A + 32 * (1 + r) + 32 * rhs
  let s := if final < s.base + 32 * maxSize then setHdr s final (fun h => { h with prev := pr }) else s
  return (A + 32, s)

theorem alloc_one {grow : Grow} {hb r : Nat} {s : State} (hbase : s.base ≠ 0) :
    alloc grow hb 1 r s = alloc1 grow r s := by
  simp only [alloc, alloc1, init, hbase, ne_eq, not_false_eq_true, ↓reduceIte, show (1 : Nat) &&& 0 = 0 from rfl,
    Nat.sub_self, Nat.add_zero, Nat.div_one, Nat.mul_one, Nat.add_sub_cancel, Nat.sub_zero]
  simp [register]


/-- Every size up to `MAX_ALLOCATION_SIZE` falls in one of the 2432 bins. -/
theorem toBin_lt (u : Bool) {x : Nat} (hx : x ≤ maxSize) : toBin u x < binCount := by
  unfold toBin binCount mantissaBits
  unfold maxSize at hx
  split
  · omega
  split
  · omega
  rename_i h0 h1
  have hl : log2 x ≤ 25 := by
    unfold log2
    have := (Nat.log2_lt (n := x) (k := 26) h0).mpr (by omega)
    omega
  have hl7 : 7 ≤ log2 x := by
    unfold log2
    exact (Nat.le_log2 h0).mpr (by omega)
  dsimp only
  by_cases h25 : log2 x = 25
  · -- x = 2^25 exactly
    have hx25 : x = 33554432 := by
      have := (Nat.le_log2 (n := x) (k := 25) h0).mp (by unfold log2 at h25; omega)
      omega
    subst hx25
    cases u <;> decide
  · have hm : (x / 2 ^ (log2 x - 7)) % 2 ^ 7 < 128 := Nat.mod_lt _ (by decide)
    cases u <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;>
      (try split) <;> (try omega)
    all_goals
      have : (log2 x - 7 + 1) * 2 ^ 7 ≤ 18 * 128 := Nat.mul_le_mul_right _ (by omega)
      first
      | omega
      | (have := Nat.or_le_add (a := (log2 x - 7 + 1) * 2 ^ 7) (b := x / 2 ^ (log2 x - 7) % 2 ^ 7); omega)


/-- The state `alloc1` leaves, from the state `s1` after the space's growth, for the bin's first
    chunk of size S; `T` is the end of the address space (a parameter: unfolding a comparison with
    the literal end is slow). -/
def allocPost (s1 : State) (bin r S T : Nat) : State :=
  let C := s1.heads bin
  let A := s1.base + 32 * ((C - s1.base) / 32)
  let s2 := unregisterFirst s1 C bin
  let s3 := registerAlloc s2 A (s1.hdr C).prev (r + 1)
  let rs := register s3 (A + 32 * (1 + r)) (r + 1) (S - r - 1)
  if A + 32 * (1 + r) + 32 * (S - r - 1) < T
  then setHdr rs.1 (A + 32 * (1 + r) + 32 * (S - r - 1)) (fun h => { h with prev := rs.2 }) else rs.1

/-- **The chosen bin's first chunk** is a free chunk of the heap, of that bin, 32-aligned, at the
    front of the bin's list. -/
theorem bin_chunk {s : State} {r bin : Nat} (hwf : WF s) (hmax : r + 1 ≤ maxSize)
    (hbin : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = some bin) :
    bin < binCount ∧ s.heads bin ≠ 0 ∧
      (∃ rest, Linked s (s.heads bin) (s.heads bin :: rest) ∧ BackLinked s 0 (s.heads bin :: rest) ∧
        (s.heads bin :: rest).Nodup ∧
        ∀ a, a ∈ s.heads bin :: rest ↔ ∃ c ∈ chunks s, c.addr = a ∧ c.used = false ∧ binDown c.size = bin) ∧
      binDown (wordSize (s.hdr (s.heads bin)).size) = bin ∧
      (∃ pre post, chunks s = pre ++ ⟨s.heads bin, wordSize (s.hdr (s.heads bin)).size, false⟩ :: post) ∧
      s.base ≤ s.heads bin ∧ (s.heads bin - s.base) % 32 = 0 := by
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf
  unfold ListsOk' at hlists
  unfold TilesOk at htiles
  have hpw := hlists.primW
  -- the bin is marked
  have hmark : bin < binCount ∧ (s.secondary (bin / 64)).testBit (bin % 64) = true := by
    have hu : binUp (r + 1) < binCount := toBin_lt true (Nat.min_le_right _ _)
    have hd : binDown (r + 1) < binCount := toBin_lt false (Nat.min_le_right _ _)
    cases h1 : findFirst s (binUp (r + 1)) with
    | some b => rw [h1] at hbin; simp at hbin; subst hbin; exact findFirst_some hu hpw h1
    | none => rw [h1] at hbin; simp at hbin; exact findFirst_some hd hpw hbin
  obtain ⟨hbc, hbit⟩ := hmark
  have hne : s.heads bin ≠ 0 := (hlists.bits bin hbc).mp hbit
  obtain ⟨l, hl, hbl, hnd, hex⟩ := hlists.lists bin hbc
  obtain ⟨rest, rfl⟩ : ∃ rest, l = s.heads bin :: rest := by
    cases l with
    | nil => exact absurd ((hl.head).mpr rfl) hne
    | cons x xs => exact ⟨xs, by rw [hl.1]⟩
  -- the chunk
  obtain ⟨c, hc, hca, hcu, hcb⟩ := (hex (s.heads bin)).mp List.mem_cons_self
  have henc := chunks_hdr c hc
  rw [hca, hcu] at henc
  have hcS : c.size = wordSize (s.hdr (s.heads bin)).size := by rw [henc, wordSize_sizeWord]
  have hceq : c = ⟨s.heads bin, wordSize (s.hdr (s.heads bin)).size, false⟩ := by
    cases c; simp only at hca hcu hcS; subst hca hcu hcS; rfl
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hc
  have hal := htiles.aligned c hc
  rw [hca] at hal
  refine ⟨hbc, hne, ⟨rest, hl, hbl, hnd, hex⟩, by rw [← hcS]; exact hcb, ⟨pre, post, by rw [hsplit, hceq]⟩,
    hal.1, by omega⟩


theorem registerAlloc_hdr {s : State} {a prev size x : Nat} :
    (registerAlloc s a prev size).hdr x =
      if x = a then { s.hdr a with prev := prev, size := sizeWord size true } else s.hdr x := by
  unfold registerAlloc setHdr
  by_cases h : x = a
  · subst h; simp [upd_self]
  · simp [upd_ne _ _ h, h]

@[simp] theorem registerAlloc_heads {s : State} {a prev size : Nat} :
    (registerAlloc s a prev size).heads = s.heads := rfl
@[simp] theorem registerAlloc_base {s : State} {a prev size : Nat} :
    (registerAlloc s a prev size).base = s.base := rfl
@[simp] theorem registerAlloc_allocated {s : State} {a prev size : Nat} :
    (registerAlloc s a prev size).allocated = s.allocated := rfl
@[simp] theorem registerAlloc_secondary {s : State} {a prev size : Nat} :
    (registerAlloc s a prev size).secondary = s.secondary := rfl
@[simp] theorem registerAlloc_primary {s : State} {a prev size : Nat} :
    (registerAlloc s a prev size).primary = s.primary := rfl

theorem unregisterFirst_hdr {s : State} {c bin x : Nat} :
    ((unregisterFirst s c bin).hdr x).prev = (s.hdr x).prev ∧
      ((unregisterFirst s c bin).hdr x).size = (s.hdr x).size ∧
      ((unregisterFirst s c bin).hdr x).next = (s.hdr x).next := by
  unfold unregisterFirst
  dsimp only
  split
  · simp [unsetBit_hdr]
  · unfold setHdr
    by_cases h : x = (s.hdr c).next
    · subst h; simp [upd_self]
    · simp [upd_ne _ _ h]

@[simp] theorem unregisterFirst_base {s : State} {c bin : Nat} : (unregisterFirst s c bin).base = s.base := by
  unfold unregisterFirst; dsimp only; split <;> rfl
@[simp] theorem unregisterFirst_allocated {s : State} {c bin : Nat} :
    (unregisterFirst s c bin).allocated = s.allocated := by
  unfold unregisterFirst; dsimp only; split <;> rfl


/-- `register` writes only the new chunk's header and its successor's back link. -/
theorem register_hdr_other {s : State} {n prev size x : Nat} (hx : x ≠ n) :
    ((register s n prev size).1.hdr x).prev = (s.hdr x).prev ∧
      ((register s n prev size).1.hdr x).size = (s.hdr x).size ∧
      ((register s n prev size).1.hdr x).next = (s.hdr x).next := by
  unfold register
  split
  · simp
  · dsimp only
    simp only [setBit_hdr]
    split
    · rw [setHdr_other hx]; simp [upd_ne _ _ hx]
    · unfold setHdr
      by_cases h : x = s.heads (binDown size)
      · subst h; simp [upd_self, upd_ne _ _ hx]
      · simp [upd_ne _ _ h, upd_ne _ _ hx]

theorem register_hdr_self {s : State} {n prev size : Nat} (hs : size ≠ 0) (hh : s.heads (binDown size) ≠ n) :
    (register s n prev size).1.hdr n = ⟨prev, sizeWord size false, s.heads (binDown size), 0⟩ := by
  unfold register
  simp only [hs, ↓reduceIte, setBit_hdr]
  split
  · rw [setHdr_self]
  · rw [setHdr_other (Ne.symm hh), setHdr_self]

theorem register_size_self {s : State} {n prev size : Nat} (hs : size ≠ 0) :
    ((register s n prev size).1.hdr n).size = sizeWord size false := by
  unfold register
  simp only [hs, ↓reduceIte, setBit_hdr]
  split
  · rw [setHdr_self]
  · unfold setHdr
    by_cases h : n = s.heads (binDown size)
    · rw [← h]; simp [upd_self]
    · simp [upd_ne _ _ h, upd_self]

theorem register_zero {s : State} {n prev : Nat} : register s n prev 0 = (s, prev) := by
  simp [register]

@[simp] theorem register_base {s : State} {n prev size : Nat} : (register s n prev size).1.base = s.base := by
  unfold register; split
  · rfl
  · dsimp only; split <;> rfl
@[simp] theorem register_allocated {s : State} {n prev size : Nat} :
    (register s n prev size).1.allocated = s.allocated := by
  unfold register; split
  · rfl
  · dsimp only; split <;> rfl


theorem setHdr_prev_size {s : State} {a x p : Nat} :
    ((setHdr s a (fun h => { h with prev := p })).hdr x).size = (s.hdr x).size := by
  unfold setHdr
  by_cases h : x = a
  · subst h; simp [upd_self]
  · simp [upd_ne _ _ h]

@[simp] theorem allocPost_base {s1 : State} {bin r S T : Nat} : (allocPost s1 bin r S T).base = s1.base := by
  unfold allocPost; dsimp only; split
  · rw [setHdr_base, register_base, registerAlloc_base, unregisterFirst_base]
  · rw [register_base, registerAlloc_base, unregisterFirst_base]
@[simp] theorem allocPost_allocated {s1 : State} {bin r S T : Nat} :
    (allocPost s1 bin r S T).allocated = s1.allocated := by
  unfold allocPost; dsimp only; split
  · rw [setHdr_allocated, register_allocated, registerAlloc_allocated, unregisterFirst_allocated]
  · rw [register_allocated, registerAlloc_allocated, unregisterFirst_allocated]

/-- The size words `allocPost` leaves: the new front's and the rest's; every other unchanged. -/
theorem allocPost_size {s1 : State} {bin r S C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) (x : Nat) :
    ((allocPost s1 bin r S T).hdr x).size =
      if x = C then sizeWord (r + 1) true
      else if x = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0 then sizeWord (S - r - 1) false
      else (s1.hdr x).size := by
  unfold allocPost
  dsimp only
  rw [hC, hA]
  have hpost : ∀ t : State, ((if C + 32 * (1 + r) + 32 * (S - r - 1) < T then
      setHdr t (C + 32 * (1 + r) + 32 * (S - r - 1)) (fun h => { h with prev := (register (registerAlloc
        (unregisterFirst s1 C bin) C (s1.hdr C).prev (r + 1)) (C + 32 * (1 + r)) (r + 1) (S - r - 1)).2 })
      else t).hdr x).size = (t.hdr x).size := by
    intro t; split
    · exact setHdr_prev_size
    · rfl
  rw [hpost]
  by_cases hx : x = C
  · subst hx
    simp only [↓reduceIte]
    rw [(register_hdr_other (by omega)).2.1, registerAlloc_hdr]
    simp
  · simp only [hx, ↓reduceIte]
    by_cases hs0 : S - r - 1 = 0
    · simp only [hs0, register_zero, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
      rw [registerAlloc_hdr]; simp only [hx, ↓reduceIte]
      exact unregisterFirst_hdr.2.1
    · by_cases hx' : x = C + 32 * (1 + r)
      · subst hx'
        simp only [ne_eq, hs0, not_false_eq_true, and_self, ↓reduceIte]
        exact register_size_self hs0
      · simp only [hx', false_and, ↓reduceIte]
        rw [(register_hdr_other hx').2.1, registerAlloc_hdr]; simp only [hx, ↓reduceIte]
        exact unregisterFirst_hdr.2.1

/-- The remainder chunk after the allocated front, if any. -/
def remChunk (C r S : Nat) : List Chunk :=
  if S - r - 1 = 0 then [] else [⟨C + 32 * (r + 1), S - r - 1, false⟩]

/-- **`alloc` on the chunk list**: the bin's first chunk C, free with S ≥ r + 1 units, becomes an
    allocated chunk of r + 1 units followed by the free rest, if any; every other chunk is as it
    was. -/
theorem allocPost_chunks {s : State} {r bin a1 : Nat} (hwf : WF s) (hmax : r + 1 ≤ maxSize)
    (hbin : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = some bin)
    (hS : r + 1 ≤ wordSize (s.hdr (s.heads bin)).size) :
    ∃ pre post, chunks s = pre ++ ⟨s.heads bin, wordSize (s.hdr (s.heads bin)).size, false⟩ :: post ∧
      chunks (allocPost { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) s.top) =
        pre ++ ⟨s.heads bin, r + 1, true⟩ ::
          (remChunk (s.heads bin) r (wordSize (s.hdr (s.heads bin)).size) ++ post) := by
  obtain ⟨hbc, hne, ⟨rest, hl, hbl, hnd, hex⟩, hbS, ⟨pre, post, hcs⟩, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  generalize hC : s.heads bin = C at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  refine ⟨pre, post, hcs, ?_⟩
  have hA : s.base + 32 * ((C - s.base) / 32) = C := by omega
  have htl := htiles
  rw [hcs] at htl
  -- every other chunk's address lies outside C's span
  have hout : ∀ d ∈ pre ++ post, d.addr + 32 * d.size ≤ C ∨ C + 32 * S ≤ d.addr := by
    intro d hd
    have hm := htl.mem_lt
    obtain ⟨m, h1, h2, h3, h4⟩ := Tiles.append.mp htl
    simp only at h2 h3 h4
    rcases List.mem_append.mp hd with hd | hd
    · left
      have := h1.mem_lt d hd
      omega
    · right
      have := h4.mem_lt d hd
      omega
  have hpos : ∀ d ∈ pre ++ post, 0 < d.size := fun d hd => (htl.mem_lt d (by
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ hd
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hd))).2.2
  have hsz := fun x => allocPost_size (s1 := { s with allocated := a1 }) (bin := bin) (r := r) (S := S)
    (T := s.top) (C := C) hC hA x
  apply chunks_eq
  · -- the tiling
    unfold State.top at htl ⊢
    simp only [allocPost_base]
    unfold remChunk
    by_cases h0 : S - r - 1 = 0
    · simp only [h0, ↓reduceIte, List.nil_append]
      have : S = r + 1 := by omega
      subst this
      exact Tiles.relabel htl
    · simp only [h0, ↓reduceIte, List.singleton_append]
      have := Tiles.split (k := r + 1) (v := true) (w := false) (by omega) (by omega) htl
      rw [show S - (r + 1) = S - r - 1 by omega] at this
      exact this
  · -- the size words
    intro c hc
    rw [hsz]
    rcases List.mem_append.mp hc with hc | hc
    · have hne : c.addr ≠ C := by
        have := hout c (List.mem_append_left _ hc); have := hpos c (List.mem_append_left _ hc); omega
      have hne' : ¬ (c.addr = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0) := by
        have := hout c (List.mem_append_left _ hc); have := hpos c (List.mem_append_left _ hc); omega
      simp only [hne, hne', ↓reduceIte]
      exact chunks_hdr c (by rw [hcs]; exact List.mem_append_left _ hc)
    · rcases List.mem_cons.mp hc with rfl | hc
      · simp
      · rcases List.mem_append.mp hc with hc | hc
        · unfold remChunk at hc
          split at hc
          · simp at hc
          · rename_i h0
            simp only [List.mem_singleton] at hc
            subst hc
            have e2 : C + 32 * (r + 1) = C + 32 * (1 + r) := by omega
            have e1 : C + 32 * (1 + r) ≠ C := by omega
            simp only [e2, e1, ↓reduceIte, ne_eq, h0, not_false_eq_true, and_self]
        · have hne : c.addr ≠ C := by
            have := hout c (List.mem_append_right _ hc); have := hpos c (List.mem_append_right _ hc); omega
          have hne' : ¬ (c.addr = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0) := by
            have := hout c (List.mem_append_right _ hc); have := hpos c (List.mem_append_right _ hc); omega
          simp only [hne, hne', ↓reduceIte]
          exact chunks_hdr c (by rw [hcs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hc))


/-- **A successful `alloc1`'s shape**: a marked bin below 2432 whose first chunk has S ≥ r + 1
    units, a grown allocated space covering the new chunk, and the state `allocPost`. -/
theorem alloc1_eq {grow : Grow} {r p : Nat} {s s' : State} (h : alloc1 grow r s = some (p, s')) :
    ∃ bin a1, ((findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1)))) = some bin ∧
      r + 1 ≤ maxSize ∧ r + 1 ≤ wordSize (s.hdr (s.heads bin)).size ∧ s.allocated ≤ a1 ∧
      (s.heads bin - s.base) / 32 + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) ≤ a1 ∧
      p = s.base + 32 * ((s.heads bin - s.base) / 32) + 32 ∧
      s' = allocPost { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size)
        (s.base + 32 * maxSize) := by
  unfold alloc1 at h
  split at h
  · simp at h
  rename_i hmax
  simp only [Option.orElse_eq_or] at h
  cases hfb : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) with
  | none => simp [hfb] at h
  | some bin =>
    simp only [hfb, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp at h
    rename_i hS
    generalize hE : (s.heads bin - s.base) / 32 + 1 + r +
      (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) = E at h ⊢
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq, register_base, registerAlloc_base, unregisterFirst_base] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bin, E, rfl, by omega, by omega, by omega, Nat.le_of_eq hE, rfl, rfl⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq, register_base, registerAlloc_base, unregisterFirst_base] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨bin, s.allocated, rfl, by omega, by omega, Nat.le_refl _, by omega, rfl, rfl⟩



/-- **`alloc`'s effect on the heap** (alignment one unit, a well-formed heap): the returned block
    `p` is the data of what was a free chunk of S ≥ r + 1 units at `p − 32`; that chunk's front
    r + 1 units are now allocated, the rest, if any, free, and every other chunk is as it was. In
    particular the new block overlaps no block allocated before. -/
theorem alloc_chunks {grow : Grow} {hb r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb 1 r s = some (p, s')) :
    ∃ pre post S, chunks s = pre ++ ⟨p - 32, S, false⟩ :: post ∧ r + 1 ≤ S ∧
      chunks s' = pre ++ ⟨p - 32, r + 1, true⟩ :: (remChunk (p - 32) r S ++ post) := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, hbin, hmax, hS, -, -, hp, rfl⟩ := alloc1_eq h
  obtain ⟨-, -, -, -, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  have hpC : p - 32 = s.heads bin := by rw [hp]; omega
  obtain ⟨pre, post, h1, h2⟩ := allocPost_chunks (a1 := a1) hwf hmax hbin hS
  exact ⟨pre, post, _, by rw [hpC]; exact h1, hS, by rw [hpC]; exact h2⟩

end Picoalloc
