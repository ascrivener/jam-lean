import Services.Picoalloc.Walk
import Services.Picoalloc.FreeLists

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
    Nat.sub_self, Nat.add_zero, Nat.div_one, Nat.mul_one, Nat.add_sub_cancel, Nat.sub_zero,
    show ∀ a b : Nat, a + b + 1 - a = b + 1 from fun a b => by omega]
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

theorem setHdr_prev_get {s : State} {a x p : Nat} :
    ((setHdr s a (fun h => { h with prev := p })).hdr x).prev = if x = a then p else (s.hdr x).prev := by
  unfold setHdr
  by_cases h : x = a
  · subst h; simp [upd_self]
  · simp [upd_ne _ _ h, h]

theorem register_prev_self {s : State} {n prev size : Nat} (hs : size ≠ 0) :
    ((register s n prev size).1.hdr n).prev = prev := by
  unfold register
  simp only [hs, ↓reduceIte, setBit_hdr]
  split
  · rw [setHdr_self]
  · unfold setHdr
    by_cases h : n = s.heads (binDown size)
    · rw [← h]; simp [upd_self]
    · simp [upd_ne _ _ h, upd_self]

theorem register_snd {s : State} {n prev size : Nat} :
    (register s n prev size).2 = if size = 0 then prev else size := by
  unfold register; split <;> rfl

/-- The `prev` fields `allocPost` leaves: C's as before, the rest's r + 1, the next chunk's the size
    before it; every other unchanged. -/
theorem allocPost_prev {s1 : State} {bin r S C T : Nat} (hC : s1.heads bin = C)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C) (hr : r + 1 ≤ S) (x : Nat) :
    ((allocPost s1 bin r S T).hdr x).prev =
      if x = C + 32 * S ∧ x < T then (if S - r - 1 = 0 then r + 1 else S - r - 1)
      else if x = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0 then r + 1
      else (s1.hdr x).prev := by
  unfold allocPost
  dsimp only
  rw [hC, hA, show C + 32 * (1 + r) + 32 * (S - r - 1) = C + 32 * S by omega]
  by_cases hx : x = C + 32 * S ∧ x < T
  · obtain ⟨rfl, hxT⟩ := hx
    simp only [hxT, ↓reduceIte, and_self, setHdr_prev_get, register_snd]
  · simp only [hx, ↓reduceIte]
    have hfin : ((if C + 32 * S < T then setHdr (register (registerAlloc (unregisterFirst s1 C bin) C
        (s1.hdr C).prev (r + 1)) (C + 32 * (1 + r)) (r + 1) (S - r - 1)).1 (C + 32 * S)
        (fun h => { h with prev := (register (registerAlloc (unregisterFirst s1 C bin) C (s1.hdr C).prev (r + 1))
          (C + 32 * (1 + r)) (r + 1) (S - r - 1)).2 }) else (register (registerAlloc (unregisterFirst s1 C bin) C
        (s1.hdr C).prev (r + 1)) (C + 32 * (1 + r)) (r + 1) (S - r - 1)).1).hdr x).prev =
        ((register (registerAlloc (unregisterFirst s1 C bin) C (s1.hdr C).prev (r + 1)) (C + 32 * (1 + r)) (r + 1)
          (S - r - 1)).1.hdr x).prev := by
      split
      · rename_i hT
        rw [setHdr_prev_get]
        have : x ≠ C + 32 * S := fun h => hx ⟨h, h ▸ hT⟩
        simp [this]
      · rfl
    rw [hfin]
    by_cases hx' : x = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0
    · obtain ⟨rfl, h0⟩ := hx'
      simp only [ne_eq, h0, not_false_eq_true, and_self, ↓reduceIte]
      exact register_prev_self h0
    · simp only [hx', ↓reduceIte]
      have hreg : ((register (registerAlloc (unregisterFirst s1 C bin) C (s1.hdr C).prev (r + 1))
          (C + 32 * (1 + r)) (r + 1) (S - r - 1)).1.hdr x).prev =
          ((registerAlloc (unregisterFirst s1 C bin) C (s1.hdr C).prev (r + 1)).hdr x).prev := by
        by_cases h0 : S - r - 1 = 0
        · rw [h0, register_zero]
        · exact (register_hdr_other (fun h => hx' ⟨h, h0⟩)).1
      rw [hreg, registerAlloc_hdr]
      split
      · rename_i h; subst h; rfl
      · exact unregisterFirst_hdr.1

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


theorem tiles_after {a top C S r : Nat} {pre post : List Chunk} (hr : r + 1 ≤ S)
    (h : Tiles a top (pre ++ ⟨C, S, false⟩ :: post)) :
    Tiles a top (pre ++ ⟨C, r + 1, true⟩ :: (remChunk C r S ++ post)) := by
  unfold remChunk
  by_cases h0 : S - r - 1 = 0
  · simp only [h0, ↓reduceIte, List.nil_append]
    have : S = r + 1 := by omega
    subst this
    exact Tiles.relabel h
  · simp only [h0, ↓reduceIte, List.singleton_append]
    have := Tiles.split (k := r + 1) (v := true) (w := false) (by omega) (by omega) h
    rw [show S - (r + 1) = S - r - 1 by omega] at this
    exact this

/-- Where the chunks around a chunk of a tiling lie. -/
theorem Tiles.around {a top C S : Nat} {u : Bool} {pre post : List Chunk}
    (h : Tiles a top (pre ++ ⟨C, S, u⟩ :: post)) :
    (∀ d ∈ pre, d.addr + 32 * d.size ≤ C) ∧ (∀ d ∈ post.head?, d.addr = C + 32 * S) ∧
      (∀ d ∈ post, C + 32 * S ≤ d.addr ∧ d.addr < top) ∧ (∀ d ∈ post.tail, C + 32 * S < d.addr) := by
  obtain ⟨m, h1, h2, h3, h4⟩ := Tiles.append.mp h
  simp only at h2 h3 h4
  subst h2
  refine ⟨fun d hd => (h1.mem_lt d hd).2.1, fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · cases post with
    | nil => simp at hd
    | cons e es => simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hd; subst hd; exact h4.1
  · have := h4.mem_lt d hd; omega
  · cases post with
    | nil => simp at hd
    | cons e es =>
      obtain ⟨he1, he2, he3⟩ := h4
      have := he3.mem_lt d hd
      omega

/-- **The free lists after `alloc`'s writes**: the bin's head `C` is gone, and the rest of the
    chunk, if any, is in its bin. -/
theorem allocPost_lists {s1 : State} {bin r S C T : Nat} {F : Nat → Nat → Prop}
    (hF : FreeLists s1 F) (hd : Disj F) (hbits : BitsOk s1.secondary s1.primary s1.heads)
    (hbin : bin < binCount) (hC : s1.heads bin = C) (hC0 : C ≠ 0)
    (hA : s1.base + 32 * ((C - s1.base) / 32) = C)
    (hN : S - r - 1 ≠ 0 → ∀ b, ¬ F b (C + 32 * (1 + r))) :
    FreeLists (allocPost s1 bin r S T) (fun b a => (F b a ∧ a ≠ C) ∨
        (S - r - 1 ≠ 0 ∧ b = binDown (S - r - 1) ∧ a = C + 32 * (1 + r))) ∧
      BitsOk (allocPost s1 bin r S T).secondary (allocPost s1 bin r S T).primary
        (allocPost s1 bin r S T).heads := by
  obtain ⟨p1, p2⟩ := pop_ok hF hd hbits hbin hC hC0
  have hd1 : Disj (fun b a => F b a ∧ a ≠ C) := fun b b' a h1 h2 => hd b b' a h1.1 h2.1
  unfold allocPost
  dsimp only
  rw [hC, hA]
  generalize unregisterFirst s1 C bin = s2 at p1 p2 ⊢
  generalize hs3 : registerAlloc s2 C (s1.hdr C).prev (r + 1) = s3
  have hn3 : ∀ x, (s3.hdr x).next = (s2.hdr x).next ∧ (s3.hdr x).prevL = (s2.hdr x).prevL := by
    intro x; rw [← hs3, registerAlloc_hdr]
    split
    · rename_i h; subst h; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have q1 : FreeLists s3 (fun b a => F b a ∧ a ≠ C) :=
    p1.congr (by rw [← hs3, registerAlloc_heads]) (fun x => (hn3 x).1) (fun x => (hn3 x).2)
  have q2 : BitsOk s3.secondary s3.primary s3.heads := by
    rw [← hs3, registerAlloc_secondary, registerAlloc_primary, registerAlloc_heads]; exact p2
  -- the last write changes a `prev` only
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
  by_cases hR : S - r - 1 = 0
  · rw [hR, register_zero]
    refine fin _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ⟨q1.iff (fun b a _ => ?_), q2⟩
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd rfl h.1)⟩
  · obtain ⟨u1, u2⟩ := push_ok (prev := r + 1) q1 hd1 q2 hR (toBin_lt false (Nat.min_le_right _ _))
      (by omega) (fun b h => hN hR b h.1)
    generalize register s3 (C + 32 * (1 + r)) (r + 1) (S - r - 1) = rs at u1 u2 ⊢
    refine fin _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) ⟨u1.iff (fun b a _ => ?_), u2⟩
    exact ⟨fun h => h.elim Or.inl (fun h => Or.inr ⟨hR, h⟩), fun h => h.elim Or.inl (fun h => Or.inr h.2)⟩

/-- The free chunks after `alloc`, against those before. -/
theorem free_after {pre post : List Chunk} {C S r a b : Nat}
    (hpre : ∀ d ∈ pre, d.addr < C) (hpost : ∀ d ∈ post, C + 32 * S ≤ d.addr) (hr : r + 1 ≤ S) :
    (((∃ c ∈ pre ++ ⟨C, S, false⟩ :: post, c.addr = a ∧ c.used = false ∧ binDown c.size = b) ∧ a ≠ C) ∨
      (S - r - 1 ≠ 0 ∧ b = binDown (S - r - 1) ∧ a = C + 32 * (1 + r))) ↔
    ∃ c ∈ pre ++ ⟨C, r + 1, true⟩ :: (remChunk C r S ++ post), c.addr = a ∧ c.used = false ∧
      binDown c.size = b := by
  constructor
  · rintro (⟨⟨c, hc, h1, h2, h3⟩, hne⟩ | ⟨hR, hb, ha⟩)
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, List.mem_append_left _ hc, h1, h2, h3⟩
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact absurd h1.symm hne
        · exact ⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hc)), h1, h2, h3⟩
    · refine ⟨⟨C + 32 * (r + 1), S - r - 1, false⟩, List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_append_left _ ?_)), ?_, rfl, hb.symm⟩
      · unfold remChunk; simp [hR]
      · show C + 32 * (r + 1) = a
        omega
  · rintro ⟨c, hc, h1, h2, h3⟩
    rcases List.mem_append.mp hc with hc | hc
    · exact Or.inl ⟨⟨c, List.mem_append_left _ hc, h1, h2, h3⟩, by have := hpre c hc; omega⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · simp at h2
      · rcases List.mem_append.mp hc with hc | hc
        · unfold remChunk at hc
          split at hc
          · simp at hc
          · rename_i hR
            simp only [List.mem_singleton] at hc
            subst hc
            refine Or.inr ⟨hR, h3.symm, ?_⟩
            have : C + 32 * (r + 1) = a := h1
            omega
        · refine Or.inl ⟨⟨c, List.mem_append_right _ (List.mem_cons_of_mem _ hc), h1, h2, h3⟩, ?_⟩
          have := hpost c hc; omega

/-- **`alloc` keeps the heap well-formed.** -/
theorem allocPost_wf {s : State} {r bin a1 : Nat} (hwf : WF s) (hmax : r + 1 ≤ maxSize)
    (hbin : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) = some bin)
    (hS : r + 1 ≤ wordSize (s.hdr (s.heads bin)).size) (ha1 : s.allocated ≤ a1)
    (hend : (s.heads bin - s.base) / 32 + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) ≤ a1) :
    WF (allocPost { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) s.top) := by
  obtain ⟨pre, post, hcs, hcs'⟩ := allocPost_chunks (a1 := a1) hwf hmax hbin hS
  obtain ⟨hbc, hne, ⟨rest, hl, hbl, hnd, hex⟩, hbS, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold SpaceOk at hspace
  generalize hs' : allocPost { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) s.top = s' at hcs' ⊢
  have hb' : s'.base = s.base := by rw [← hs', allocPost_base]
  have ha' : s'.allocated = a1 := by rw [← hs', allocPost_allocated]
  have ht' : s'.top = s.top := by unfold State.top; rw [hb']
  generalize hC : s.heads bin = C at *
  generalize hSd : wordSize (s.hdr C).size = S at *
  have hA : s.base + 32 * ((C - s.base) / 32) = C := by omega
  rw [hcs] at htiles hcoal hspace
  have htl := htiles
  refine ⟨by rw [hb']; exact hb0, by rw [hb']; exact hbal, by rw [ht']; exact hfit, ?_, ?_, ?_, ?_, ?_⟩
  · -- tiling
    unfold TilesOk; rw [hcs', hb', ht']
    exact tiles_after hS htl
  · -- coalesced
    unfold CoalOk; rw [hcs']
    unfold remChunk
    split
    · simp only [List.nil_append]; exact (Coalesced.split (C' := 0) (S' := 0) hcoal).2
    · simp only [List.singleton_append]; exact (Coalesced.split hcoal).1
  · -- prev links
    unfold PrevsOk; rw [hcs']
    unfold PrevsOk at hprev; rw [hcs] at hprev
    obtain ⟨hpre, hmid, hlink⟩ := PrevOk.append.mp hprev
    obtain ⟨hpa, hph, hpp, hpt⟩ := Tiles.around htl
    have hpv := fun x => allocPost_prev (s1 := { s with allocated := a1 }) (bin := bin) (r := r) (S := S)
      (T := s.top) (C := C) hC hA hS x
    rw [hs'] at hpv
    generalize s.top = T at hpv hpp
    -- every chunk before C, or after the one following it, keeps its prev
    have keep : ∀ d ∈ pre ++ post.tail, (s'.hdr d.addr).prev = (s.hdr d.addr).prev := by
      intro d hd
      rw [hpv]
      have hcases : d.addr < C ∨ C + 32 * S < d.addr := by
        rcases List.mem_append.mp hd with hd | hd
        · have := hpa d hd
          have := (htl.mem_lt d (List.mem_append_left _ hd)).2.2
          omega
        · exact Or.inr (hpt d hd)
      have e1 : ¬ (d.addr = C + 32 * S ∧ d.addr < T) := by omega
      have e2 : ¬ (d.addr = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0) := by omega
      rw [if_neg e1, if_neg e2]
    refine PrevOk.append.mpr ⟨hpre.congr (fun d hd => keep d (List.mem_append_left _ (List.mem_of_mem_tail hd))),
      ?_, fun x hx y hy => ?_⟩
    · -- from C on
      have hpostOk : PrevOk s' post := by
        cases post with
        | nil => trivial
        | cons e es => exact hmid.2.congr (fun d hd => keep d (List.mem_append_right _ (by simpa using hd)))
      have hhead : ∀ d ∈ post.head?, (s'.hdr d.addr).prev = (if S - r - 1 = 0 then r + 1 else S - r - 1) := by
        intro d hd
        rw [hpv]
        have hda := hph d hd
        have hlt : d.addr < T := (hpp d (by cases post <;> simp_all)).2
        rw [hda] at hlt ⊢
        rw [if_pos ⟨rfl, hlt⟩]
      unfold remChunk
      split
      · rename_i h0
        simp only [List.nil_append]
        cases post with
        | nil => trivial
        | cons e es =>
          refine ⟨?_, hpostOk⟩
          have := hhead e (by simp)
          rw [if_pos h0] at this
          exact this
      · rename_i h0
        simp only [List.singleton_append]
        refine ⟨?_, ?_⟩
        · have hx := hpv (C + 32 * (1 + r))
          have e1 : ¬ (C + 32 * (1 + r) = C + 32 * S ∧ C + 32 * (1 + r) < T) := by omega
          rw [if_neg e1, if_pos ⟨rfl, h0⟩, show C + 32 * (1 + r) = C + 32 * (r + 1) by omega] at hx
          rw [show ∀ a s u, Chunk.addr ⟨a, s, u⟩ = a from fun _ _ _ => rfl]
          exact hx
        · cases post with
          | nil => trivial
          | cons e es =>
            refine ⟨?_, hpostOk⟩
            have := hhead e (by simp)
            rw [if_neg h0] at this
            exact this
    · -- the link from the last chunk before C
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      rw [hpv]
      have e1 : ¬ (C = C + 32 * S ∧ C < T) := by omega
      have e2 : ¬ (C = C + 32 * (1 + r) ∧ S - r - 1 ≠ 0) := by omega
      rw [if_neg e1, if_neg e2]
      exact hlink x hx ⟨C, S, false⟩ (by simp)
  · -- free lists
    unfold ListsOk' at hlists ⊢
    rw [hcs] at hlists
    rw [hcs']
    obtain ⟨hpa, -, hpp, -⟩ := Tiles.around htl
    have hpre : ∀ d ∈ pre, d.addr < C := fun d hd => by
      have := hpa d hd
      have := (htl.mem_lt d (List.mem_append_left _ hd)).2.2
      omega
    have hpost : ∀ d ∈ post, C + 32 * S ≤ d.addr := fun d hd => (hpp d hd).1
    have hF0 : FreeLists { s with allocated := a1 } (fun b a => ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post,
        c.addr = a ∧ c.used = false ∧ binDown c.size = b) :=
      FreeLists.congr (s := s) (fun b hb => hlists.lists b hb) rfl (fun _ => rfl) (fun _ => rfl)
    have hd0 : Disj (fun b a => ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post,
        c.addr = a ∧ c.used = false ∧ binDown c.size = b) := by
      rintro b b' a ⟨c, hc, h1, -, h3⟩ ⟨d, hd, h1', -, h3'⟩
      have := htl.addr_inj c hc d hd (h1.trans h1'.symm)
      subst this; rw [← h3, ← h3']
    have hN : S - r - 1 ≠ 0 → ∀ b, ¬ ∃ c ∈ pre ++ ⟨C, S, false⟩ :: post,
        c.addr = C + 32 * (1 + r) ∧ c.used = false ∧ binDown c.size = b := by
      rintro hR b ⟨c, hc, h1, -, -⟩
      rcases List.mem_append.mp hc with hc | hc
      · have := hpre c hc; omega
      · rcases List.mem_cons.mp hc with rfl | hc
        · simp only at h1; omega
        · have := hpost c hc; omega
    obtain ⟨hL, hB⟩ := allocPost_lists (s1 := { s with allocated := a1 }) (T := s.top) hF0 hd0
      ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩ hbc hC hne hA hN
    rw [hs'] at hL hB
    obtain ⟨b1, b2, b3, b4⟩ := hB
    refine ⟨fun b hb => ?_, b1, b2, b3, b4⟩
    obtain ⟨l, h1, h2, h3, h4⟩ := hL b hb
    exact ⟨l, h1, h2, h3, fun a => (h4 a).trans (free_after hpre hpost hS)⟩
  · -- space
    unfold SpaceOk; rw [hcs', ha', hb']
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨h1, h2⟩ := hspace c (List.mem_append_left _ hc)
      exact ⟨fun hu => by have := h1 hu; omega, by omega⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · simp only [forall_const]
        split at hend <;> omega
      · rcases List.mem_append.mp hc with hc | hc
        · unfold remChunk at hc
          split at hc
          · simp at hc
          · rename_i h0
            simp only [List.mem_singleton] at hc
            subst hc
            simp only [Bool.false_eq_true, false_imp_iff, true_and]
            simp only [h0, ↓reduceIte] at hend
            omega
        · obtain ⟨h1, h2⟩ := hspace c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
          exact ⟨fun hu => by have := h1 hu; omega, by omega⟩

/-- **`alloc` keeps the heap well-formed** (an allocation of `r + 1` units, without alignment). -/
theorem alloc_wf {grow : Grow} {hb r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb 1 r s = some (p, s')) : WF s' := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, hbin, hmax, hS, ha1, hend, -, rfl⟩ := alloc1_eq h
  have ht : s.base + 32 * maxSize = s.top := rfl
  rw [ht]
  exact allocPost_wf hwf hmax hbin hS ha1 hend

end Picoalloc
