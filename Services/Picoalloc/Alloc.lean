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
    chunk of size S. -/
def allocPost (s1 : State) (bin r S : Nat) : State :=
  let C := s1.heads bin
  let A := s1.base + 32 * ((C - s1.base) / 32)
  let s2 := unregisterFirst s1 C bin
  let s3 := registerAlloc s2 A (s1.hdr C).prev (r + 1)
  let rs := register s3 (A + 32 * (1 + r)) (r + 1) (S - r - 1)
  if A + 32 * (1 + r) + 32 * (S - r - 1) < rs.1.base + 32 * maxSize
  then setHdr rs.1 (A + 32 * (1 + r) + 32 * (S - r - 1)) (fun h => { h with prev := rs.2 }) else rs.1

/-- **A successful `alloc1`'s shape**: a marked bin below 2432 whose first chunk has S ≥ r + 1
    units, a grown allocated space covering the new chunk, and the state `allocPost`. -/
theorem alloc1_eq {grow : Grow} {r p : Nat} {s s' : State} (h : alloc1 grow r s = some (p, s')) :
    ∃ bin a1, ((findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1)))) = some bin ∧
      r + 1 ≤ maxSize ∧ r + 1 ≤ wordSize (s.hdr (s.heads bin)).size ∧ s.allocated ≤ a1 ∧
      (s.heads bin - s.base) / 32 + 1 + r +
        (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) ≤ a1 ∧
      p = s.base + 32 * ((s.heads bin - s.base) / 32) + 32 ∧
      s' = allocPost { s with allocated := a1 } bin r (wordSize (s.hdr (s.heads bin)).size) := by
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
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bin, E, rfl, by omega, by omega, by omega, Nat.le_of_eq hE, rfl, rfl⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨bin, s.allocated, rfl, by omega, by omega, Nat.le_refl _, by omega, rfl, rfl⟩

end Picoalloc
