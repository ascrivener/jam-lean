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

end Picoalloc
