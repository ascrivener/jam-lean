import JAM.Blake2b
import JAM.Codec

/-!
# The Fisher–Yates shuffle (GP v0.8.0 Appendix F)

ℱ over a numeric sequence (eq. `suffle`) and over a hash, through the sequence-from-hash
function 𝒬_l (eq. `sequencefromhash`).
-/

namespace JAM.Shuffle

/-- ℱ(**s**, **r**) (GP eq. `suffle`): take **s**_{r₀ mod l}, move **s**_{l−1} into its place, drop the
    last element and continue with **r**_{1…}. Recursion is on |**s**|, which shrinks by one each
    step; **r** must have at least |**s**| elements (missing ones are read as 0). -/
def shuffle {α : Type} : List α → List Nat → List α
  | [], _ => []
  | x :: xs, r =>
    let s := x :: xs
    let i := r.headD 0 % s.length
    let last := s.getLast (List.cons_ne_nil x xs)
    -- **s**' = **s** with index i replaced by **s**_{l−1}, then cut to its first l − 1 elements
    s.getD i x :: shuffle ((s.set i last).take xs.length) r.tail
termination_by s => s.length
decreasing_by simp

/-- 𝒬_l(h) (GP eq. `sequencefromhash`): element i is ℰ_4⁻¹ of octets 4i mod 32 … +4 of
    ℋ(h ⌢ ℰ_4(⌊i/8⌋)). -/
def seqFromHash (l : Nat) (h : ByteArray) : List Nat :=
  (List.range l).map fun i =>
    let block := Blake2b.hash256 (h ++ ⟨(PVM.Num.encodeLE 4 (i / 8)).toArray⟩)
    PVM.Num.decodeLE ((block.extract (4 * i % 32) (4 * i % 32 + 4)).toList)

/-- ℱ(**s**, h) = ℱ(**s**, 𝒬_{|**s**|}(h)) (GP eq. `sequencefromhash`). -/
def shuffleHash {α : Type} (s : List α) (h : ByteArray) : List α :=
  shuffle s (seqFromHash s.length h)

end JAM.Shuffle
