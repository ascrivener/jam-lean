import JAM.Fast.Blake2b
import JAM.Blake2b
import JAM.Codec

/-!
# The Fisher–Yates shuffle (GP v0.8.1 Appendix F)

$\mathcal{F}$ over a numeric sequence (eq. `suffle`) and over a hash, through the sequence-from-hash
function $\mathcal{Q}_l$ (eq. `sequencefromhash`).
-/

namespace JAM.Shuffle

/-- $\mathcal{F}(\mathbf{s}, \mathbf{r})$ (GP eq. `suffle`): take $\mathbf{s}_{r_0 \bmod l}$, move
    $\mathbf{s}_{l-1}$ into its place, drop the last element and continue with $\mathbf{r}_{1\ldots}$.
    Recursion is on $|\mathbf{s}|$, which shrinks by one each step; $\mathbf{r}$ must have at least
    $|\mathbf{s}|$ elements (missing ones are read as 0). -/
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

/-- $\mathcal{Q}_l(h)$ (GP eq. `sequencefromhash`): element $i$ is $\mathcal{E}_4^{-1}$ of octets
    $4i \bmod 32 \ldots {+4}$ of $\mathcal{H}(h \frown \mathcal{E}_4(\lfloor i/8 \rfloor))$. -/
def seqFromHash (l : Nat) (h : ByteArray) : List Nat :=
  (List.range l).map fun i =>
    let block := Blake2b.hash256 (h ++ ⟨(PVM.Num.encodeLE 4 (i / 8)).toArray⟩)
    PVM.Num.decodeLE ((block.extract (4 * i % 32) (4 * i % 32 + 4)).toList)

/-- $\mathcal{F}(\mathbf{s}, h) = \mathcal{F}(\mathbf{s}, \mathcal{Q}_{|\mathbf{s}|}(h))$
    (GP eq. `sequencefromhash`). -/
def shuffleHash {α : Type} (s : List α) (h : ByteArray) : List α :=
  shuffle s (seqFromHash s.length h)

end JAM.Shuffle
