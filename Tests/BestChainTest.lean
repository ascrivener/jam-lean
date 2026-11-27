import JAM.BestChain
import JAM.Theorems.BestChain

/-!
# Best-chain scenarios (`lake build Tests.BestChainTest`)

Hand-built block trees for GP v0.8.1 §19 (`JAM.BestChain`), with small numbers as header hashes.
There are no test vectors for §19; every expected value is worked out by hand from (19.1)–(19.4) and
the §17.3 disregard rule. Each `#guard` is evaluated when the file is elaborated, so building the
module runs the tests.

The base tree (slot in brackets, `T` for ticket-sealed):

```
0 [0] ── 1 [1] T ── 2 [2] ── 3 [3]          m(3) = 1, the longest chain
     └── 4 [4] T ── 5 [5] T                 m(5) = 2
```
-/

namespace JAM.Tests.BestChain

open JAM JAM.BestChain

/-- A known block: hash, parent, slot, 𝐓; audited and not disregarded unless changed. -/
def blk (h p s : Nat) (t : Bool) : BlockInfo Nat :=
  { hash := h, parent := p, slot := s, ticketed := t, audited := true, disregarded := false }

def base : List (BlockInfo Nat) :=
  [blk 0 0 0 false, blk 1 0 1 true, blk 2 1 2 false, blk 3 2 3 false, blk 4 0 4 true,
    blk 5 4 5 true]

/-- Replace the block with hash `h`. -/
def edit (bs : List (BlockInfo Nat)) (h : Nat) (f : BlockInfo Nat → BlockInfo Nat) :
    List (BlockInfo Nat) :=
  bs.map fun b => if b.hash = h then f b else b

def hashesOf (bs : List (BlockInfo Nat)) (b : Nat) : List Nat :=
  match lookup bs b with
  | some x => (ancestry bs x).map (·.hash)
  | none => []

def m (bs : List (BlockInfo Nat)) (b : Nat) : Nat :=
  match lookup bs b with
  | some x => metric bs x
  | none => 0

/-! ## 𝐀 and m -/

#guard hashesOf base 3 = [3, 2, 1, 0]
#guard hashesOf base 5 = [5, 4, 0]
-- The genesis-like block 0 is its own parent; P(H)_T < H_T fails, so 𝐀 stops there.
#guard hashesOf base 0 = [0]
#guard (base.map fun b => m base b.hash) = [0, 1, 1, 1, 1, 2]

/-! ## (19.4): ticketed blocks beat length -/

#guard bestHeads .head base 0 = [5]
#guard bestHead? .chain base 0 = some 5

/-! ## (19.2): an unaudited block -/

-- 5 is not audited: under either reading 5 is out, and every other block has m = 1.
def unaudited5 := edit base 5 fun b => { b with audited := false }
#guard bestHeads .head unaudited5 0 = [1, 2, 3, 4]
-- 4 is not audited but 5 is: the formula (head) accepts 5; the chain reading does not.
def unaudited4 := edit base 4 fun b => { b with audited := false }
#guard bestHeads .head unaudited4 0 = [5]
#guard bestHeads .chain unaudited4 0 = [1, 2, 3]
-- A finalized ancestor's 𝐔 is not asked under the chain reading.
def unaudited0 := edit base 0 fun b => { b with audited := false }
#guard bestHeads .chain unaudited0 1 = [1, 2, 3]

/-! ## §17.3: a disregarded block -/

-- 4 accumulates a report ⅓ of validators judge invalid: the whole fork through 4 is out.
def disputed4 := edit base 4 fun b => { b with disregarded := true }
#guard bestHeads .head disputed4 0 = [1, 2, 3]
-- Disregarding the finalized block leaves nothing acceptable (note v0.8.1-A22).
#guard bestHeads .head (edit base 0 fun b => { b with disregarded := true }) 0 = []

/-! ## (19.3): equivocation -/

-- 7 is a second block at slot 2: both 2 and 7, and every chain through them, are out; 1 is not.
def equiv := base ++ [blk 7 1 2 true]
#guard bestHeads .head equiv 0 = [5]
#guard bestHeads .head (edit equiv 5 fun b => { b with audited := false }) 0 = [1, 4]
-- Once 2 is finalized, its equivocation with 8 (another block at slot 2) no longer matters: 2 and
-- 3 are acceptable, both with m = 1.
def equivFinal := base ++ [blk 8 0 2 true]
#guard bestHeads .head equivFinal 2 = [2, 3]
#guard bestHeads .head equivFinal 0 = [5]

/-! ## (19.1): finality prunes other forks -/

#guard bestHeads .head base 1 = [1, 2, 3]
#guard bestHeads .head base 4 = [5]
#guard bestHeads .head base 3 = [3]
-- An unknown finalized block: nothing is acceptable.
#guard bestHeads .head base 99 = []
#guard bestHead? .head base 99 = none

/-! ## Order independence -/

#guard bestHeads .head base.reverse 0 = [5]
#guard bestHeads .head unaudited5.reverse 0 = [4, 3, 2, 1]
#guard bestHeads .head equiv.reverse 0 = [5]

/-! ## 𝐓 and the timeslot rule -/

#guard ticketedOf (.tickets []) = true
#guard ticketedOf (.keys []) = false
-- P(H)_T < H_T ∧ H_T·6 ≤ 𝒯.
#guard slotTimely 1 2 12 = true
#guard slotTimely 1 2 11 = false
#guard slotTimely 2 2 100 = false

/-! ## The theorems, instantiated -/

example : bestHeads .head base 0 ≠ [] :=
  bestHeads_ne_nil .head (f := blk 0 0 0 false) (by decide) rfl (by
    rw [ancestry_eq]; simp [lookup, base, blk])

end JAM.Tests.BestChain
