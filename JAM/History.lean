import JAM.Merkle
import JAM.Codec
import JAM.Params

/-!
# Recent history (GP v0.8.0 §7, `sec:recenthistory`)

The recent-blocks state β = (β_H, β_B) (eq. `recentspec`): the last 𝖧 blocks' header hashes,
state roots, accumulation-output super-peaks, timeslots and reported packages (β_H, eq.
`recenthistoryspec`), and the Accumulation Output Log β_B, a Merkle mountain belt of Keccak
hashes (eq. `accoutbeltspec`).

From Appendix E (`sec:mmr`) it needs the MMB append function 𝒜 (eq. `mmrappend`) and the
super-peak function ℳ_R; the binary Merkle root ℳ_B is `JAM.Merkle.root`.
-/

namespace JAM

/-- A Merkle mountain range or belt: a sequence of optional peaks ⟦ℍ?⟧ (GP Appendix E, `sec:mmr`).
    Peak i, when present, is the root of a tree of 2^i items. -/
abbrev MMR := List (Option (List UInt8))

namespace MMR

/-- The zero hash ℍ_0. -/
def zeroHash : List UInt8 := List.replicate 32 0

/-- P(**r**, l, n, H) of the append function (GP eq. `mmrappend`): carry l up from peak n.
    R(**s**, i, v) is `List.set`. Each recursive call moves n one peak further, so it ends at
    |**r**|. -/
def place (H : ByteArray → ByteArray) (r : MMR) (l : List UInt8) (n : Nat) : MMR :=
  if h : n < r.length then
    match r[n] with
    | none => r.set n (some l)
    | some p => place H (r.set n none) (H ⟨(p ++ l).toArray⟩).toList (n + 1)
  else r ++ [some l]
termination_by r.length - n
decreasing_by simp only [List.length_set]; omega

/-- 𝒜(**r**, l, H) = P(**r**, l, 0, H) (GP eq. `mmrappend`). -/
def append (H : ByteArray → ByteArray) (r : MMR) (l : List UInt8) : MMR := place H r l 0

/-- The prefix $peak. -/
def peakPrefix : List UInt8 := "peak".toUTF8.toList

/-- ℳ_R on the present peaks **h**, given last-first: ℍ_0 for none, **h**_0 for one, and
    ℋ_K($peak ⌢ ℳ_R(**h**_{…|**h**|−1}) ⌢ **h**_{|**h**|−1}) otherwise. -/
def superPeakRev : List (List UInt8) → List UInt8
  | [] => zeroHash
  | [x] => x
  | x :: rest => (Keccak.keccak256 ⟨(peakPrefix ++ superPeakRev rest ++ x).toArray⟩).toList

/-- ℳ_R(**b**) (GP Appendix E, the MMR super-peak function), with **h** the present peaks of
    **b** in order. Always Keccak, as the paper defines it. -/
def superPeak (b : MMR) : List UInt8 := superPeakRev (b.filterMap id).reverse

end MMR

/-- One entry of β_H (GP eq. `recenthistoryspec`): header hash h, state root s, accumulation-output
    super-peak b, timeslot t, and the reported packages **p** (work-package hash → segment root). -/
structure RecentBlock where
  headerHash : List UInt8
  stateRoot : List UInt8
  accRoot : List UInt8
  slot : Nat
  reported : OctetDict
  deriving Inhabited

/-- β = (β_H, β_B) (GP eq. `recentspec`). -/
structure Recent where
  history : List RecentBlock
  belt : MMR
  deriving Inhabited

/-- What the recent-history transition reads from the block and from accumulation. -/
structure HistoryInput where
  /-- ℋ(H), the header hash. -/
  headerHash : List UInt8
  /-- H_r, the parent block's state root. -/
  parentStateRoot : List UInt8
  /-- ℳ_B(**s**, ℋ_K): the root of the block's accumulation outputs (GP eq. `accoutbeltdef`;
      `JAM.accumulate` returns it as `AccResult.root`). -/
  accRoot : List UInt8
  /-- H_t. -/
  slot : Nat
  /-- (((g_w)_s)_h, ((g_w)_s)_e) for each g ∈ E_G. -/
  reported : List (List UInt8 × List UInt8)

/-- β_H^† (GP eq. `correctlaststateroot`): β_H with its last entry's state root set to H_r. -/
def Recent.withParentRoot (h : List RecentBlock) (parentStateRoot : List UInt8) : List RecentBlock :=
  match h.getLast? with
  | none => h
  | some b => h.dropLast ++ [{ b with stateRoot := parentStateRoot }]

/-- The recent-history transition β ↦ β' (GP §7): correct the last state root (eq.
    `correctlaststateroot`), append the accumulation-output root to the belt with 𝒜 and Keccak
    (eq. `accoutbeltdef`), and append the new block's entry, keeping the last 𝖧
    (eq. `recenthistorydef`). The new entry's state root is ℍ_0. -/
def recentHistory (params : Params) (pre : Recent) (i : HistoryInput) : Recent :=
  let dagger := Recent.withParentRoot pre.history i.parentStateRoot
  let belt := MMR.append Keccak.keccak256 pre.belt i.accRoot
  let entry : RecentBlock :=
    { headerHash := i.headerHash, stateRoot := MMR.zeroHash, accRoot := MMR.superPeak belt,
      slot := i.slot, reported := Std.ExtTreeMap.ofList i.reported }
  let h := dagger ++ [entry]
  { history := h.drop (h.length - params.recentHistoryLen), belt }

end JAM
