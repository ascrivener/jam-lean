import JAM.Fast.Keccak
import JAM.Merkle
import JAM.Codec
import JAM.Params

/-!
# Recent history (GP v0.8.1 §7, `sec:recenthistory`)

The recent-blocks state $\beta = (\beta_H, \beta_B)$ (eq. `recentspec`): the last $\mathsf{H}$ blocks' header hashes,
state roots, accumulation-output super-peaks, timeslots and reported packages ($\beta_H$, eq.
`recenthistoryspec`), and the Accumulation Output Log $\beta_B$, a Merkle mountain belt of Keccak
hashes (eq. `accoutbeltspec`).

From Appendix E (`sec:mmr`) it needs the MMB append function $\mathcal{A}$ (eq. `mmrappend`) and the
super-peak function $\mathcal{M}_R$; the binary Merkle root $\mathcal{M}_B$ is `JAM.Merkle.root`.
-/

namespace JAM

/-- A Merkle mountain range or belt: a sequence of optional peaks $[\![ \mathbb{H}? ]\!]$ (GP Appendix E, `sec:mmr`).
    Peak $i$, when present, is the root of a tree of $2^i$ items. -/
abbrev MMR := List (Option (List UInt8))

namespace MMR

/-- $P(\mathbf{r}, l, n, H)$ of the append function (GP eq. `mmrappend`): carry $l$ up from peak $n$.
    $R(\mathbf{s}, i, v)$ is `List.set`. Each recursive call moves $n$ one peak further, so it ends at
    $|\mathbf{r}|$. -/
def place (H : ByteArray → ByteArray) (r : MMR) (l : List UInt8) (n : Nat) : MMR :=
  if h : n < r.length then
    match r[n] with
    | none => r.set n (some l)
    | some p => place H (r.set n none) (H ⟨(p ++ l).toArray⟩).toList (n + 1)
  else r ++ [some l]
termination_by r.length - n
decreasing_by simp only [List.length_set]; omega

/-- $\mathcal{A}(\mathbf{r}, l, H) = P(\mathbf{r}, l, 0, H)$ (GP eq. `mmrappend`). -/
def append (H : ByteArray → ByteArray) (r : MMR) (l : List UInt8) : MMR := place H r l 0

/-- $\mathcal{E}_M(\mathbf{b}) = \mathcal{E}(\updownarrow[\text{¿}x \mid x \orderedin \mathbf{b}])$ (GP eq. E.9, the
    MMR encoding function): the peaks with a length prefix, each with the optional
    discriminator. -/
def encode (b : MMR) : List UInt8 := Codec.varSeq (Codec.opt id) b

/-- The prefix `$peak`. -/
def peakPrefix : List UInt8 := "peak".toUTF8.toList

/-- $\mathcal{M}_R$ on the present peaks $\mathbf{h}$, given last-first: $\zerohash$ for none, $\mathbf{h}_0$ for one, and
    $\mathcal{H}_K(\mathtt{\$peak} \frown \mathcal{M}_R(\mathbf{h}_{\dots|\mathbf{h}|-1}) \frown \mathbf{h}_{|\mathbf{h}|-1})$ otherwise. -/
def superPeakRev : List (List UInt8) → List UInt8
  | [] => zeroHash
  | [x] => x
  | x :: rest => (Keccak.keccak256 ⟨(peakPrefix ++ superPeakRev rest ++ x).toArray⟩).toList

/-- $\mathcal{M}_R(\mathbf{b})$ (GP Appendix E, the MMR super-peak function), with $\mathbf{h}$ the present peaks of
    $\mathbf{b}$ in order. Always Keccak, as the paper defines it. -/
def superPeak (b : MMR) : List UInt8 := superPeakRev (b.filterMap id).reverse

end MMR

/-- One entry of $\beta_H$ (GP eq. `recenthistoryspec`): header hash $h$, state root $s$, accumulation-output
    super-peak $b$, timeslot $t$, and the reported packages $\mathbf{p}$ (work-package hash $\to$ segment root). -/
structure RecentBlock where
  headerHash : List UInt8
  stateRoot : List UInt8
  accRoot : List UInt8
  slot : Nat
  reported : OctetDict
  deriving Inhabited

/-- $\beta = (\beta_H, \beta_B)$ (GP eq. `recentspec`). -/
structure Recent where
  history : List RecentBlock
  belt : MMR
  deriving Inhabited

/-- $\mathcal{M}_B(\mathbf{s}, \mathcal{H}_K)$ with $\mathbf{s} = [\mathcal{E}_4(s) \frown \mathcal{E}(h) \mid (s, h) \in \theta']$
    (GP v0.8.1 eq. `accoutbeltdef`): the Keccak Merkle root of the block's accumulation outputs
    $\theta'$, which is appended to the belt. $\mathcal{E}(h)$ of a hash is the hash itself. -/
def accOutRoot (theta : List (Nat × List UInt8)) : List UInt8 :=
  Merkle.root Keccak.keccak256 (theta.map fun (s, h) => Codec.fixed 4 s ++ h)

/-- What the recent-history transition reads from the block and from accumulation. -/
structure HistoryInput where
  /-- $\mathcal{H}(\mathbf{H})$, the header hash. -/
  headerHash : List UInt8
  /-- $\mathbf{H}_R$, the parent block's state root. -/
  parentStateRoot : List UInt8
  /-- $\mathcal{M}_B(\mathbf{s}, \mathcal{H}_K)$: the root of the block's accumulation outputs (GP eq.
      `accoutbeltdef`; `JAM.importBlockWith` computes it with `JAM.accOutRoot`). -/
  accRoot : List UInt8
  /-- $\mathbf{H}_T$. -/
  slot : Nat
  /-- $(((g_\mathbf{r})_\mathbf{s})_p, ((g_\mathbf{r})_\mathbf{s})_e)$ for each $g \in \mathbf{E}_G$. -/
  reported : List (List UInt8 × List UInt8)

/-- $\beta_H^\dagger$ (GP eq. `correctlaststateroot`): $\beta_H$ with its last entry's state root set to $\mathbf{H}_R$. -/
def Recent.withParentRoot (h : List RecentBlock) (parentStateRoot : List UInt8) : List RecentBlock :=
  match h.getLast? with
  | none => h
  | some b => h.dropLast ++ [{ b with stateRoot := parentStateRoot }]

/-- $\beta'$ from $\beta_H^\dagger$ and $\beta_B$ (GP v0.8.1 §7): append the accumulation-output root to
    the belt with $\mathcal{A}$ and Keccak (eq. `accoutbeltdef`), and append the new block's entry to
    $\beta_H^\dagger$, keeping the last $\mathsf{H}$ (eq. `recenthistorydef`). The new entry's state root
    is $\zerohash$, and its reported packages are $\mathbf{p}$, given as `i.reported`. `i.parentStateRoot`
    is not read: it is already in $\beta_H^\dagger$. -/
def recentHistoryOf (params : Params) (dagger : List RecentBlock) (beltPre : MMR) (i : HistoryInput) :
    Recent :=
  let belt := MMR.append Keccak.keccak256 beltPre i.accRoot
  let entry : RecentBlock :=
    { headerHash := i.headerHash, stateRoot := zeroHash, accRoot := MMR.superPeak belt,
      slot := i.slot, reported := Std.ExtTreeMap.ofList i.reported }
  let h := dagger ++ [entry]
  { history := h.drop (h.length - params.recentHistoryLen), belt }

/-- The recent-history transition $\beta \mapsto \beta'$ (GP §7): correct the last state root to form
    $\beta_H^\dagger$ (eq. `correctlaststateroot`), then `JAM.recentHistoryOf` (eqs. `accoutbeltdef`,
    `recenthistorydef`). `JAM.importBlockWith` forms $\beta_H^\dagger$ itself and calls
    `JAM.recentHistoryOf` directly. -/
def recentHistory (params : Params) (pre : Recent) (i : HistoryInput) : Recent :=
  recentHistoryOf params (Recent.withParentRoot pre.history i.parentStateRoot) pre.belt i

end JAM
