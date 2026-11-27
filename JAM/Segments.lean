import JAM.Merkle
import JAM.Codec
import JAM.Constants

/-!
# Constant-depth Merkle trees and segment justifications (GP v0.8.1 Appendix E, §14)

The constant-depth binary Merkle function and its page functions, from GP v0.8.1 Appendix E
("Constant-Depth Tree", `merklization.tex`):

* the constancy preprocessor $C$ (eq. E.7)
  — `constancy`;
* $\mathcal{M}(\mathbf{v}, H) = N(C(\mathbf{v}, H), H)$ (eq. `constantdepthmerkleroot`) — `cdRoot`;
* $\mathcal{J}_x(\mathbf{v}, i, H)$ (eq. `constantdepthsubtreemerklejust`) — `justify`;
* $\mathcal{L}_x(\mathbf{v}, i, H)$ (eq. `constantdepthsubtreemerkleleafpage`) — `page`;

built on the node function $N$ (eq. `merklenode`, `JAM.Merkle.node`) and the trace function $T$
(eq. after `merklenode`) — `trace`. From §14 (`work_packages_and_reports.tex`):

* the zero-padding function $\mathcal{P}_n$ (eq. `zeropadding`) — `zeroPad`;
* the paged-proofs function $P$ (eq. `pagedproofs`) — `pagedProofs`;
* the justifications $J_{\mathbf{r}}$ of the imported segments of a work-item (the equation defining
  $X$, $L_{\mathbf{r}}$, $S_{\mathbf{r}}$ and $J_{\mathbf{r}}$ in §14.4) use $\mathcal{J}_0$ —
  `justify 0`.

The paper does not state the verification side. §17.2 (`auditing.tex`) only says that a
justification "allows verification that each segment's hash is included in the referencing Merkle
root". We define it as the inverse of $T$: `foldPath` recomputes a root from a value at the bottom of a
path and the path $T$ gives (top to bottom); `verifySegment` checks one segment with its
$\mathcal{J}_0$ justification and `verifyPage` checks one page of $\mathcal{L}_x$ with its
$\mathcal{J}_x$ path. The readings are recorded
on each definition and in [`docs/upstream-candidates.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues).

The main results are `verifySegment_justify` (every segment verifies against $\mathcal{M}$ with its
$\mathcal{J}_0$ justification), `verifyPage_page_justify` (every page of $\mathcal{L}_x$ verifies
with its $\mathcal{J}_x$ path), `pagedProofs_verify` (each paged-proof segment of $P$ is the padded
encoding of a page and a path that verify), and `justify_zero_eq_page` (a $\mathcal{J}_0$
justification is the page's $\mathcal{J}_x$ path followed by the
trace within the page, as §14's note on deriving justifications from a single paged-proof says).
-/

namespace JAM.Segments

open JAM.Merkle (node nodePrefix)

/-- An octet sequence. -/
abbrev Blob := List UInt8

/-- The hash function $H$ applied to an octet list. -/
def hashL (H : ByteArray → ByteArray) (b : Blob) : Blob := (H ⟨b.toArray⟩).toList

/-- The prefix `$leaf` (GP Appendix E, the constancy preprocessor $C$). -/
def leafPrefix : Blob := "leaf".toUTF8.toList

/-- The zero hash $\zerohash$ (32 zero octets). -/
def zeroHash : Blob := List.replicate 32 0

/-- $H(\mathtt{\$leaf} \frown l)$: the hash of one data item in $C$ and $\mathcal{L}_x$ (GP
    Appendix E). -/
def leafHash (H : ByteArray → ByteArray) (l : Blob) : Blob := hashL H (leafPrefix ++ l)

/-- $\lceil \log_2(\max(1, n)) \rceil$ (GP Appendix E, used in $C$ and $\mathcal{J}_x$). -/
def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- $C(\mathbf{v}, H)$ (GP v0.8.1 Appendix E, the constancy preprocessor): each item hashed with the
    prefix `$leaf`, then padded with the zero hash to
    $2^{\lceil \log_2(\max(1, |\mathbf{v}|)) \rceil}$ items. -/
def constancy (H : ByteArray → ByteArray) (v : List Blob) : List Blob :=
  v.map (leafHash H) ++ List.replicate (2 ^ ceilLog2 v.length - v.length) zeroHash

/-- $\mathcal{M}(\mathbf{v}, H) = N(C(\mathbf{v}, H), H)$ (GP v0.8.1 eq. `constantdepthmerkleroot`): the constant-depth
    binary Merkle root. `JAM.Merkle.node` takes the length of its argument as fuel. -/
def cdRoot (H : ByteArray → ByteArray) (v : List Blob) : Blob :=
  let c := constancy H v
  node H c.length c

/-- $T(\mathbf{v}, i, H)$ (GP v0.8.1 Appendix E, the trace function after eq. `merklenode`): each
    opposite node $N(P^\bot(\mathbf{v}, i), H)$, from top to bottom, on the way to the item at index
    $i$. $P^\top$ is the half of $\mathbf{v}$ (split at $\lceil |\mathbf{v}|/2 \rceil$) containing
    $i$, $P^\bot$ the other half, and $P_I$ the offset of $P^\top$. `fuel` bounds the recursion
    depth; $|\mathbf{v}|$ suffices, since each level shortens $\mathbf{v}$. -/
def trace (H : ByteArray → ByteArray) : Nat → List Blob → Nat → List Blob
  | 0, _, _ => []
  | fuel + 1, v, i =>
    if v.length ≤ 1 then []
    else
      let h := (v.length + 1) / 2
      if i < h then
        let o := v.drop h
        node H o.length o :: trace H fuel (v.take h) i
      else
        let o := v.take h
        node H o.length o :: trace H fuel (v.drop h) (i - h)

/-- $\mathcal{J}_x(\mathbf{v}, i, H)$ (GP v0.8.1 eq. `constantdepthsubtreemerklejust`): the first
    $\max(0, \lceil \log_2(\max(1, |\mathbf{v}|)) \rceil - x)$ nodes of
    $T(C(\mathbf{v}, H), 2^x \cdot i, H)$, the Merkle path from the root to the $2^x$-leaf page with
    index $i$. Natural subtraction gives the $\max(0, \cdot)$.

    Reading: the paper types $i \in \mathbb{N}_{|\mathbf{v}|}$, although $i$ is a page index and only
    $i < \lceil |\mathbf{v}|/2^x \rceil$ gives a node of the tree ($P$ uses only those); for larger
    $i$ the trace runs off the end and the result has no meaning. -/
def justify (H : ByteArray → ByteArray) (x : Nat) (v : List Blob) (i : Nat) : List Blob :=
  let c := constancy H v
  (trace H c.length c (2 ^ x * i)).take (ceilLog2 v.length - x)

/-- $\mathcal{L}_x(\mathbf{v}, i, H)$ (GP v0.8.1 eq. `constantdepthsubtreemerkleleafpage`): the leaf
    hashes $H(\mathtt{\$leaf} \frown l)$ of the items
    $\mathbf{v}_{2^x \cdot i \ldots \min(2^x \cdot i + 2^x, |\mathbf{v}|)}$. The last page may be
    short. -/
def page (H : ByteArray → ByteArray) (x : Nat) (v : List Blob) (i : Nat) : List Blob :=
  ((v.drop (2 ^ x * i)).take (2 ^ x)).map (leafHash H)

/-- $\mathcal{P}_n(\mathbf{x})$ (GP v0.8.1 eq. `zeropadding`): $\mathbf{x}$ followed by zeros up to
    the next multiple of $n$, that is
    $\mathbf{x} \frown [0, 0, \ldots]_{((|\mathbf{x}| + n - 1) \bmod n) + 1 \ldots n}$. -/
def zeroPad (n : Nat) (x : Blob) : Blob :=
  x ++ List.replicate (n - ((x.length + n - 1) % n + 1)) 0

/-- $\mathcal{E}(\updownarrow\mathbf{j}, \updownarrow\mathbf{l})$ for two sequences of hashes
    (GP Appendix C, discriminator encoding). -/
def encodeProof (j l : List Blob) : Blob :=
  Codec.varSeq id j ++ Codec.varSeq id l

/-- $P(\mathbf{s})$ (GP v0.8.1 eq. `pagedproofs`): for each page index
    $i < \lceil |\mathbf{s}|/64 \rceil$, the segment
    $\mathcal{P}_{\mathsf{W}_G}(\mathcal{E}(\updownarrow\mathcal{J}_6(\mathbf{s}, i), \updownarrow\mathcal{L}_6(\mathbf{s}, i)))$.
    $H$ is Blake2b in the paper; it is a parameter here, like everywhere in `JAM.Merkle`. -/
def pagedProofs (H : ByteArray → ByteArray) (s : List Blob) : List Blob :=
  (List.range ((s.length + 63) / 64)).map fun i =>
    zeroPad Constants.Csegmentsize (encodeProof (justify H 6 s i) (page H 6 s i))

/-! ## Verification -/

/-- $H(\mathtt{\$node} \frown l \frown r)$: one inner node of $N$ (GP eq. `merklenode`). -/
def combine (H : ByteArray → ByteArray) (l r : Blob) : Blob := hashL H (nodePrefix ++ l ++ r)

/-- The root recomputed from the value `leaf` at the bottom of a path at index $i$, and the path
    (top to bottom, as $T$ gives it). With $k$ nodes below the head of the path, the value lies in
    the left subtree when $i < 2^k$, and the head is its right sibling; otherwise in the right
    subtree at index $i - 2^k$.

    Reading: the paper defines $T$ but not its inverse; this is the inverse for the perfect trees
    $C$ produces (every subtree at depth $k$ below the root has $2^{\text{depth} - k}$ leaves). -/
def foldPath (H : ByteArray → ByteArray) (leaf : Blob) (i : Nat) : List Blob → Blob
  | [] => leaf
  | s :: rest =>
    if i < 2 ^ rest.length then combine H (foldPath H leaf i rest) s
    else combine H s (foldPath H leaf (i - 2 ^ rest.length) rest)

/-- Whether segment `seg` at index $n$, with the justification $\mathbf{j}$ (as $\mathcal{J}_0$ gives
    it, GP §14.4 $J_{\mathbf{r}}$), is included in the constant-depth tree with root $r$:
    $n < 2^{|\mathbf{j}|}$ and the path folds the leaf hash $H(\mathtt{\$leaf} \frown \mathit{seg})$
    to $r$.

    Reading: the paper says only that justifications allow this check (GP §17.2). The depth of
    the tree is taken from the length of $\mathbf{j}$. -/
def verifySegment (H : ByteArray → ByteArray) (r : Blob) (n : Nat) (seg : Blob)
    (j : List Blob) : Bool :=
  decide (n < 2 ^ j.length) && foldPath H (leafHash H seg) n j == r

/-- The root of a page of leaf hashes $\mathbf{l}$ as a subtree: $\mathbf{l}$ padded with the zero
    hash to $2^w$ items, $w = x$ when the path is non-empty (a full $2^x$-leaf subtree, the last page
    padded), and $w = \lceil \log_2(\max(1, |\mathbf{l}|)) \rceil$ when it is empty (the page is the
    whole tree, as when $\lceil \log_2(\max(1, |\mathbf{v}|)) \rceil \leq x$). -/
def pageRoot (H : ByteArray → ByteArray) (x : Nat) (l path : List Blob) : Blob :=
  let w := if path.isEmpty then ceilLog2 l.length else x
  let c := l ++ List.replicate (2 ^ w - l.length) zeroHash
  node H c.length c

/-- Whether the page $\mathbf{l}$ of leaf hashes with index $i$ (as $\mathcal{L}_x$ gives it) and its
    path $\mathbf{p}$ (as $\mathcal{J}_x$ gives it) are consistent with the root $r$:
    $|\mathbf{l}| \leq 2^x$, $i < 2^{|\mathbf{p}|}$, and the path folds the page's subtree root
    (`pageRoot`) to $r$. This is the check a holder of one paged-proof segment of $P$ (GP eq.
    `pagedproofs`) can make. -/
def verifyPage (H : ByteArray → ByteArray) (r : Blob) (x i : Nat) (l p : List Blob) : Bool :=
  decide (l.length ≤ 2 ^ x) && decide (i < 2 ^ p.length) && foldPath H (pageRoot H x l p) i p == r

/-! ## Lemmas -/

theorem ceilLog2_spec (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split
  · simp; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

theorem ceilLog2_le {n d : Nat} (h : n ≤ 2 ^ d) : ceilLog2 n ≤ d := by
  unfold ceilLog2
  split
  · omega
  · rename_i hn
    have : Nat.log2 (n - 1) < d := by
      rw [Nat.log2_lt (by omega)]
      omega
    omega

theorem ceilLog2_pow (d : Nat) : ceilLog2 (2 ^ d) = d := by
  apply Nat.le_antisymm (ceilLog2_le (Nat.le_refl _))
  have h := ceilLog2_spec (2 ^ d)
  exact (Nat.pow_le_pow_iff_right (by decide)).mp h

theorem length_constancy (H : ByteArray → ByteArray) (v : List Blob) :
    (constancy H v).length = 2 ^ ceilLog2 v.length := by
  have := ceilLog2_spec v.length
  simp [constancy]; omega

theorem getElem_constancy (H : ByteArray → ByteArray) (v : List Blob) (i : Nat) (hi : i < v.length) :
    (constancy H v)[i]'(by rw [length_constancy]; have := ceilLog2_spec v.length; omega) =
      leafHash H v[i] := by
  simp only [constancy]
  rw [List.getElem_append_left (by simpa using hi)]
  simp

/-- $N$ ignores excess fuel: on a list of at most `f` and at most `g` items it gives the same result
    with either. -/
theorem node_fuel (H : ByteArray → ByteArray) :
    ∀ (f g : Nat) (v : List Blob), v.length ≤ f → v.length ≤ g → node H f v = node H g v := by
  intro f
  induction f with
  | zero =>
    intro g v hf _
    have : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases g <;> simp [node]
  | succ f ih =>
    intro g v hf hg
    match v, g with
    | [], g => cases g <;> simp [node]
    | [a], g => cases g <;> simp [node]
    | a :: b :: rest, 0 => simp at hg
    | a :: b :: rest, g + 1 =>
      simp only [node]
      simp only [List.length_cons] at hf hg ⊢
      rw [ih g, ih g] <;> simp <;> omega

/-- One step of $N$ on two or more items. -/
theorem node_succ (H : ByteArray → ByteArray) (f : Nat) (v : List Blob) (h : 2 ≤ v.length) :
    node H (f + 1) v =
      combine H (node H f (v.take ((v.length + 1) / 2))) (node H f (v.drop ((v.length + 1) / 2))) := by
  match v, h with
  | _ :: _ :: _, _ => rfl

/-- The length of $T$ on a perfect tree of $2^k$ items is $k$. -/
theorem length_trace (H : ByteArray → ByteArray) :
    ∀ (k f : Nat) (w : List Blob) (i : Nat), w.length = 2 ^ k → 2 ^ k ≤ f →
      (trace H f w i).length = k := by
  intro k
  induction k with
  | zero =>
    intro f w i hw _
    cases f with
    | zero => simp [trace]
    | succ f => simp [trace, hw]
  | succ k ih =>
    intro f w i hw hf
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    cases f with
    | zero => omega
    | succ f =>
      have hh : (w.length + 1) / 2 = 2 ^ k := by omega
      have hlen : ¬ w.length ≤ 1 := by omega
      simp only [trace, hlen, ↓reduceIte, hh]
      split
      · simp only [List.length_cons]
        rw [ih f _ _ (by simp; omega) (by omega)]
      · simp only [List.length_cons]
        rw [ih f _ _ (by simp; omega) (by omega)]

/-- The main lemma: on a perfect tree $\mathbf{w}$ of $2^k$ items, folding the first $k - j$ nodes
    of $T(\mathbf{w}, i)$ from the root of the $2^j$-item block containing $i$, at block index
    $\lfloor i / 2^j \rfloor$, gives $N(\mathbf{w})$. The case $j = 0$ is a single leaf; $j = k$ is
    the whole tree. -/
theorem foldPath_trace (H : ByteArray → ByteArray) :
    ∀ (k j f g : Nat) (w : List Blob) (i : Nat), j ≤ k → w.length = 2 ^ k → i < 2 ^ k →
      2 ^ k ≤ f → 2 ^ k ≤ g →
      foldPath H (node H (2 ^ j) ((w.drop (2 ^ j * (i / 2 ^ j))).take (2 ^ j))) (i / 2 ^ j)
        ((trace H f w i).take (k - j)) = node H g w := by
  intro k
  induction k with
  | zero =>
    intro j f g w i hj hw hi _ hg
    have hj0 : j = 0 := by omega
    have hi0 : i = 0 := by simp at hi; omega
    subst hj0 hi0
    simp only [Nat.pow_zero, Nat.div_one, Nat.mul_zero, List.drop_zero, Nat.sub_self,
      List.take_zero, foldPath]
    rw [List.take_of_length_le (by simp [hw])]
    exact node_fuel H _ _ _ (by simp [hw]) (by simp [hw]; omega)
  | succ k ih =>
    intro j f g w i hj hw hi hf hg
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    by_cases hjk : j = k + 1
    · subst hjk
      have : i / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hi
      simp only [this, Nat.mul_zero, List.drop_zero, Nat.sub_self, List.take_zero, foldPath]
      rw [List.take_of_length_le (by simp [hw])]
      exact node_fuel H _ _ _ (by simp [hw]) (by simp [hw]; omega)
    · have hj' : j ≤ k := by omega
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hh : (w.length + 1) / 2 = 2 ^ k := by omega
      have hlen : ¬ w.length ≤ 1 := by omega
      have hkj : k + 1 - j = (k - j) + 1 := by omega
      -- the node of w unfolds into its two halves
      have hnode : node H (g + 1) w =
          combine H (node H (2 ^ k) (w.take (2 ^ k))) (node H (2 ^ k) (w.drop (2 ^ k))) := by
        rw [node_succ H g w (by omega), hh]
        rw [node_fuel H g (2 ^ k), node_fuel H g (2 ^ k)] <;> simp <;> omega
      have h2j : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hjpos : 0 < 2 ^ j := Nat.two_pow_pos j
      have hrestlen : ∀ (u : List Blob) (i' : Nat), u.length = 2 ^ k →
          ((trace H f u i').take (k - j)).length = k - j := by
        intro u i' hu
        rw [List.length_take, length_trace H k f u i' hu (by omega)]; omega
      simp only [trace, hlen, ↓reduceIte, hh]
      rw [hnode]
      split
      · rename_i hik
        rw [hkj, List.take_succ_cons, foldPath, hrestlen _ _ (by simp; omega)]
        have hlt : i / 2 ^ j < 2 ^ (k - j) := by
          rw [Nat.div_lt_iff_lt_mul hjpos, Nat.mul_comm, ← h2j]; exact hik
        simp only [hlt, ↓reduceIte]
        have hblock : (w.drop (2 ^ j * (i / 2 ^ j))).take (2 ^ j) =
            ((w.take (2 ^ k)).drop (2 ^ j * (i / 2 ^ j))).take (2 ^ j) := by
          rw [List.drop_take, List.take_take]
          congr 1
          have : 2 ^ j * (i / 2 ^ j) + 2 ^ j ≤ 2 ^ k := by
            rw [h2j]
            have := Nat.mul_le_mul_left (2 ^ j) (show i / 2 ^ j + 1 ≤ 2 ^ (k - j) by omega)
            rw [Nat.mul_add, Nat.mul_one] at this; exact this
          omega
        rw [hblock, ih j f (2 ^ k) (w.take (2 ^ k)) i hj' (by simp; omega) hik (by omega)
          (Nat.le_refl _)]
        congr 1 <;> apply node_fuel <;> simp <;> omega
      · rename_i hik
        rw [hkj, List.take_succ_cons, foldPath, hrestlen _ _ (by simp; omega)]
        have hge : ¬ i / 2 ^ j < 2 ^ (k - j) := by
          rw [Nat.div_lt_iff_lt_mul hjpos, Nat.mul_comm, ← h2j]; exact hik
        simp only [hge, ↓reduceIte]
        have hdiv : i / 2 ^ j - 2 ^ (k - j) = (i - 2 ^ k) / 2 ^ j := by
          rw [h2j, Nat.sub_mul_div]
        have hblock : (w.drop (2 ^ j * (i / 2 ^ j))).take (2 ^ j) =
            ((w.drop (2 ^ k)).drop (2 ^ j * ((i - 2 ^ k) / 2 ^ j))).take (2 ^ j) := by
          rw [List.drop_drop]
          congr 2
          rw [← hdiv, Nat.mul_sub, ← h2j]
          have : 2 ^ k ≤ 2 ^ j * (i / 2 ^ j) := by
            rw [h2j]; exact Nat.mul_le_mul_left _ (by omega)
          omega
        rw [hdiv, hblock, ih j f (2 ^ k) (w.drop (2 ^ k)) (i - 2 ^ k) hj' (by simp; omega)
          (by omega) (by omega) (Nat.le_refl _)]
        congr 1 <;> apply node_fuel <;> simp <;> omega

/-! ## Correctness -/

/-- Every segment verifies against $\mathcal{M}$ with its $\mathcal{J}_0$ justification (GP v0.8.1
    eqs. `constantdepthmerkleroot`, `constantdepthsubtreemerklejust`; the check a guarantor or
    auditor makes on the imported segments and justifications $J_{\mathbf{r}}$ of §14.4). -/
theorem verifySegment_justify (H : ByteArray → ByteArray) (v : List Blob) (n : Nat)
    (hn : n < v.length) :
    verifySegment H (cdRoot H v) n v[n] (justify H 0 v n) = true := by
  have hlen := length_constancy H v
  have hspec := ceilLog2_spec v.length
  have htr : (trace H (constancy H v).length (constancy H v) n).length = ceilLog2 v.length :=
    length_trace H _ _ _ _ hlen (by omega)
  have hj : (justify H 0 v n).length = ceilLog2 v.length := by
    simp only [justify, Nat.pow_zero, Nat.one_mul, Nat.sub_zero, List.length_take, htr]; omega
  have key := foldPath_trace H (ceilLog2 v.length) 0 (constancy H v).length (constancy H v).length
    (constancy H v) n (Nat.zero_le _) hlen (by omega) (by omega) (by omega)
  simp only [Nat.pow_zero, Nat.div_one, Nat.one_mul, Nat.sub_zero] at key
  have hleaf : node H 1 (((constancy H v).drop n).take 1) = leafHash H v[n] := by
    have hc : n < (constancy H v).length := by omega
    rw [List.drop_eq_getElem_cons hc, List.take_succ_cons, List.take_zero]
    exact getElem_constancy H v n hn
  rw [hleaf] at key
  simp only [verifySegment, hj, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨by omega, ?_⟩
  simp only [justify, Nat.pow_zero, Nat.one_mul, Nat.sub_zero, cdRoot]
  exact key

/-- A slice of $C(\mathbf{v})$ is the leaf hashes of the slice of $\mathbf{v}$, padded with the zero
    hash. -/
theorem slice_constancy (H : ByteArray → ByteArray) (v : List Blob) (a b : Nat)
    (hab : a + b ≤ 2 ^ ceilLog2 v.length) :
    ((constancy H v).drop a).take b =
      ((v.drop a).take b).map (leafHash H) ++
        List.replicate (b - ((v.drop a).take b).length) zeroHash := by
  apply List.ext_getElem
  · have := ceilLog2_spec v.length
    simp only [List.length_take, List.length_drop, List.length_append, List.length_map,
      List.length_replicate, length_constancy]
    omega
  · intro m h1 h2
    have hmb : m < b := by simp only [List.length_take] at h1; omega
    simp only [List.getElem_take, List.getElem_drop, constancy]
    by_cases hm : a + m < v.length
    · rw [List.getElem_append_left (by simpa using hm)]
      rw [List.getElem_append_left (by simp; omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega)]
      rw [List.getElem_append_right (by simp; omega)]
      simp

/-- Every page of $\mathcal{L}_x$ verifies against $\mathcal{M}$ with its $\mathcal{J}_x$ path (GP
    v0.8.1 eqs. `constantdepthmerkleroot`, `constantdepthsubtreemerklejust`,
    `constantdepthsubtreemerkleleafpage`), for each page index $i < \lceil |\mathbf{v}|/2^x \rceil$. -/
theorem verifyPage_page_justify (H : ByteArray → ByteArray) (v : List Blob) (x i : Nat)
    (hi : 2 ^ x * i < v.length) :
    verifyPage H (cdRoot H v) x i (page H x v i) (justify H x v i) = true := by
  have hlen := length_constancy H v
  have hspec := ceilLog2_spec v.length
  have hxpos : 0 < 2 ^ x := Nat.two_pow_pos x
  have hpl : (page H x v i).length ≤ 2 ^ x := by
    simp only [page, List.length_map, List.length_take]; omega
  simp only [verifyPage, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases hd : x < ceilLog2 v.length
  · -- a proper subtree: the path has ⌈log₂ |v|⌉ − x nodes
    have htr : (trace H (constancy H v).length (constancy H v) (2 ^ x * i)).length =
        ceilLog2 v.length := length_trace H _ _ _ _ hlen (by omega)
    have hjl : (justify H x v i).length = ceilLog2 v.length - x := by
      simp only [justify, List.length_take, htr]; omega
    have hne : (justify H x v i).isEmpty = false := by
      cases h : justify H x v i with
      | nil => rw [h] at hjl; simp at hjl; omega
      | cons _ _ => rfl
    have h2 : 2 ^ ceilLog2 v.length = 2 ^ x * 2 ^ (ceilLog2 v.length - x) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hilt : i < 2 ^ (ceilLog2 v.length - x) := by
      have : 2 ^ x * i < 2 ^ x * 2 ^ (ceilLog2 v.length - x) := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    refine ⟨⟨hpl, by rw [hjl]; exact hilt⟩, ?_⟩
    have key := foldPath_trace H (ceilLog2 v.length) x (constancy H v).length
      (constancy H v).length (constancy H v) (2 ^ x * i) (by omega) hlen (by omega) (by omega)
      (by omega)
    rw [Nat.mul_div_cancel_left _ hxpos] at key
    have hroot : pageRoot H x (page H x v i) (justify H x v i) =
        node H (2 ^ x) (((constancy H v).drop (2 ^ x * i)).take (2 ^ x)) := by
      have hab : 2 ^ x * i + 2 ^ x ≤ 2 ^ ceilLog2 v.length := by
        rw [h2]
        have := Nat.mul_le_mul_left (2 ^ x) (show i + 1 ≤ 2 ^ (ceilLog2 v.length - x) by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; exact this
      simp only [pageRoot, hne, Bool.false_eq_true, ↓reduceIte]
      rw [slice_constancy H v _ _ hab]
      simp only [page, List.length_map]
      apply node_fuel <;> simp <;> omega
    rw [hroot]
    exact key
  · -- the page is the whole tree and the path is empty
    have hjnil : justify H x v i = [] := by
      simp only [justify]; rw [show ceilLog2 v.length - x = 0 by omega]; simp
    have hle : v.length ≤ 2 ^ x :=
      Nat.le_trans hspec (Nat.pow_le_pow_right (by decide) (by omega))
    have hi0 : i = 0 := by
      cases i with
      | zero => rfl
      | succ i => have := Nat.mul_le_mul_left (2 ^ x) (show 1 ≤ i + 1 by omega); omega
    subst hi0
    have hpage : page H x v 0 = v.map (leafHash H) := by
      simp [page, List.take_of_length_le hle]
    refine ⟨⟨hpl, by rw [hjnil]; simp⟩, ?_⟩
    rw [hjnil, hpage]
    simp [foldPath, pageRoot, cdRoot, constancy]

/-- The length of $P(\mathbf{s})$ is $\lceil |\mathbf{s}|/64 \rceil$ (GP v0.8.1 §14.4: "exactly
    $\lceil |\mathbf{s}|/64 \rceil$ paged-proof segments"). -/
theorem length_pagedProofs (H : ByteArray → ByteArray) (s : List Blob) :
    (pagedProofs H s).length = (s.length + 63) / 64 := by
  simp [pagedProofs]

/-- Each paged-proof segment of $P(\mathbf{s})$ (GP v0.8.1 eq. `pagedproofs`) is the padded encoding
    of a page of leaf hashes and a path that verify against $\mathcal{M}(\mathbf{s})$ (eq.
    `constantdepthmerkleroot`): the pages of $P$ are consistent with the segment root. -/
theorem pagedProofs_verify (H : ByteArray → ByteArray) (s : List Blob) (i : Nat)
    (hi : i < (pagedProofs H s).length) :
    ∃ l p, (pagedProofs H s)[i] = zeroPad Constants.Csegmentsize (encodeProof p l) ∧
      l = page H 6 s i ∧ p = justify H 6 s i ∧
      verifyPage H (cdRoot H s) 6 i l p = true := by
  refine ⟨page H 6 s i, justify H 6 s i, by simp [pagedProofs], rfl, rfl, ?_⟩
  apply verifyPage_page_justify
  rw [length_pagedProofs] at hi
  have : 64 * i < s.length := by omega
  simpa using this

/-! ## Deriving $\mathcal{J}_0$ from a paged proof (GP v0.8.1 §14.4) -/

/-- $T$ ignores excess fuel, like $N$ (`node_fuel`). -/
theorem trace_fuel (H : ByteArray → ByteArray) :
    ∀ (f g : Nat) (v : List Blob) (i : Nat), v.length ≤ f → v.length ≤ g →
      trace H f v i = trace H g v i := by
  intro f
  induction f with
  | zero =>
    intro g v i hf _
    have : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; cases g <;> simp [trace]
  | succ f ih =>
    intro g v i hf hg
    cases g with
    | zero =>
      have : v = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [trace]
    | succ g =>
      simp only [trace]
      split
      · rfl
      · split
        · rw [ih g] <;> simp <;> omega
        · rw [ih g] <;> simp <;> omega

/-- For $j \leq k$ and $i < 2^{k+1}$: $i$ lies in the left half exactly when its $2^j$-block does. -/
theorem lt_iff_block_lt {i j k : Nat} (hj : j ≤ k) :
    i < 2 ^ k ↔ 2 ^ j * (i / 2 ^ j) < 2 ^ k := by
  have hjpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have h2j : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add]; congr 1; omega
  constructor
  · intro h; exact Nat.lt_of_le_of_lt (Nat.mul_div_le i (2 ^ j)) h
  · intro h
    rw [h2j] at h ⊢
    have h' : i / 2 ^ j < 2 ^ (k - j) := Nat.lt_of_mul_lt_mul_left h
    rw [Nat.div_lt_iff_lt_mul hjpos] at h'
    rw [Nat.mul_comm]; exact h'

/-- For $j \leq k$ and $2^k \leq i$: the $2^j$-block index of $i - 2^k$. -/
theorem block_sub {i j k : Nat} (hj : j ≤ k) (hi : 2 ^ k ≤ i) :
    2 ^ j * ((i - 2 ^ k) / 2 ^ j) = 2 ^ j * (i / 2 ^ j) - 2 ^ k := by
  have hjpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have h2j : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add]; congr 1; omega
  have : i = (i - 2 ^ k) + 2 ^ j * 2 ^ (k - j) := by omega
  conv => rhs; rw [this]
  rw [Nat.add_mul_div_left _ _ hjpos, Nat.mul_add, ← h2j]; omega

/-- The first $k - j$ nodes of $T(\mathbf{w}, i)$ depend only on the $2^j$-block of $i$. -/
theorem trace_take_block (H : ByteArray → ByteArray) :
    ∀ (k j f : Nat) (w : List Blob) (i : Nat), j ≤ k → w.length = 2 ^ k → i < 2 ^ k →
      2 ^ k ≤ f →
      (trace H f w i).take (k - j) = (trace H f w (2 ^ j * (i / 2 ^ j))).take (k - j) := by
  intro k
  induction k with
  | zero => intro j f w i hj _ _ _; rw [show 0 - j = 0 by omega]; simp
  | succ k ih =>
    intro j f w i hj hw hi hf
    by_cases hjk : j = k + 1
    · subst hjk; simp
    · have hj' : j ≤ k := by omega
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hh : (w.length + 1) / 2 = 2 ^ k := by omega
      have hlen : ¬ w.length ≤ 1 := by omega
      have hkj : k + 1 - j = (k - j) + 1 := by omega
      have hiff := lt_iff_block_lt (i := i) hj'
      have hble : 2 ^ j * (i / 2 ^ j) ≤ i := Nat.mul_div_le i _
      simp only [trace, hlen, ↓reduceIte, hh, hkj]
      by_cases hik : i < 2 ^ k
      · have hb := hiff.mp hik
        simp only [hik, hb, ↓reduceIte, List.take_succ_cons]
        rw [ih j f _ i hj' (by simp; omega) hik (by omega)]
      · have hb : ¬ 2 ^ j * (i / 2 ^ j) < 2 ^ k := fun h => hik (hiff.mpr h)
        simp only [hik, hb, ↓reduceIte, List.take_succ_cons]
        rw [ih j f _ (i - 2 ^ k) hj' (by simp; omega) (by omega) (by omega), block_sub hj' (by omega)]

/-- $T(\mathbf{w}, i)$ splits at depth $k - j$: what follows its first $k - j$ nodes is the trace
    within the $2^j$-item block containing $i$. -/
theorem trace_drop_block (H : ByteArray → ByteArray) :
    ∀ (k j f : Nat) (w : List Blob) (i : Nat), j ≤ k → w.length = 2 ^ k → i < 2 ^ k →
      2 ^ k ≤ f →
      (trace H f w i).drop (k - j) =
        trace H (2 ^ j) ((w.drop (2 ^ j * (i / 2 ^ j))).take (2 ^ j)) (i % 2 ^ j) := by
  intro k
  induction k with
  | zero =>
    intro j f w i hj hw hi _
    have hj0 : j = 0 := by omega
    have hi0 : i = 0 := by simp at hi; omega
    subst hj0 hi0
    simp only [Nat.pow_zero] at hw
    cases f with
    | zero => simp [trace, hw]
    | succ f => simp [trace, hw]
  | succ k ih =>
    intro j f w i hj hw hi hf
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    by_cases hjk : j = k + 1
    · subst hjk
      have : i / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt hi
      simp only [this, Nat.mul_zero, List.drop_zero, Nat.sub_self, Nat.mod_eq_of_lt hi]
      rw [List.take_of_length_le (by simp [hw])]
      exact trace_fuel H _ _ _ _ (by omega) (by omega)
    · have hj' : j ≤ k := by omega
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hh : (w.length + 1) / 2 = 2 ^ k := by omega
      have hlen : ¬ w.length ≤ 1 := by omega
      have hkj : k + 1 - j = (k - j) + 1 := by omega
      have hiff := lt_iff_block_lt (i := i) hj'
      have hble : 2 ^ j * (i / 2 ^ j) ≤ i := Nat.mul_div_le i _
      have hjpos : 0 < 2 ^ j := Nat.two_pow_pos j
      have h2j : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← Nat.pow_add]; congr 1; omega
      have hblk : 2 ^ j * (i / 2 ^ j) + 2 ^ j ≤ 2 ^ (k + 1) := by
        have := Nat.lt_mul_div_succ i hjpos
        have : i / 2 ^ j < 2 ^ (k + 1 - j) := by
          rw [Nat.div_lt_iff_lt_mul hjpos, ← Nat.pow_add]
          rw [show k + 1 - j + j = k + 1 by omega]; exact hi
        have h2 : 2 ^ (k + 1) = 2 ^ j * 2 ^ (k + 1 - j) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [h2]
        have := Nat.mul_le_mul_left (2 ^ j) (show i / 2 ^ j + 1 ≤ 2 ^ (k + 1 - j) by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; exact this
      simp only [trace, hlen, ↓reduceIte, hh, hkj]
      by_cases hik : i < 2 ^ k
      · simp only [hik, ↓reduceIte, List.drop_succ_cons]
        rw [ih j f _ i hj' (by simp; omega) hik (by omega)]
        have hb := hiff.mp hik
        have hle : 2 ^ j * (i / 2 ^ j) + 2 ^ j ≤ 2 ^ k := by
          rw [h2j]
          have : i / 2 ^ j < 2 ^ (k - j) := by
            rw [Nat.div_lt_iff_lt_mul hjpos, Nat.mul_comm, ← h2j]; exact hik
          have := Nat.mul_le_mul_left (2 ^ j) (show i / 2 ^ j + 1 ≤ 2 ^ (k - j) by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; exact this
        rw [List.drop_take, List.take_take]
        congr 2
        omega
      · simp only [hik, ↓reduceIte, List.drop_succ_cons]
        rw [ih j f _ (i - 2 ^ k) hj' (by simp; omega) (by omega) (by omega),
          block_sub hj' (by omega), List.drop_drop]
        have hmod : (i - 2 ^ k) % 2 ^ j = i % 2 ^ j := by
          rw [h2j]
          exact Nat.sub_mul_mod (by rw [← h2j]; omega)
        rw [hmod]
        congr 3
        have : 2 ^ k ≤ 2 ^ j * (i / 2 ^ j) := by
          rw [← Nat.not_lt, ← hiff]; exact hik
        omega

/-- The leaves of the subtree a page and its path stand for: the page padded with the zero hash as
    in `pageRoot`. -/
def pageLeaves (x : Nat) (l path : List Blob) : List Blob :=
  let w := if path.isEmpty then ceilLog2 l.length else x
  l ++ List.replicate (2 ^ w - l.length) zeroHash

/-- A $\mathcal{J}_0$ justification is derived from one paged proof (GP v0.8.1 §14.4, the note after
    the definition of $J_{\mathbf{r}}$: "each justification can be derived through a single
    paged-proof"): $\mathcal{J}_0(\mathbf{v}, n)$ is the $\mathcal{J}_x$ path of page
    $\lfloor n / 2^x \rfloor$ followed by the trace of $n \bmod 2^x$ within that page's leaves
    (eqs. `constantdepthsubtreemerklejust`, `constantdepthsubtreemerkleleafpage`). -/
theorem justify_zero_eq_page (H : ByteArray → ByteArray) (v : List Blob) (x n : Nat)
    (hn : n < v.length) :
    justify H 0 v n =
      justify H x v (n / 2 ^ x) ++
        trace H (2 ^ x) (pageLeaves x (page H x v (n / 2 ^ x)) (justify H x v (n / 2 ^ x)))
          (n % 2 ^ x) := by
  have hlen := length_constancy H v
  have hspec := ceilLog2_spec v.length
  have hxpos : 0 < 2 ^ x := Nat.two_pow_pos x
  have htr : (trace H (constancy H v).length (constancy H v) n).length = ceilLog2 v.length :=
    length_trace H _ _ _ _ hlen (by omega)
  have hj0 : justify H 0 v n = trace H (constancy H v).length (constancy H v) n := by
    simp only [justify, Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
    exact List.take_of_length_le (by omega)
  rw [hj0]
  by_cases hd : x < ceilLog2 v.length
  · have hjl : (justify H x v (n / 2 ^ x)).length = ceilLog2 v.length - x := by
      simp only [justify, List.length_take]
      rw [length_trace H _ _ _ _ hlen (by omega)]; omega
    have hne : (justify H x v (n / 2 ^ x)).isEmpty = false := by
      cases h : justify H x v (n / 2 ^ x) with
      | nil => rw [h] at hjl; simp at hjl; omega
      | cons _ _ => rfl
    have hpre : justify H x v (n / 2 ^ x) =
        (trace H (constancy H v).length (constancy H v) n).take (ceilLog2 v.length - x) := by
      simp only [justify]
      rw [trace_take_block H (ceilLog2 v.length) x (constancy H v).length (constancy H v) n
        (by omega) hlen (by omega) (by omega)]
    have hsuf := trace_drop_block H (ceilLog2 v.length) x (constancy H v).length (constancy H v) n
      (Nat.le_of_lt hd) hlen (by omega) (by omega)
    have hab : 2 ^ x * (n / 2 ^ x) + 2 ^ x ≤ 2 ^ ceilLog2 v.length := by
      have h2 : 2 ^ ceilLog2 v.length = 2 ^ x * 2 ^ (ceilLog2 v.length - x) := by
        rw [← Nat.pow_add]; congr 1; omega
      have : n / 2 ^ x < 2 ^ (ceilLog2 v.length - x) := by
        rw [Nat.div_lt_iff_lt_mul hxpos, Nat.mul_comm, ← h2]; omega
      rw [h2]
      have := Nat.mul_le_mul_left (2 ^ x) (show n / 2 ^ x + 1 ≤ 2 ^ (ceilLog2 v.length - x) by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; exact this
    have hleaves : pageLeaves x (page H x v (n / 2 ^ x)) (justify H x v (n / 2 ^ x)) =
        ((constancy H v).drop (2 ^ x * (n / 2 ^ x))).take (2 ^ x) := by
      simp only [pageLeaves, hne, Bool.false_eq_true, ↓reduceIte]
      rw [slice_constancy H v _ _ hab]
      simp [page]
    rw [hleaves, ← hsuf, hpre, List.take_append_drop]
  · have hjnil : justify H x v (n / 2 ^ x) = [] := by
      simp only [justify]; rw [show ceilLog2 v.length - x = 0 by omega]; simp
    have hle : v.length ≤ 2 ^ x :=
      Nat.le_trans hspec (Nat.pow_le_pow_right (by decide) (by omega))
    have hq : n / 2 ^ x = 0 := Nat.div_eq_of_lt (by omega)
    have hr : n % 2 ^ x = n := Nat.mod_eq_of_lt (by omega)
    rw [hjnil, hq, hr]
    have hpage : page H x v 0 = v.map (leafHash H) := by
      simp [page, List.take_of_length_le hle]
    have hpl : pageLeaves x (page H x v 0) [] = constancy H v := by
      simp [pageLeaves, hpage, constancy]
    rw [hpl, List.nil_append]
    have : 2 ^ ceilLog2 v.length ≤ 2 ^ x := Nat.pow_le_pow_right (by decide) (by omega)
    apply trace_fuel <;> omega

end JAM.Segments
