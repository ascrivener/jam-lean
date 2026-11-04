import PVM.Logic.ChunkBlob
import PVM.Logic.Code
import PVM.Theorems.HostIds

/-!
# Checking 𝔳_blob a stretch at a time

𝔳_blob (GP §A.1) walks the whole program from ı = 0, instruction by instruction. `CodeView.walk`
is k steps of that walk, each checking exactly what `vBlobAux` checks, and `vBlobAux_walk` says
𝔳_blob from ı is 𝔳_blob from where the k steps end: so the kernel can check a large program's
𝔳_blob as a chain of walks, each a declaration of its own.

`walkF` is the same walk with U and T read from bit masks (`validOpcodeBits`, `terminatorBits`,
checked against the tables for every octet), and `NatBlob.wview` the view of a blob reading a
stretch of the code from one number cut out of the blob once: both only make the kernel faster,
and `walkF_eq`, `wview_eq` say they agree with `walk` and `NatBlob.view`.
-/

namespace PVM

/-- U, the valid opcodes, as a bit mask (`isValidOpcode_bits`). -/
def validOpcodeBits : Nat := 3450873173393714245069311760876943481412597855754250132342037770404871

/-- T, the block-termination opcodes, as a bit mask (`isTerminator_bits`). -/
def terminatorBits : Nat := 1626779934493380067417503145553173186535055562438082563

theorem isValidOpcode_bits : ∀ n, n < 256 → isValidOpcode n = validOpcodeBits.testBit n := by
  decide +kernel

theorem isTerminator_bits : ∀ n, n < 256 → isTerminator n = terminatorBits.testBit n := by
  decide +kernel

namespace CodeView

/-- k steps of 𝔳_blob from ı, each checking what `vBlobAux` checks before it moves on: the index
    the steps end at, or `none` if a step fails or the walk reaches the end of the code. -/
def walk (V : CodeView) : Nat → Nat → Option Nat
  | 0, i => some i
  | k + 1, i =>
    if i > 0 && i == V.maskSize then none
    else if V.next i == V.maskSize && !isTerminator (V.zeta i) then none
    else if V.vInst i then V.walk k (V.next i)
    else none

/-- **𝔳_blob from ı is 𝔳_blob from where k steps of it end.** -/
theorem vBlobAux_walk (V : CodeView) :
    ∀ k i j f, V.walk k i = some j → k ≤ f → V.vBlobAux f i = V.vBlobAux (f - k) j := by
  intro k
  induction k with
  | zero => intro i j f h _; simp only [walk, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    intro i j f h hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [walk] at h
    rw [vBlobAux]
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rw [ite_eq_right (by assumption), ite_eq_right (by assumption), ite_eq_left (by assumption),
            ih _ _ _ h (by omega)]
          congr 1; omega
        · cases h

/-- 𝔳_blob at the end of the code. -/
theorem vBlobAux_end (V : CodeView) (f i : Nat) (hf : 0 < f) (h0 : 0 < i) (h : i = V.maskSize) :
    V.vBlobAux f i = true := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  rw [vBlobAux, ite_eq_left]
  subst h
  simp [h0]

/-- `walk`, with U and T read from their bit masks. -/
def walkF (V : CodeView) : Nat → Nat → Option Nat
  | 0, i => some i
  | k + 1, i =>
    if i > 0 && i == V.maskSize then none
    else if V.next i == V.maskSize && !terminatorBits.testBit (V.zeta i) then none
    else if V.maskSize == V.codeSize && decide (i < V.maskSize) && V.maskAt i &&
        validOpcodeBits.testBit (V.zeta i) then V.walkF k (V.next i)
    else none

theorem walkF_eq (V : CodeView) (hz : ∀ i, V.zeta i < 256) : ∀ k i, V.walkF k i = V.walk k i := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    rw [walkF, walk, ← isTerminator_bits _ (hz i), vInst, ← isValidOpcode_bits _ (hz i), ih]

end CodeView

/-- Whether a fact holds, read through a program's `CodeView` and jump table. -/
def CodeFact.holdsV (V : CodeView) (jt : Array Nat) : CodeFact → Bool
  | .instr i ins n => V.vInst i && V.decode i == some ins && V.next i == n
  | .blockStart n b => V.isBlockStart n == b
  | .jumpTableSize n => jt.size == n
  | .jumpEntry k t => jt.getD k 0 == t
  | .block s e => V.isBlockStart s && ((List.range (e - s - 1)).all fun k => !V.isBlockStart (s + 1 + k)) &&
      decide (V.blockCost s ≤ stepCostCap)

theorem CodeFact.holds_view (P : Program) (f : CodeFact) : f.holds P = f.holdsV P.view P.jumpTable := by
  cases f
  case block s e => simp only [CodeFact.holds, CodeFact.holdsV, Program.blockCost_view]; rfl
  all_goals rfl

theorem CodeFact.all_holds_of_view (P : Program) (V : CodeView) (hV : P.view = V) (fs : List CodeFact)
    (h : fs.all (CodeFact.holdsV V P.jumpTable) = true) : fs.all (·.holds P) = true := by
  subst hV
  simpa only [CodeFact.holds_view] using h

/-- `checkCode` from a parse, 𝔳_blob and the facts a chunk at a time. -/
theorem checkCode_of_chunks {p : ByteArray} {P : Program} {cs : List (List CodeFact)}
    (hp : Blob.parse? p = some P) (hv : P.vBlob = true) (hc : cs.all (fun c => c.all (·.holds P)) = true) :
    checkCode p cs.flatten = true := by
  simp only [checkCode, hp, hv, Bool.true_and, List.all_flatten]
  exact hc

/-! ## The host-call ids a program names -/

theorem OneImmOp.ofOpcode?_some {n : Nat} {o : OneImmOp} (h : OneImmOp.ofOpcode? n = some o) : n = 10 := by
  unfold OneImmOp.ofOpcode? at h
  split at h
  · rfl
  · cases h

/-- Only opcode 10 decodes to a one-immediate instruction. -/
theorem CodeView.zeta_of_decode_oneImm (V : CodeView) {i : Nat} {o : OneImmOp} {x : UInt64}
    (h : V.decode i = some (.oneImm o x)) : V.zeta i = 10 := by
  unfold CodeView.decode at h
  dsimp only at h
  split at h
  all_goals first
    | cases h
    | (simp only [Option.map_eq_some_iff] at h
       obtain ⟨a, ha, hb⟩ := h
       first
         | exact OneImmOp.ofOpcode?_some ha
         | cases hb)

/-- k indices from a: every `ecalli` among them names an id in `ids` (only opcode-10 octets at
    opcode positions are decoded). -/
def CodeView.hostScan (V : CodeView) (ids : List Nat) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, a =>
    (!(V.maskAt a && V.zeta a == 10) ||
      (match V.decode a with
       | some (.oneImm .ecalli x) => ids.contains x.toNat
       | _ => true)) && V.hostScan ids k (a + 1)

theorem CodeView.hostScan_sound (V : CodeView) (ids : List Nat) :
    ∀ k a, V.hostScan ids k a = true → ∀ i, a ≤ i → i < a + k → V.maskAt i = true →
      ∀ x, V.decode i = some (.oneImm .ecalli x) → x.toNat ∈ ids := by
  intro k
  induction k with
  | zero => intro a _ i h1 h2; omega
  | succ k ih =>
    intro a h i h1 h2 hm x hd
    rw [hostScan, Bool.and_eq_true] at h
    by_cases hia : i = a
    · subst hia
      have hz := V.zeta_of_decode_oneImm hd
      have := h.1
      simp only [hm, hz, beq_self_eq_true, Bool.and_true, Bool.not_true, Bool.false_or, hd] at this
      exact List.elem_iff.1 this
    · exact ih (a + 1) h.2 i (by omega) (by omega) hm x hd

/-- **The host-call ids a program names**, from what the code says at its opcode positions. -/
theorem Program.hostCallIds_sub (P : Program) (ids : List Nat)
    (h : ∀ i, i < P.code.size → P.view.maskAt i = true → ∀ x,
      P.view.decode i = some (.oneImm .ecalli x) → x.toNat ∈ ids) :
    ∀ n ∈ P.hostCallIds, n ∈ ids := by
  intro n hn
  simp only [Program.hostCallIds, List.mem_filterMap, List.mem_range] at hn
  obtain ⟨i, hi, hx⟩ := hn
  split at hx
  · rename_i hv
    split at hx
    · rename_i x hd
      cases hx
      have hm : P.view.maskAt i = true := by
        simp only [Program.vInst, Bool.and_eq_true] at hv
        exact hv.1.2
      exact h i hi hm x hd
    · cases hx
  · cases hx

theorem hostCallIdsOf_of {p : ByteArray} {P : Program} (h : Blob.parse? p = some P) :
    hostCallIdsOf p = P.hostCallIds := by
  unfold hostCallIdsOf; rw [h]

theorem jamHostCallIdsOf_of {b : ByteArray} {jb : JamBlob} (h : JamBlob.parse? b = some jb) :
    jamHostCallIdsOf b = hostCallIdsOf jb.code := by
  unfold jamHostCallIdsOf; rw [h]

/-- Covering a range by two. -/
theorem range_cover {Q : Nat → Prop} {a b c : Nat} (h1 : ∀ i, a ≤ i → i < b → Q i)
    (h2 : ∀ i, b ≤ i → i < c → Q i) : ∀ i, a ≤ i → i < c → Q i := by
  intro i ha hc
  by_cases hb : i < b
  · exact h1 i ha hb
  · exact h2 i (by omega) hc

namespace NatBlob

/-- `view`, reading the stretch of w code octets and w bitmask bits from index a from numbers cut
    out of N once. -/
def wview (N oc mb cLen a w : Nat) : CodeView where
  zeta i := if i < cLen then
      (if a ≤ i ∧ i < a + w then byte ((N >>> (8 * (oc + a))) % 2 ^ (8 * w)) (i - a) else byte N (oc + i))
    else 0
  maskExt i := if i < cLen then
      (if a ≤ i ∧ i < a + w then bit ((N >>> (mb + a)) % 2 ^ w) (i - a) else bit N (mb + i))
    else true
  maskAt i := if i < cLen then
      (if a ≤ i ∧ i < a + w then bit ((N >>> (mb + a)) % 2 ^ w) (i - a) else bit N (mb + i))
    else false
  codeSize := cLen
  maskSize := cLen

theorem wview_eq (N oc mb cLen a w : Nat) : wview N oc mb cLen a w = view N oc mb cLen := by
  have hz : ∀ i, (if a ≤ i ∧ i < a + w then byte ((N >>> (8 * (oc + a))) % 2 ^ (8 * w)) (i - a)
      else byte N (oc + i)) = byte N (oc + i) := by
    intro i
    split
    · rw [byte_window N (oc + a) w (oc + i) (by omega) (by omega)]
      congr 1; omega
    · rfl
  have hm : ∀ i, (if a ≤ i ∧ i < a + w then bit ((N >>> (mb + a)) % 2 ^ w) (i - a)
      else bit N (mb + i)) = bit N (mb + i) := by
    intro i
    split
    · rw [bit_window N (mb + a) w (mb + i) (by omega) (by omega)]
      congr 1; omega
    · rfl
  simp only [wview, view, hz, hm]

theorem view_zeta_lt (N oc mb cLen i : Nat) : (view N oc mb cLen).zeta i < 256 := by
  simp only [view]
  split
  · exact byte_lt _ _
  · decide

end NatBlob

end PVM
