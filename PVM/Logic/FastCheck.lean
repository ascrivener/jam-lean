import PVM.Logic.ChunkBlob
import PVM.Logic.Code

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

theorem CodeFact.holds_view (P : Program) (f : CodeFact) : f.holds P = f.holdsV P.view P.jumpTable := by
  cases f <;> rfl

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
