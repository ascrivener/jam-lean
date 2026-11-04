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

/-- A fact about every octet, from facts about 16 at a time. -/
theorem forall_octet_of_ranges {Q : Nat → Prop} (h : ∀ k, k < 16 → ∀ m, m < 16 → Q (16 * k + m)) :
    ∀ n, n < 256 → Q n := by
  intro n hn
  have := h (n / 16) (by omega) (n % 16) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

theorem isValidOpcode_bits_0 : ∀ m, m < 16 → isValidOpcode (16 * 0 + m) = validOpcodeBits.testBit (16 * 0 + m) := by
  decide +kernel

theorem isValidOpcode_bits_1 : ∀ m, m < 16 → isValidOpcode (16 * 1 + m) = validOpcodeBits.testBit (16 * 1 + m) := by
  decide +kernel

theorem isValidOpcode_bits_2 : ∀ m, m < 16 → isValidOpcode (16 * 2 + m) = validOpcodeBits.testBit (16 * 2 + m) := by
  decide +kernel

theorem isValidOpcode_bits_3 : ∀ m, m < 16 → isValidOpcode (16 * 3 + m) = validOpcodeBits.testBit (16 * 3 + m) := by
  decide +kernel

theorem isValidOpcode_bits_4 : ∀ m, m < 16 → isValidOpcode (16 * 4 + m) = validOpcodeBits.testBit (16 * 4 + m) := by
  decide +kernel

theorem isValidOpcode_bits_5 : ∀ m, m < 16 → isValidOpcode (16 * 5 + m) = validOpcodeBits.testBit (16 * 5 + m) := by
  decide +kernel

theorem isValidOpcode_bits_6 : ∀ m, m < 16 → isValidOpcode (16 * 6 + m) = validOpcodeBits.testBit (16 * 6 + m) := by
  decide +kernel

theorem isValidOpcode_bits_7 : ∀ m, m < 16 → isValidOpcode (16 * 7 + m) = validOpcodeBits.testBit (16 * 7 + m) := by
  decide +kernel

theorem isValidOpcode_bits_8 : ∀ m, m < 16 → isValidOpcode (16 * 8 + m) = validOpcodeBits.testBit (16 * 8 + m) := by
  decide +kernel

theorem isValidOpcode_bits_9 : ∀ m, m < 16 → isValidOpcode (16 * 9 + m) = validOpcodeBits.testBit (16 * 9 + m) := by
  decide +kernel

theorem isValidOpcode_bits_10 : ∀ m, m < 16 → isValidOpcode (16 * 10 + m) = validOpcodeBits.testBit (16 * 10 + m) := by
  decide +kernel

theorem isValidOpcode_bits_11 : ∀ m, m < 16 → isValidOpcode (16 * 11 + m) = validOpcodeBits.testBit (16 * 11 + m) := by
  decide +kernel

theorem isValidOpcode_bits_12 : ∀ m, m < 16 → isValidOpcode (16 * 12 + m) = validOpcodeBits.testBit (16 * 12 + m) := by
  decide +kernel

theorem isValidOpcode_bits_13 : ∀ m, m < 16 → isValidOpcode (16 * 13 + m) = validOpcodeBits.testBit (16 * 13 + m) := by
  decide +kernel

theorem isValidOpcode_bits_14 : ∀ m, m < 16 → isValidOpcode (16 * 14 + m) = validOpcodeBits.testBit (16 * 14 + m) := by
  decide +kernel

theorem isValidOpcode_bits_15 : ∀ m, m < 16 → isValidOpcode (16 * 15 + m) = validOpcodeBits.testBit (16 * 15 + m) := by
  decide +kernel

/-- U as its bit mask, for every octet (16 octets to a theorem, so that no check is long). -/
theorem isValidOpcode_bits : ∀ n, n < 256 → isValidOpcode n = validOpcodeBits.testBit n :=
  forall_octet_of_ranges fun k hk =>
    match k, hk with
    | 0, _ => isValidOpcode_bits_0
    | 1, _ => isValidOpcode_bits_1
    | 2, _ => isValidOpcode_bits_2
    | 3, _ => isValidOpcode_bits_3
    | 4, _ => isValidOpcode_bits_4
    | 5, _ => isValidOpcode_bits_5
    | 6, _ => isValidOpcode_bits_6
    | 7, _ => isValidOpcode_bits_7
    | 8, _ => isValidOpcode_bits_8
    | 9, _ => isValidOpcode_bits_9
    | 10, _ => isValidOpcode_bits_10
    | 11, _ => isValidOpcode_bits_11
    | 12, _ => isValidOpcode_bits_12
    | 13, _ => isValidOpcode_bits_13
    | 14, _ => isValidOpcode_bits_14
    | 15, _ => isValidOpcode_bits_15
    | k + 16, hk => absurd hk (by omega)

theorem isTerminator_bits_0 : ∀ m, m < 16 → isTerminator (16 * 0 + m) = terminatorBits.testBit (16 * 0 + m) := by
  decide +kernel

theorem isTerminator_bits_1 : ∀ m, m < 16 → isTerminator (16 * 1 + m) = terminatorBits.testBit (16 * 1 + m) := by
  decide +kernel

theorem isTerminator_bits_2 : ∀ m, m < 16 → isTerminator (16 * 2 + m) = terminatorBits.testBit (16 * 2 + m) := by
  decide +kernel

theorem isTerminator_bits_3 : ∀ m, m < 16 → isTerminator (16 * 3 + m) = terminatorBits.testBit (16 * 3 + m) := by
  decide +kernel

theorem isTerminator_bits_4 : ∀ m, m < 16 → isTerminator (16 * 4 + m) = terminatorBits.testBit (16 * 4 + m) := by
  decide +kernel

theorem isTerminator_bits_5 : ∀ m, m < 16 → isTerminator (16 * 5 + m) = terminatorBits.testBit (16 * 5 + m) := by
  decide +kernel

theorem isTerminator_bits_6 : ∀ m, m < 16 → isTerminator (16 * 6 + m) = terminatorBits.testBit (16 * 6 + m) := by
  decide +kernel

theorem isTerminator_bits_7 : ∀ m, m < 16 → isTerminator (16 * 7 + m) = terminatorBits.testBit (16 * 7 + m) := by
  decide +kernel

theorem isTerminator_bits_8 : ∀ m, m < 16 → isTerminator (16 * 8 + m) = terminatorBits.testBit (16 * 8 + m) := by
  decide +kernel

theorem isTerminator_bits_9 : ∀ m, m < 16 → isTerminator (16 * 9 + m) = terminatorBits.testBit (16 * 9 + m) := by
  decide +kernel

theorem isTerminator_bits_10 : ∀ m, m < 16 → isTerminator (16 * 10 + m) = terminatorBits.testBit (16 * 10 + m) := by
  decide +kernel

theorem isTerminator_bits_11 : ∀ m, m < 16 → isTerminator (16 * 11 + m) = terminatorBits.testBit (16 * 11 + m) := by
  decide +kernel

theorem isTerminator_bits_12 : ∀ m, m < 16 → isTerminator (16 * 12 + m) = terminatorBits.testBit (16 * 12 + m) := by
  decide +kernel

theorem isTerminator_bits_13 : ∀ m, m < 16 → isTerminator (16 * 13 + m) = terminatorBits.testBit (16 * 13 + m) := by
  decide +kernel

theorem isTerminator_bits_14 : ∀ m, m < 16 → isTerminator (16 * 14 + m) = terminatorBits.testBit (16 * 14 + m) := by
  decide +kernel

theorem isTerminator_bits_15 : ∀ m, m < 16 → isTerminator (16 * 15 + m) = terminatorBits.testBit (16 * 15 + m) := by
  decide +kernel

/-- T as its bit mask, for every octet (16 octets to a theorem, so that no check is long). -/
theorem isTerminator_bits : ∀ n, n < 256 → isTerminator n = terminatorBits.testBit n :=
  forall_octet_of_ranges fun k hk =>
    match k, hk with
    | 0, _ => isTerminator_bits_0
    | 1, _ => isTerminator_bits_1
    | 2, _ => isTerminator_bits_2
    | 3, _ => isTerminator_bits_3
    | 4, _ => isTerminator_bits_4
    | 5, _ => isTerminator_bits_5
    | 6, _ => isTerminator_bits_6
    | 7, _ => isTerminator_bits_7
    | 8, _ => isTerminator_bits_8
    | 9, _ => isTerminator_bits_9
    | 10, _ => isTerminator_bits_10
    | 11, _ => isTerminator_bits_11
    | 12, _ => isTerminator_bits_12
    | 13, _ => isTerminator_bits_13
    | 14, _ => isTerminator_bits_14
    | 15, _ => isTerminator_bits_15
    | k + 16, hk => absurd hk (by omega)

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

/-! ## A block's cost, a few transitions at a time -/

namespace CodeView.Sim

/-- k transitions of 𝔛 that each continue (`.inl`), or `none`. -/
def steps (V : CodeView) : Nat → SimState → Option SimState
  | 0, x => some x
  | k + 1, x => match transition V x with
    | some (.inl y) => steps V k y
    | _ => none

/-- **𝔛 from x is 𝔛 from where k continuing transitions lead.** -/
theorem run_steps (V : CodeView) : ∀ k x y f, steps V k x = some y → run V (f + k) x = run V f y := by
  intro k
  induction k with
  | zero => intro x y f h; simp only [steps, Option.some.injEq] at h; subst h; rfl
  | succ k ih =>
    intro x y f h
    rw [steps] at h
    rw [show f + (k + 1) = (f + k) + 1 by omega, run]
    split at h
    · rename_i x' hx
      rw [hx]
      exact ih x' y f h
    · cases h

/-- 𝔛 stops at a final state. -/
theorem run_final (V : CodeView) (x : SimState) (f : Nat) (h : transition V x = some (.inr x)) :
    run V (f + 1) x = some x := by
  rw [run, h]

end CodeView.Sim

theorem CodeView.blockCost_of_run (V : CodeView) (s : Nat) (z : SimState)
    (h : CodeView.Sim.run V (CodeView.Sim.fuel V s) (Sim.init s) = some z) :
    V.blockCost s = max (z.cycle - 3) 1 := by
  simp [CodeView.blockCost, CodeView.blockCost?, h]

/-- `followsTerminator`, with T read from its bit mask. -/
def CodeView.followsTerminatorF (V : CodeView) (n : Nat) : Bool :=
  (List.range 25).any fun d =>
    decide (d + 1 ≤ n) &&
      (let m := n - 1 - d
       decide (m < V.codeSize) && V.maskAt m && terminatorBits.testBit (V.zeta m) && V.next m == n)

/-- `isBlockStart`, testing the cheap half first and reading U and T from their bit masks. -/
def CodeView.isBlockStartF (V : CodeView) (n : Nat) : Bool :=
  (decide (n < V.codeSize) && V.maskAt n && validOpcodeBits.testBit (V.zeta n)) &&
    (n == 0 || V.followsTerminatorF n)

theorem CodeView.isBlockStartF_eq (V : CodeView) (hz : ∀ i, V.zeta i < 256) (n : Nat) :
    V.isBlockStartF n = V.isBlockStart n := by
  have hf : V.followsTerminatorF n = V.followsTerminator n := by
    simp only [followsTerminatorF, followsTerminator]
    congr 1
    funext d
    rw [isTerminator_bits _ (hz _)]
  rw [isBlockStartF, isBlockStart, hf, isInstrStart, isValidOpcode_bits _ (hz n), Bool.and_comm]

/-- No block starts at a, …, a + len − 1. -/
def CodeView.noStartsF (V : CodeView) (a len : Nat) : Bool :=
  (List.range len).all fun k => !V.isBlockStartF (a + k)

theorem CodeView.noStartsF_sound (V : CodeView) (hz : ∀ i, V.zeta i < 256) (a len : Nat)
    (h : V.noStartsF a len = true) : ∀ k, a ≤ k → k < a + len → V.isBlockStart k = false := by
  intro k h1 h2
  simp only [noStartsF, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  have := h (k - a) (by omega)
  rwa [show a + (k - a) = k by omega, isBlockStartF_eq V hz] at this

/-- The block-start part of a `.block` fact. -/
def CodeFact.blockStartsV (V : CodeView) (s e : Nat) : Bool :=
  V.isBlockStart s && ((List.range (e - s - 1)).all fun k => !V.isBlockStart (s + 1 + k))

theorem CodeFact.holds_block (P : Program) (s e : Nat) :
    (CodeFact.block s e).holds P = (CodeFact.blockStartsV P.view s e && decide (P.view.blockCost s ≤ stepCostCap)) := by
  simp only [CodeFact.holds, CodeFact.blockStartsV, Program.blockCost_view]
  rfl

/-- The block-start part of a `.block` fact, from s ∈ ϖ and no starts in (s, e). -/
theorem CodeFact.blockStartsV_of (V : CodeView) (s e : Nat) (hs : V.isBlockStart s = true)
    (hno : ∀ k, s + 1 ≤ k → k < e → V.isBlockStart k = false) :
    CodeFact.blockStartsV V s e = true := by
  simp only [CodeFact.blockStartsV, hs, Bool.true_and, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  intro k hk
  exact hno (s + 1 + k) (by omega) (by omega)

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

/-- `view` of a blob of chunks, reading the code from chunks kc … kc + mc − 1 and the bitmask
    from chunks km … km + mm − 1 alone, wherever they hold it (`cview_eq`). A check then works
    on a few small numbers and never builds the whole blob. -/
def cview (cs : List Nat) (oc mb cLen kc mc km mm : Nat) : CodeView where
  zeta i := if i < cLen then
      (if 1024 * kc ≤ oc + i ∧ oc + i < 1024 * (kc + mc) then
        byte (ofChunks ((cs.drop kc).take mc)) (oc + i - 1024 * kc)
      else byte (ofChunks cs) (oc + i))
    else 0
  maskExt i := if i < cLen then
      (if 8192 * km ≤ mb + i ∧ mb + i < 8192 * (km + mm) then
        bit (ofChunks ((cs.drop km).take mm)) (mb + i - 8192 * km)
      else bit (ofChunks cs) (mb + i))
    else true
  maskAt i := if i < cLen then
      (if 8192 * km ≤ mb + i ∧ mb + i < 8192 * (km + mm) then
        bit (ofChunks ((cs.drop km).take mm)) (mb + i - 8192 * km)
      else bit (ofChunks cs) (mb + i))
    else false
  codeSize := cLen
  maskSize := cLen

theorem cview_eq (cs : List Nat) (h : ∀ c ∈ cs, c < 2 ^ 8192) (oc mb cLen kc mc km mm : Nat) :
    cview cs oc mb cLen kc mc km mm = view (ofChunks cs) oc mb cLen := by
  have hz : ∀ i, (if 1024 * kc ≤ oc + i ∧ oc + i < 1024 * (kc + mc) then
      byte (ofChunks ((cs.drop kc).take mc)) (oc + i - 1024 * kc) else byte (ofChunks cs) (oc + i)) =
      byte (ofChunks cs) (oc + i) := by
    intro i
    split
    · rename_i hw; exact (byte_ofChunks_window cs h kc mc _ hw.1 hw.2).symm
    · rfl
  have hm : ∀ i, (if 8192 * km ≤ mb + i ∧ mb + i < 8192 * (km + mm) then
      bit (ofChunks ((cs.drop km).take mm)) (mb + i - 8192 * km) else bit (ofChunks cs) (mb + i)) =
      bit (ofChunks cs) (mb + i) := by
    intro i
    split
    · rename_i hw; exact (bit_ofChunks_window cs h km mm _ hw.1 hw.2).symm
    · rfl
  simp only [cview, view, hz, hm]

/-- `cview` with a second stretch of code, chunks kc₂ … kc₂ + mc₂ − 1: for a block whose branch
    target lies far from it. -/
def cview2 (cs : List Nat) (oc mb cLen kc mc kc₂ mc₂ km mm : Nat) : CodeView :=
  { cview cs oc mb cLen kc mc km mm with
    zeta := fun i => if i < cLen then
      (if 1024 * kc ≤ oc + i ∧ oc + i < 1024 * (kc + mc) then
        byte (ofChunks ((cs.drop kc).take mc)) (oc + i - 1024 * kc)
      else if 1024 * kc₂ ≤ oc + i ∧ oc + i < 1024 * (kc₂ + mc₂) then
        byte (ofChunks ((cs.drop kc₂).take mc₂)) (oc + i - 1024 * kc₂)
      else byte (ofChunks cs) (oc + i))
    else 0 }

theorem cview2_eq (cs : List Nat) (h : ∀ c ∈ cs, c < 2 ^ 8192) (oc mb cLen kc mc kc₂ mc₂ km mm : Nat) :
    cview2 cs oc mb cLen kc mc kc₂ mc₂ km mm = view (ofChunks cs) oc mb cLen := by
  rw [← cview_eq cs h oc mb cLen kc mc km mm]
  simp only [cview2, cview, CodeView.mk.injEq, and_true]
  funext i
  split
  · split
    · rfl
    · split
      · rename_i _ _ hw
        exact (byte_ofChunks_window cs h kc₂ mc₂ _ hw.1 hw.2).symm
      · rfl
  · rfl

theorem cview_zeta_lt (cs : List Nat) (h : ∀ c ∈ cs, c < 2 ^ 8192) (oc mb cLen kc mc km mm i : Nat) :
    (cview cs oc mb cLen kc mc km mm).zeta i < 256 := by
  rw [cview_eq cs h]
  simp only [view]
  split
  · exact byte_lt _ _
  · decide

theorem view_zeta_lt (N oc mb cLen i : Nat) : (view N oc mb cLen).zeta i < 256 := by
  simp only [view]
  split
  · exact byte_lt _ _
  · decide

end NatBlob

end PVM
