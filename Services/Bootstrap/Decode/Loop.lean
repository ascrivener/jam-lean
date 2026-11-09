import Services.Bootstrap.DecodeLoop
import Services.Bootstrap.Decode.Tag

/-!
# `Instructions::decode`'s element loop, for any instruction

`DecodeLoop` proves the loop at 680 for lists of `Checkpoint`. Here the element decoder is abstract:
`ElemOk enc Rep` says that `Instruction::decode`, entered at 20626 after reading the first octet of
`enc`, reads the rest of `enc`, returns to the loop (723) and leaves in its 232-octet slot a value
satisfying `Rep`, other than the error word. The pass and the loop are proved once for every list
of elements that satisfy it; each variant's decode theorem (`Decode.Tag`, `Decode.Fixed`, …) supplies
an `ElemOk`.
-/

namespace Services.Bootstrap.Decode.Loop

open PVM Services.Bootstrap Services.Bootstrap.Code
open Services.Bootstrap.DecodeLoop (rdN_of)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 723 … 743: the element decoded without error (the word at sp + 64 is not 2^64 − 2): move the
    232-octet value from sp + 64 to sp + 296 (`memcpy`, returning to 749). -/
theorem g3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (W : Nat)
    (h1 : ω[1] = UInt64.ofNat 4278057688)
    (m64 : μ.readN 4278057752 8 = Num.encodeLE 8 W) (hW : W < 18446744073709551616)
    (hne : W ≠ 18446744073709551614)
    (hr : ∀ a, 4278057752 ≤ a → a < 4278057760 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 723 ω μ x 68729 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 20 ∧ ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat 4278057984 ∧ ω'[8] = UInt64.ofNat 4278057752 ∧ ω'[9] = UInt64.ofNat 232 := by
  have r64 : rdN μ 4278057752 8 = W := rdN_of m64 hW
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, r64, hne, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try rfl

/-- **One element decodes**: from 20626 in the decode loop's frame (the decoder's frame at
    A = 4278057632, its slot at O = 4278057752, the reader at RD = 4278058648), with the first octet of
    `enc` read into A and the rest of `enc` at the reader, `Instruction::decode` returns to 723 with the
    reader advanced past `enc`, a value satisfying `Rep` and other than the error word in O … O + 232,
    and memory changed only in the stack from its bottom (4278050816) to A + 32, the reader and the slot. -/
def ElemOk (p : ByteArray) (P : Program) (enc : List UInt8) (Rep : List UInt8 → Prop) : Prop :=
  ∀ (X : Type) (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat),
    ω[1] = UInt64.ofNat 4278057632 → ω[5] = UInt64.ofNat 4278057752 → ω[6] = UInt64.ofNat 4278058648 →
    ω[7] = UInt64.ofNat 0 → μ.read 4278057632 = enc.headD 0 →
    μ.readN 4278058648 8 = Num.encodeLE 8 ptr → μ.readN 4278058656 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN 4278057680 8 = Num.encodeLE 8 18 → μ.readN 4278057672 8 = Num.encodeLE 8 v5 →
    μ.readN 4278057664 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < 4278058216 → μ.writable a = true) →
    (∀ a, 4278058648 ≤ a → a < 4278058664 → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 723 ω' μ' x 4000 ∧
      ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278058648 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN 4278058656 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN 4278057752 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      Rep (μ'.readN 4278057752 232) ∧
      (∀ a, a < 4294967296 → (a < 4278050816 ∨ 4278057664 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
        (a < 4278057752 ∨ 4278057984 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- The octets before element k of a list of encodings. -/
def off (es : List (List UInt8)) (k : Nat) : Nat := ((es.take k).flatten).length

/-- A stretch of a read: octets i … i + m of the n at a. -/
theorem readN_sub (μ : Memory) (a n i m : Nat) (l : List UInt8) (h : μ.readN a n = l) (hm : i + m ≤ n) :
    μ.readN (a + i) m = (l.drop i).take m := by
  subst h
  apply List.ext_getElem
  · simp [Memory.length_readN]; omega
  · intro j h1 h2
    simp [Memory.readN, Nat.add_assoc]

/-- Element k sits at its offset in the flattened list. -/
theorem flatten_at (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    ((es.flatten).drop (off es k)).take (es[k].length) = es[k] := by
  have : es.flatten = (es.take k).flatten ++ (es[k] ++ (es.drop (k + 1)).flatten) := by
    calc es.flatten = (es.take k ++ es.drop k).flatten := by rw [List.take_append_drop]
      _ = _ := by rw [List.flatten_append, List.drop_eq_getElem_cons hk, List.flatten_cons]
  rw [this, off, List.drop_left, List.take_left]

theorem off_succ (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    off es (k + 1) = off es k + es[k].length := by
  unfold off
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.flatten_append, List.length_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem off_le (es : List (List UInt8)) (k : Nat) : off es k ≤ es.flatten.length := by
  have : es.flatten.length = ((es.take k ++ es.drop k).flatten).length := by rw [List.take_append_drop]
  rw [this, List.flatten_append, List.length_append, off]
  omega

theorem off_lt (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    off es k + es[k].length ≤ es.flatten.length := by
  rw [← off_succ es k hk]; exact off_le es (k + 1)

/-- The first octet of a read. -/
theorem read_head (μ : Memory) (a n : Nat) (l : List UInt8) (h : μ.readN a n = l) (hn : 0 < n) :
    μ.read a = l.headD 0 := by
  subst h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [Memory.readN, List.range_succ_eq_map]

/-- **The loop's state at 680** after k of the elements `es` (their encodings, in order): the frame's
    slots, the reader just after element k − 1, the payload's octets, the dispatch table, the k values
    decoded so far in the buffer B (value j satisfying `reps j`), and the access the pass needs. -/
structure Inv (es : List (List UInt8)) (reps : Nat → List UInt8 → Prop) (k B : Nat) (ω : Regs) (μ : Memory) :
    Prop where
  r1 : ω[1] = UInt64.ofNat 4278057688
  r5 : ω[5] = UInt64.ofNat (es.length - k)
  m24 : μ.readN 4278057712 8 = Num.encodeLE 8 4278058648
  m40 : μ.readN 4278057728 8 = Num.encodeLE 8 es.length
  m48 : μ.readN 4278057736 8 = Num.encodeLE 8 B
  m56 : μ.readN 4278057744 8 = Num.encodeLE 8 k
  rP : μ.readN 4278058648 8 = Num.encodeLE 8 (206913 + off es k)
  rL : μ.readN 4278058656 8 = Num.encodeLE 8 (es.flatten.length + 32 - off es k)
  pay : μ.readN 206913 es.flatten.length = es.flatten
  tab : μ.readN 67476 100 = Tag.table
  el : ∀ j, j < k → reps j (μ.readN (B + 232 * j) 232)
  ws : ∀ a, 4278050816 ≤ a → a < 4278058216 → μ.writable a = true
  wr : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ.writable a = true
  wb : ∀ a, B ≤ a → a < B + 232 * es.length → μ.writable a = true
  rp : ∀ a, 206913 ≤ a → a < 206913 + es.flatten.length → μ.readable a = true
  rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true

/-- The memory a pass may change: the stack below the loop's frame, the reader and the buffer. -/
def Frame (n B : Nat) (μ μ' : Memory) : Prop :=
  (∀ a, a < 4294967296 → (a < 4278050816 ∨ 4278058216 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
    (a < B ∨ B + 232 * n ≤ a) → μ'.read a = μ.read a) ∧
  (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- Bounds the pass needs: a short list of non-empty encodings, and the buffer after the payload in
    the heap, 8-aligned and below 2^31. -/
def Ok (es : List (List UInt8)) (B : Nat) : Prop :=
  es.length < 128 ∧ 206913 + es.flatten.length ≤ B ∧ B % 8 = 0 ∧ B + 232 * es.length < 2147483648 ∧
    ∀ j (hj : j < es.length), 1 ≤ es[j].length

macro "fr_conv" : tactic => `(tactic| (simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
  decide_eq_false_iff_not, not_and, Nat.not_lt] at *; omega))

/-- **One pass** of the decode loop: from the state after k < n elements, element k is decoded
    (`ElemOk`) into the buffer's slot k; the loop continues at 680, or leaves for 562 after the last. -/
theorem pass {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (es : List (List UInt8)) (reps : Nat → List UInt8 → Prop) (k B : Nat)
    (hk : k < es.length) (ok : Ok es B) (hel : ∀ j (hj : j < es.length), ElemOk p P es[j] (reps j))
    (h : Inv es reps k B ω μ) :
    ∃ ω' μ', FreeStepsH p R 680 ω μ x (if k + 1 < es.length then 680 else 562) ω' μ' x 5700 ∧
      Inv es reps (k + 1) B ω' μ' ∧ Frame es.length B μ μ' := by
  obtain ⟨hn, hB1, hB2, hB3, hne⟩ := ok
  obtain ⟨r1, r5, m24, m40, m48, m56, rP, rL, pay, tab, el, ws, wr, wb, rp, rt⟩ := h
  have hL := hne k hk
  have hoff := off_lt es k hk
  -- element k in the payload
  have ek : μ.readN (206913 + off es k) es[k].length = es[k] := by
    rw [readN_sub μ 206913 _ _ _ _ pay hoff, flatten_at es k hk]
  have ek0 : μ.read (206913 + off es k) = es[k].headD 0 := read_head μ _ _ _ ek (by omega)
  have ekt : μ.readN (206913 + off es k + 1) (es[k].length - 1) = es[k].tail := by
    rw [readN_sub μ _ _ 1 _ _ ek (by omega), List.drop_one, List.take_of_length_le (by simp)]
  -- S1
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, as0, as5, as6, afr, ard, awr⟩ :=
    DecodeLoop.s1 (p := p) (P := P) (R := R) x ω μ r1 m24 (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega)))
  have afr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057632 ≤ a ∧ a < 4278057688))) = true → μ1.read a = μ.read a :=
    fun a ha => afr a (by fr_conv) (by fr_conv)
  clear afr
  -- the tag
  obtain ⟨ω2, μ2, run2, ok2⟩ := read_ok (p := p) (P := P) (R := R) x ω1 μ1 930 20626 4278057632 4278058648
    4278057632 (206913 + off es k) (es.flatten.length + 32 - off es k) 1 a0 a1 a7 a8 a9 (by decide)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_464]) bs_20626 (by decide) (by decide) (by decide)
    (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) (by omega) (by decide) (by omega)
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wr a h1 h2)
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [ard]; exact rp a (by omega) (by omega))
    (by rw [Memory.readN_congr (fun j hj => afr' _ (by fr_conv))]; exact rP)
    (by rw [Memory.readN_congr (fun j hj => afr' _ (by fr_conv))]; exact rL)
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b12, b7, bR0, bR8, bbuf, bfr, brd, bwr⟩ := ok2
  have bfr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057544 ≤ a ∧ a < 4278057632)) && !(decide (4278058648 ≤ a ∧ a < 4278058664)) && !(decide (4278057632 ≤ a ∧ a < 4278057633))) = true →
      μ2.read a = μ1.read a := fun a ha => bfr a (by fr_conv) (by fr_conv) (by fr_conv) (by fr_conv)
  clear bfr
  have tag2 : μ2.read 4278057632 = es[k].headD 0 := by
    have := congrArg List.head? bbuf
    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.head?_cons, Option.some.injEq, Nat.add_zero] at this
    rw [this, afr' _ (by fr_conv)]
    exact ek0
  have pay2 : ∀ a, 206913 ≤ a → a < 206913 + es.flatten.length → μ2.read a = μ.read a :=
    fun a h1 h2 => (bfr' a (by fr_conv)).trans (afr' a (by fr_conv))
  -- the element
  have v5 : (ω[5]).toNat = es.length - k := by rw [r5]; simp; omega
  obtain ⟨ω3, μ3, run3, c1, c5, c6, cR0, cR8, ⟨W, hW, cW, cne⟩, crep, cfr, crd, cwr⟩ :=
    hel k hk X R x ω2 μ2 (206913 + off es k + 1) (es.flatten.length + 32 - off es k - 1) (es.length - k)
      (ω[6]).toNat (b1.trans a1) (b5.trans a5) (b6.trans a6) b7 tag2 bR0 bR8 (by omega) (by omega) (by omega)
      (by omega)
      (by rw [Memory.readN_congr (fun j hj => pay2 _ (by omega) (by omega))]; exact ekt)
      (fun a h1 h2 => by rw [brd, ard]; exact rp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as0)
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv)), as5, v5])
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as6)
      (by omega) (UInt64.toNat_lt _)
      (by rw [Memory.readN_congr (fun j hj => (bfr' _ (by fr_conv)).trans (afr' _ (by fr_conv)))]; exact tab)
      (fun a h1 h2 => by rw [brd, ard]; exact rt a h1 h2)
      (fun a h1 h2 => by rw [bwr, awr]; exact ws a h1 h2)
      (fun a h1 h2 => by rw [bwr, awr]; exact wr a h1 h2)
  have cfr' : ∀ a, (decide (a < 4294967296) && !(decide (4278050816 ≤ a ∧ a < 4278057664)) && !(decide (4278058648 ≤ a ∧ a < 4278058664)) && !(decide (4278057752 ≤ a ∧ a < 4278057984))) = true →
      μ3.read a = μ2.read a := fun a ha => cfr a (by fr_conv) (by fr_conv) (by fr_conv) (by fr_conv)
  clear cfr
  -- S3 and the first move
  obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := g3 (p := p) (P := P) (R := R) x ω3 μ3 W c1 cW hW cne
    (fun a h1 h2 => by rw [crd, brd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ecp, efr, erd, ewr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R)
    x ω4 μ3 20 749 4278057688 4278057984 4278057752 232 d0 d1 d7 d8 d9 (by decide)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_9]) bs_749 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun a h1 h2 => by rw [crd, brd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact ws a (by omega) (by omega))
  have efr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057984 ≤ a ∧ a < 4278058216)) && !(decide (4278057640 ≤ a ∧ a < 4278057688))) = true → μ5.read a = μ3.read a :=
    fun a ha => efr a (by fr_conv) (by fr_conv) (by fr_conv)
  clear efr
  -- S4 and the second move
  have keep : ∀ a, 4278057712 ≤ a → a < 4278057752 → μ5.read a = μ.read a := fun a h1 h2 =>
    (efr' a (by fr_conv)).trans ((cfr' a (by fr_conv)).trans ((bfr' a (by fr_conv)).trans (afr' a (by fr_conv))))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ffr, frd, fwr⟩ := DecodeLoop.s4 (p := p) (P := P) (R := R)
    x ω5 μ5 k es.length B hk (by omega) (by omega) e1
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m56)
    (fun a h1 h2 => by rw [ewr, cwr, bwr, awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [erd, crd, brd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
  have ffr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057720 ≤ a ∧ a < 4278057728))) = true → μ6.read a = μ5.read a :=
    fun a ha => ffr a (by fr_conv) (by fr_conv)
  clear ffr
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, gcp, gfr, grd, gwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R)
    x ω6 μ6 16 668 4278057688 (B + 232 * k) 4278057984 232 f0 f1 f7 f8 f9 (by decide)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_7]) bs_668 (by decide) (by decide) (by decide)
    (by omega) (by decide) (by omega) (by omega) (by omega) (by decide)
    (fun a h1 h2 => by rw [frd, erd, crd, brd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [fwr, ewr, cwr, bwr, awr]; exact wb a (by omega) (by omega))
    (fun a h1 h2 => by rw [fwr, ewr, cwr, bwr, awr]; exact ws a (by omega) (by omega))
  have gfr' : ∀ a, (decide (a < 4294967296) && !(decide (B + 232 * k ≤ a ∧ a < B + 232 * k + 232)) &&
      !(decide (4278057640 ≤ a ∧ a < 4278057688))) = true → μ7.read a = μ6.read a :=
    fun a ha => gfr a (by fr_conv) (by fr_conv) (by fr_conv)
  clear gfr
  -- the slot holds the element's value
  have slot : μ7.readN (B + 232 * k) 232 = μ3.readN 4278057752 232 := by
    rw [gcp, Memory.readN_congr (fun j hj => ffr' _ (by fr_conv)), ecp]
  -- everything outside the stack, the reader and the slot is as at the start
  have back : ∀ a, a < 4294967296 → (a < 4278050816 ∨ 4278058216 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
      (a < B + 232 * k ∨ B + 232 * k + 232 ≤ a) → μ7.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans ((efr' a (by fr_conv)).trans
      ((cfr' a (by fr_conv)).trans ((bfr' a (by fr_conv)).trans (afr' a (by fr_conv))))))
  have q6 : ω7[6] = UInt64.ofNat k := g6.trans f6
  have q5 : ω7[5] = UInt64.ofNat (es.length - k) := g5.trans (f5.trans (e5.trans (d5.trans c5)))
  have q1 : ω7[1] = UInt64.ofNat 4278057688 := g1
  have hrdq : ∀ a, μ7.readable a = μ.readable a := fun a => by rw [grd, frd, erd, crd, brd, ard]
  have hwrq : ∀ a, μ7.writable a = μ.writable a := fun a => by rw [gwr, fwr, ewr, cwr, bwr, awr]
  -- the reader, after the element
  have rd7 : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ7.read a = μ3.read a := fun a h1 h2 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans (efr' a (by fr_conv)))
  have offk1 := off_succ es k hk
  -- S5: count it, and loop or leave
  have post : ∀ (t : Nat) (ω8 : Regs), FreeStepsH p R 668 ω7 μ7 x t ω8 (μ7.writeN 4278057744 (Num.encodeLE 8 (k + 1))) x 4 →
      ω8[1] = UInt64.ofNat 4278057688 → ω8[5] = UInt64.ofNat (es.length - (k + 1)) →
      ∃ ω' μ', FreeStepsH p R 680 ω μ x t ω' μ' x 5700 ∧ Inv es reps (k + 1) B ω' μ' ∧ Frame es.length B μ μ' := by
    intro t ω8 run8 h1' h5'
    refine ⟨ω8, _, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      run8))))))).mono (by omega), ⟨h1', h5', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m24
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m40
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m48
    · exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), cR0, offk1]
      congr 1; omega
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), cR8, offk1]
      congr 1; omega
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp only [Num.length_encodeLE]; omega) (by simp [two32])
          (by simp only [two32]; omega),
        Memory.readN_congr (fun j hj => back _ (by omega) (by omega) (by omega) (by omega))]; exact pay
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => back _ (by omega) (by omega) (by omega) (by omega))]; exact tab
    · intro j hj
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega)]
      rcases Nat.lt_or_ge j k with hj' | hj'
      · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by
          rcases Nat.lt_or_ge j k with _ | _ <;> omega))]
        exact el j hj'
      · rw [show j = k by omega, slot]; exact crep
    · intro a h1 h2; rw [Memory.writable_writeN, hwrq]; exact ws a h1 h2
    · intro a h1 h2; rw [Memory.writable_writeN, hwrq]; exact wr a h1 h2
    · intro a h1 h2; rw [Memory.writable_writeN, hwrq]; exact wb a h1 h2
    · intro a h1 h2; rw [Memory.readable_writeN, hrdq]; exact rp a h1 h2
    · intro a h1 h2; rw [Memory.readable_writeN, hrdq]; exact rt a h1 h2
    · intro a h0 h1 h2 h3
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega)]
      exact back a h0 h1 h2 (by omega)
    · intro a; rw [Memory.readable_writeN, hrdq]
    · intro a; rw [Memory.writable_writeN, hwrq]
  by_cases hmore : k + 1 < es.length
  · rw [if_pos hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := DecodeLoop.s5_more (p := p) (P := P) (R := R) x ω7 μ7 k (es.length - k) (by omega)
      (by omega) (by omega) q1 q5 q6 (fun a h1 h2 => by rw [hwrq]; exact ws a (by omega) (by omega))
    exact post 680 ω8 run8 i1 (i5.trans (by rw [show es.length - k - 1 = es.length - (k + 1) by omega]))
  · rw [if_neg hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := DecodeLoop.s5_last (p := p) (P := P) (R := R) x ω7 μ7 k (by omega) q1
      (q5.trans (by rw [show es.length - k = 1 by omega])) q6 (fun a h1 h2 => by rw [hwrq]; exact ws a (by omega) (by omega))
    exact post 562 ω8 run8 i1 (i5.trans (by rw [show es.length - (k + 1) = 0 by omega]))

/-- **The decode loop**: from the state after k < n elements, the loop decodes the rest, each through
    its `ElemOk`, and leaves for 562 with all n values in the buffer, changing only the stack below the
    loop's frame, the reader and the buffer. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) (es : List (List UInt8))
    (reps : Nat → List UInt8 → Prop) (B : Nat) (ok : Ok es B)
    (hel : ∀ j (hj : j < es.length), ElemOk p P es[j] (reps j)) :
    ∀ r k (ω : Regs) (μ : Memory), es.length - k = r → k < es.length → Inv es reps k B ω μ →
      ∃ ω' μ', FreeStepsH p R 680 ω μ x 562 ω' μ' x (5700 * r) ∧ Inv es reps es.length B ω' μ' ∧
        Frame es.length B μ μ' := by
  intro r
  induction r with
  | zero => intro k ω μ hr hk; omega
  | succ r ih =>
    intro k ω μ hr hk h
    obtain ⟨ω1, μ1, run1, h1, f1⟩ := pass (p := p) (P := P) (R := R) x ω μ es reps k B hk ok hel h
    by_cases hmore : k + 1 < es.length
    · rw [if_pos hmore] at run1
      obtain ⟨ω2, μ2, run2, h2, f2⟩ := ih (k + 1) ω1 μ1 (by omega) hmore h1
      refine ⟨ω2, μ2, (run1.trans run2).mono (by rw [Nat.mul_succ]; omega), h2, ?_, ?_, ?_⟩
      · intro a h0 ha hb hc; rw [f2.1 a h0 ha hb hc, f1.1 a h0 ha hb hc]
      · intro a; rw [f2.2.1, f1.2.1]
      · intro a; rw [f2.2.2, f1.2.2]
    · rw [if_neg hmore] at run1
      rw [show k + 1 = es.length by omega] at h1
      exact ⟨ω1, μ1, run1.mono (by rw [Nat.mul_succ]; omega), h1, f1⟩

end Services.Bootstrap.Decode.Loop
