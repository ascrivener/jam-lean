import Services.Bootstrap.Reader
import Services.Bootstrap.MemcpyBig
import PVM.Logic.Go

/-!
# Bootstrap's instruction-list decode loop

`Instructions::decode` decodes the list's elements in a loop at 680, with the frame
ω₁ = sp = 4278057688: the reader's address at sp + 24, the Vec's capacity, buffer and length at
sp + 40, sp + 48 and sp + 56, and the elements still to decode in ω₅. One pass reads the element's
tag (`read_ok`), dispatches on it (for `Checkpoint`, tag 15, the value is the discriminant word
2^63 + 14 at sp + 64), moves the 232-octet value to sp + 296 and then to the buffer's slot
(`memcpy_big_aligned`), and counts it. The steps between the summaries are proved here with
`pvm_go`.
-/

namespace Services.Bootstrap.DecodeLoop

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 680 … 719: spill ω₀ = 18, ω₅, ω₆ below sp, clear the result's tag octet at sp − 56, and call the
    reader for one octet into sp − 56. -/
theorem s1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h1 : ω[1] = UInt64.ofNat 4278057688)
    (m24 : μ.readN 4278057712 8 = Num.encodeLE 8 4278058648)
    (hw : ∀ a, 4278057632 ≤ a → a < 4278057688 → μ.writable a = true)
    (hr : ∀ a, 4278057712 ≤ a → a < 4278057720 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 680 ω μ x 58434 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 930 ∧ ω'[1] = UInt64.ofNat 4278057632 ∧ ω'[5] = UInt64.ofNat 4278057752 ∧
      ω'[6] = UInt64.ofNat 4278058648 ∧ ω'[7] = UInt64.ofNat 4278058648 ∧ ω'[8] = UInt64.ofNat 4278057632 ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN 4278057680 8 = Num.encodeLE 8 18 ∧ μ'.readN 4278057672 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN 4278057664 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < 4278057632 ∨ 4278057688 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrf : ∀ a, 4278057632 ≤ a → a < 4278057688 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 : rdN μ 4278057712 8 = 4278058648 := by
    rw [← encodeLE_rdN] at m24
    have := congrArg Num.decodeLE m24
    rwa [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (rdN_lt64 μ _)] at this
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, r24, hw, hrf, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32,
      h1, r24]
    all_goals try rfl

/-- A word fact as the folded load `pvm_simp` sees. -/
theorem rdN_of {μ : Memory} {a n v : Nat} (h : μ.readN a n = Num.encodeLE n v) (hv : v < 2 ^ (8 * n)) :
    rdN μ a n = v := by
  show Num.decodeLE (μ.readN a n) = v
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- 20626 … 21217: the tag decode, after the reader left the tag 15 at sp − 56 (ω₁ = sp − 56): the
    dispatch table's entry for 15 leads to 21193, which stores `Checkpoint`'s discriminant word
    2^63 + 14 at sp + 64 (ω₅), restores ω₀, ω₅, ω₆ and sp, and returns to 723. -/
theorem s2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (v5 v6 : Nat)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat 4278057632) (h5 : ω[5] = UInt64.ofNat 4278057752) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read 4278057632 = 15) (tab : μ.readN 67536 4 = [50, 252, 254, 255])
    (s0 : μ.readN 4278057680 8 = Num.encodeLE 8 18) (s5 : μ.readN 4278057672 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN 4278057664 8 = Num.encodeLE 8 v6)
    (hw : ∀ a, 4278057752 ≤ a → a < 4278057760 → μ.writable a = true)
    (hr : ∀ a, 4278057632 ≤ a → a < 4278057688 → μ.readable a = true)
    (hrt : ∀ a, 67536 ≤ a → a < 67540 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 723 ω' μ' x 19 ∧
      ω'[0] = UInt64.ofNat 18 ∧ ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278057752 8 = Num.encodeLE 8 9223372036854775822 ∧
      (∀ a, a < 4294967296 → (a < 4278057752 ∨ 4278057760 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rt : rdN μ 67536 4 = 4294900786 := by simp [rdN, tab, Num.decodeLE]
  have r0 : rdN μ 4278057680 8 = 18 := rdN_of s0 (by decide)
  have r5 : rdN μ 4278057672 8 = v5 := rdN_of s5 hv5
  have r6 : rdN μ 4278057664 8 = v6 := rdN_of s6 hv6
  have rb : rdN μ 4278057632 1 = 15 := by simp [rdN, Memory.readN, tag, Num.decodeLE]
  have hsx : sxw 4 4294900786 = 18446744073709485106 := by decide
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, rt, r0, r5, r6, rb, tag, hw, hr, hrt, hsx, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, h1, r0, r5, r6]
    all_goals try rfl

/-- 723 … 743: the result is no error (ω₇ ≠ 2^64 − 2): move the 232-octet value from sp + 64 to
    sp + 296 (`memcpy`, returning to 749). -/
theorem s3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h1 : ω[1] = UInt64.ofNat 4278057688)
    (m64 : μ.readN 4278057752 8 = Num.encodeLE 8 9223372036854775822)
    (hr : ∀ a, 4278057752 ≤ a → a < 4278057760 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 723 ω μ x 68729 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 20 ∧ ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat 4278057984 ∧ ω'[8] = UInt64.ofNat 4278057752 ∧ ω'[9] = UInt64.ofNat 232 := by
  have r64 : rdN μ 4278057752 8 = 9223372036854775822 := rdN_of m64 (by decide)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, r64, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, h1]
    all_goals try rfl

/-- 749 … 662: the Vec has room (length k ≠ capacity c): the slot's address, B + 232 k for the buffer B, and the
    move of the value from sp + 296 there (`memcpy`, returning to 668). -/
theorem s4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (k c B : Nat)
    (hk : k < c) (hc : c < 4294967296) (hB : B + 232 * c < 4294967296)
    (h1 : ω[1] = UInt64.ofNat 4278057688)
    (m40 : μ.readN 4278057728 8 = Num.encodeLE 8 c) (m48 : μ.readN 4278057736 8 = Num.encodeLE 8 B)
    (m56 : μ.readN 4278057744 8 = Num.encodeLE 8 k)
    (hw : ∀ a, 4278057720 ≤ a → a < 4278057728 → μ.writable a = true)
    (hr : ∀ a, 4278057720 ≤ a → a < 4278057752 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 749 ω μ x 68729 ω' μ' x 11 ∧
      ω'[0] = UInt64.ofNat 16 ∧ ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat k ∧
      ω'[7] = UInt64.ofNat (B + 232 * k) ∧ ω'[8] = UInt64.ofNat 4278057984 ∧
      ω'[9] = UInt64.ofNat 232 ∧
      (∀ a, a < 4294967296 → (a < 4278057720 ∨ 4278057728 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r40 : rdN μ 4278057728 8 = c := rdN_of m40 (by omega)
  have r48 : rdN μ 4278057736 8 = B := rdN_of m48 (by omega)
  have r56 : rdN μ 4278057744 8 = k := rdN_of m56 (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, r40, r48, r56, hk, hc, hB, hw, hr, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, h1]
    all_goals try (congr 1; omega)
    all_goals try with_reducible rfl

/-- 668 … 677: count the element (length k + 1 at sp + 56, ω₅ − 1 left) and loop to 680. -/
theorem s5_more {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (k r : Nat)
    (hk : k < 4294967296) (hr2 : 2 ≤ r) (hrb : r < 4294967296)
    (h1 : ω[1] = UInt64.ofNat 4278057688) (h5 : ω[5] = UInt64.ofNat r) (h6 : ω[6] = UInt64.ofNat k)
    (hw : ∀ a, 4278057744 ≤ a → a < 4278057752 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 668 ω μ x 680 ω' (μ.writeN 4278057744 (Num.encodeLE 8 (k + 1))) x 4 ∧
      ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat (r - 1) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hk, hr2, hrb, hw]
  case post =>
    refine ⟨?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, h1]
    all_goals try (congr 1; omega)
    all_goals try with_reducible rfl

/-- 668 … 677: count the last element (length k + 1) and leave the loop for 562. -/
theorem s5_last {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (k : Nat)
    (hk : k < 4294967296)
    (h1 : ω[1] = UInt64.ofNat 4278057688) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat k)
    (hw : ∀ a, 4278057744 ≤ a → a < 4278057752 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 668 ω μ x 562 ω' (μ.writeN 4278057744 (Num.encodeLE 8 (k + 1))) x 4 ∧
      ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hk, hw]
  case post =>
    refine ⟨?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32, h1]
    all_goals try rfl

/-- **The loop's state at 680** after k of the n elements: the frame's slots, the reader at the
    k-th element's tag, the tags still to read (all 15, `Checkpoint`), the dispatch table's entry,
    the k elements decoded (their discriminant word) in the buffer B, and the access the pass needs. -/
structure Inv (n k B : Nat) (ω : Regs) (μ : Memory) : Prop where
  r1 : ω[1] = UInt64.ofNat 4278057688
  r5 : ω[5] = UInt64.ofNat (n - k)
  m24 : μ.readN 4278057712 8 = Num.encodeLE 8 4278058648
  m40 : μ.readN 4278057728 8 = Num.encodeLE 8 n
  m48 : μ.readN 4278057736 8 = Num.encodeLE 8 B
  m56 : μ.readN 4278057744 8 = Num.encodeLE 8 k
  rP : μ.readN 4278058648 8 = Num.encodeLE 8 (206913 + k)
  rL : μ.readN 4278058656 8 = Num.encodeLE 8 (n + 32 - k)
  pay : ∀ j, k ≤ j → j < n → μ.read (206913 + j) = 15
  tab : μ.readN 67536 4 = [50, 252, 254, 255]
  el : ∀ j, j < k → μ.readN (B + 232 * j) 8 = Num.encodeLE 8 9223372036854775822
  ws : ∀ a, 4278057496 ≤ a → a < 4278058216 → μ.writable a = true
  wr : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ.writable a = true
  wb : ∀ a, B ≤ a → a < B + 232 * n → μ.writable a = true
  rp : ∀ a, 206913 ≤ a → a < 206913 + n → μ.readable a = true
  rt : ∀ a, 67536 ≤ a → a < 67540 → μ.readable a = true

/-- The memory a pass may change: the stack frame, the reader and the buffer. -/
def Frame (n B : Nat) (μ μ' : Memory) : Prop :=
  (∀ a, a < 4294967296 → (a < 4278057496 ∨ 4278058216 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
    (a < B ∨ B + 232 * n ≤ a) → μ'.read a = μ.read a) ∧
  (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- Bounds the pass's address arithmetic needs: the list is short and the buffer lies after the
    payload's octets in the heap, 8-aligned. -/
def Ok (n B : Nat) : Prop := n < 128 ∧ 206913 + n ≤ B ∧ B % 8 = 0 ∧ B + 232 * n < 2147483648

macro "fr_conv" : tactic => `(tactic| (simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
  decide_eq_false_iff_not, not_and, Nat.not_lt] at *; omega))

/-- **One pass** of the decode loop: from the state after k < n elements, the (k+1)-th `Checkpoint`
    is decoded into the buffer's slot k; the loop continues at 680, or leaves for 562 after the last. -/
theorem pass {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (n k B : Nat)
    (hk : k < n) (ok : Ok n B) (h : Inv n k B ω μ) :
    ∃ ω' μ', FreeStepsH p R 680 ω μ x (if k + 1 < n then 680 else 562) ω' μ' x 1700 ∧
      Inv n (k + 1) B ω' μ' ∧ Frame n B μ μ' := by
  obtain ⟨hn, hB1, hB2, hB3⟩ := ok
  obtain ⟨r1, r5, m24, m40, m48, m56, rP, rL, pay, tab, el, ws, wr, wb, rp, rt⟩ := h
  -- S1
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, as0, as5, as6, afr, ard, awr⟩ :=
    s1 (p := p) (P := P) (R := R) x ω μ r1 m24 (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega)))
  have afr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057632 ≤ a ∧ a < 4278057688))) = true → μ1.read a = μ.read a :=
    fun a ha => afr a (by fr_conv) (by fr_conv)
  clear afr
  -- the tag
  obtain ⟨ω2, μ2, run2, ok2⟩ := read_ok (p := p) (P := P) (R := R) x ω1 μ1 930 20626 4278057632 4278058648
    4278057632 (206913 + k) (n + 32 - k) 1 a0 a1 a7 a8 a9 (by decide)
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
  have tag2 : μ2.read 4278057632 = 15 := by
    have := congrArg List.head? bbuf
    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.head?_cons, Option.some.injEq, Nat.add_zero] at this
    rw [this, afr' _ (by fr_conv)]
    exact pay k (Nat.le_refl k) hk
  -- S2
  have v5 : (ω[5]).toNat = n - k := by rw [r5]; simp; omega
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c64, cfr, crd, cwr⟩ := s2 (p := p) (P := P) (R := R) x ω2 μ2
    (n - k) (ω[6]).toNat (by omega) (UInt64.toNat_lt _) (b1.trans a1) (b5.trans a5) b7 tag2
    (by rw [Memory.readN_congr (fun j hj => (bfr' _ (by fr_conv)).trans (afr' _ (by fr_conv)))]; exact tab)
    (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as0)
    (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv)), as5, v5])
    (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as6)
    (fun a h1 h2 => by rw [bwr, awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [brd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [brd, ard]; exact rt a h1 h2)
  have cfr' : ∀ a, (decide (a < 4294967296) && !(decide (4278057752 ≤ a ∧ a < 4278057760))) = true → μ3.read a = μ2.read a :=
    fun a ha => cfr a (by fr_conv) (by fr_conv)
  clear cfr
  -- S3 and the first move
  obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := s3 (p := p) (P := P) (R := R) x ω3 μ3 c1 c64
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
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ffr, frd, fwr⟩ := s4 (p := p) (P := P) (R := R) x ω5 μ5 k n B
    hk (by omega) (by omega) e1
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
  -- the slot holds the discriminant word
  have slot : μ7.readN (B + 232 * k) 8 = Num.encodeLE 8 9223372036854775822 := by
    rw [← readN_take μ7 _ 232 8 (by decide), gcp, readN_take _ _ 232 8 (by decide),
      Memory.readN_congr (fun j hj => ffr' _ (by fr_conv)), ← readN_take μ5 _ 232 8 (by decide), ecp,
      readN_take _ _ 232 8 (by decide)]
    exact c64
  -- everything below the slot and stack is as at the start
  have back : ∀ a, a < 4294967296 → (a < 4278057496 ∨ 4278058216 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
      (a < B + 232 * k ∨ B + 232 * k + 232 ≤ a) → μ7.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans ((efr' a (by fr_conv)).trans
      ((cfr' a (by fr_conv)).trans ((bfr' a (by fr_conv)).trans (afr' a (by fr_conv))))))
  have q6 : ω7[6] = UInt64.ofNat k := g6.trans f6
  have q5 : ω7[5] = UInt64.ofNat (n - k) := g5.trans (f5.trans (e5.trans (d5.trans c5)))
  have q1 : ω7[1] = UInt64.ofNat 4278057688 := g1
  have hrdq : ∀ a, μ7.readable a = μ.readable a := fun a => by rw [grd, frd, erd, crd, brd, ard]
  have hwrq : ∀ a, μ7.writable a = μ.writable a := fun a => by rw [gwr, fwr, ewr, cwr, bwr, awr]
  -- the reader, after the tag
  have rd7 : ∀ a, 4278058648 ≤ a → a < 4278058664 → μ7.read a = μ2.read a := fun a h1 h2 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans ((efr' a (by fr_conv)).trans (cfr' a (by fr_conv))))
  -- S5: count it, and loop or leave
  have post : ∀ (t : Nat) (ω8 : Regs), FreeStepsH p R 668 ω7 μ7 x t ω8 (μ7.writeN 4278057744 (Num.encodeLE 8 (k + 1))) x 4 →
      ω8[1] = UInt64.ofNat 4278057688 → ω8[5] = UInt64.ofNat (n - (k + 1)) →
      ∃ ω' μ', FreeStepsH p R 680 ω μ x t ω' μ' x 1700 ∧ Inv n (k + 1) B ω' μ' ∧ Frame n B μ μ' := by
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
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), bR0, Nat.add_assoc]
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), bR8]
      first | rfl | (congr 1; omega)
    · intro j h1 h2
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega),
        back _ (by omega) (by omega) (by omega) (by omega)]
      exact pay j (by omega) h2
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32]),
        Memory.readN_congr (fun j hj => back _ (by omega) (by omega) (by omega) (by omega))]; exact tab
    · intro j hj
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega)]
      rcases Nat.lt_or_ge j k with hj' | hj'
      · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by
          rcases Nat.lt_or_ge j k with _ | _ <;> omega))]
        exact el j hj'
      · rw [show j = k by omega]; exact slot
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
  by_cases hmore : k + 1 < n
  · rw [if_pos hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := s5_more (p := p) (P := P) (R := R) x ω7 μ7 k (n - k) (by omega) (by omega)
      (by omega) q1 q5 q6 (fun a h1 h2 => by rw [hwrq]; exact ws a (by omega) (by omega))
    exact post 680 ω8 run8 i1 (i5.trans (by rw [show n - k - 1 = n - (k + 1) by omega]))
  · rw [if_neg hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := s5_last (p := p) (P := P) (R := R) x ω7 μ7 k (by omega) q1
      (q5.trans (by rw [show n - k = 1 by omega])) q6 (fun a h1 h2 => by rw [hwrq]; exact ws a (by omega) (by omega))
    exact post 562 ω8 run8 i1 (i5.trans (by rw [show n - (k + 1) = 0 by omega]))

/-- **The decode loop**: from the state after k < n elements, the loop decodes the rest and leaves for
    562 with all n `Checkpoint`s in the buffer, changing only the stack frame, the reader and the
    buffer. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) (n B : Nat) (ok : Ok n B) :
    ∀ r k (ω : Regs) (μ : Memory), n - k = r → k < n → Inv n k B ω μ →
      ∃ ω' μ', FreeStepsH p R 680 ω μ x 562 ω' μ' x (1700 * r) ∧ Inv n n B ω' μ' ∧ Frame n B μ μ' := by
  intro r
  induction r with
  | zero => intro k ω μ hr hk; omega
  | succ r ih =>
    intro k ω μ hr hk h
    obtain ⟨ω1, μ1, run1, h1, f1⟩ := pass (p := p) (P := P) (R := R) x ω μ n k B hk ok h
    by_cases hmore : k + 1 < n
    · rw [if_pos hmore] at run1
      obtain ⟨ω2, μ2, run2, h2, f2⟩ := ih (k + 1) ω1 μ1 (by omega) hmore h1
      refine ⟨ω2, μ2, (run1.trans run2).mono (by rw [Nat.mul_succ]; omega), h2, ?_, ?_, ?_⟩
      · intro a h0 ha hb hc; rw [f2.1 a h0 ha hb hc, f1.1 a h0 ha hb hc]
      · intro a; rw [f2.2.1, f1.2.1]
      · intro a; rw [f2.2.2, f1.2.2]
    · rw [if_neg hmore] at run1
      rw [show k + 1 = n by omega] at h1
      exact ⟨ω1, μ1, run1.mono (by rw [Nat.mul_succ]; omega), h1, f1⟩

end Services.Bootstrap.DecodeLoop
