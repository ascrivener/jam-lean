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
    and memory changed only in the 184 octets below A, the reader and the slot. -/
def ElemOk (p : ByteArray) (P : Program) (enc : List UInt8) (Rep : List UInt8 → Prop) : Prop :=
  ∀ (X : Type) (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat),
    ω[1] = UInt64.ofNat 4278057632 → ω[5] = UInt64.ofNat 4278057752 → ω[6] = UInt64.ofNat 4278058648 →
    ω[7] = UInt64.ofNat 0 → μ.read 4278057632 = enc.headD 0 →
    μ.readN 4278058648 8 = Num.encodeLE 8 ptr → μ.readN 4278058656 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278057448 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN 4278057680 8 = Num.encodeLE 8 18 → μ.readN 4278057672 8 = Num.encodeLE 8 v5 →
    μ.readN 4278057664 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278057448 ≤ a → a < 4278058216 → μ.writable a = true) →
    (∀ a, 4278058648 ≤ a → a < 4278058664 → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 723 ω' μ' x 2000 ∧
      ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278058648 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN 4278058656 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN 4278057752 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      Rep (μ'.readN 4278057752 232) ∧
      (∀ a, a < 4294967296 → (a < 4278057448 ∨ 4278057632 ≤ a) → (a < 4278058648 ∨ 4278058664 ≤ a) →
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

end Services.Bootstrap.Decode.Loop
