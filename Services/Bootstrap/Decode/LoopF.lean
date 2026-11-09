import Services.Bootstrap.DecodeLoop
import Services.Bootstrap.Decode.Tag

/-!
# The decode loop's steps, at any frame base

`Instructions::decode`'s element loop runs with its frame wherever its caller's stack pointer puts
it: in refine at 4278057688 (`DecodeLoop`), in accumulate lower. Here its step lemmas take the
frame base F (the element decoder's frame, the loop's stack pointer being F + 56) and the reader's
address RD; `DecodeLoop`'s are these at F = 4278057632, RD = 4278058648.
-/

namespace Services.Bootstrap.Decode.LoopF

open PVM Services.Bootstrap Services.Bootstrap.Code
open Services.Bootstrap.DecodeLoop (rdN_of)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- 680 … 719 (`DecodeLoop.s1` at frame base F): spill ω₀ = 18, ω₅, ω₆ at F + 48, F + 40, F + 32,
    clear the tag octet at F and call the reader (RD, kept at F + 80) for one octet into F. -/
theorem s1F {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F RD : Nat)
    (hF : 65536 ≤ F ∧ F + 1024 < 4294967296) (hRD : RD < 4294967296)
    (h1 : ω[1] = UInt64.ofNat (F + 56))
    (m24 : μ.readN (F + 80) 8 = Num.encodeLE 8 RD)
    (hw : ∀ a, F ≤ a → a < F + 56 → μ.writable a = true)
    (hr : ∀ a, F + 80 ≤ a → a < F + 88 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 680 ω μ x 58434 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 930 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat (F + 120) ∧
      ω'[6] = UInt64.ofNat RD ∧ ω'[7] = UInt64.ofNat RD ∧ ω'[8] = UInt64.ofNat F ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (F + 48) 8 = Num.encodeLE 8 18 ∧ μ'.readN (F + 40) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrf : ∀ a, F ≤ a → a < F + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 : rdN μ (F + 80) 8 = RD := rdN_of m24 (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, r24, hF, hRD, hw, hrf, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show F + 56 - 56 = F by omega, show F + 56 - 56 + 48 = F + 48 by omega,
      show F + 56 - 56 + 40 = F + 40 by omega, show F + 56 - 56 + 32 = F + 32 by omega,
      show F + 56 + 64 = F + 120 by omega, show F + 56 - 8 = F + 48 by omega,
      show F + 56 - 16 = F + 40 by omega, show F + 56 - 24 = F + 32 by omega]
    post_simp
    all_goals try (rw [UInt64.ofNat_toNat]; rfl)

/-- 723 … 743 (`Loop.g3` at frame base F): the element decoded without error (the word W at F + 120
    is not 2^64 − 2): move the 232-octet value from F + 120 to F + 352 (`memcpy`, returning to 749). -/
theorem g3F {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F W : Nat)
    (hF : 65536 ≤ F ∧ F + 1024 < 4294967296) (h1 : ω[1] = UInt64.ofNat (F + 56))
    (m64 : μ.readN (F + 120) 8 = Num.encodeLE 8 W) (hW : W < 18446744073709551616)
    (hne : W ≠ 18446744073709551614)
    (hr : ∀ a, F + 120 ≤ a → a < F + 128 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 723 ω μ x 68729 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 20 ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (F + 352) ∧ ω'[8] = UInt64.ofNat (F + 120) ∧ ω'[9] = UInt64.ofNat 232 := by
  have r64 : rdN μ (F + 56 + 64) 8 = W := by rw [show F + 56 + 64 = F + 120 by omega]; exact rdN_of m64 hW
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, r64, hne, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [show F + 56 + 296 = F + 352 by omega, show F + 56 + 64 = F + 120 by omega]
    post_simp
    all_goals try assumption

/-- 749 … 662 (`DecodeLoop.s4` at frame base F): the Vec has room (length k < capacity c): the slot's
    address B + 232 k and the move of the value from F + 352 there (`memcpy`, returning to 668). -/
theorem s4F {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F k c B : Nat)
    (hF : 65536 ≤ F ∧ F + 1024 < 4294967296)
    (hk : k < c) (hc : c < 4294967296) (hB : B + 232 * c < 4294967296)
    (h1 : ω[1] = UInt64.ofNat (F + 56))
    (m40 : μ.readN (F + 96) 8 = Num.encodeLE 8 c) (m48 : μ.readN (F + 104) 8 = Num.encodeLE 8 B)
    (m56 : μ.readN (F + 112) 8 = Num.encodeLE 8 k)
    (hw : ∀ a, F + 88 ≤ a → a < F + 96 → μ.writable a = true)
    (hr : ∀ a, F + 88 ≤ a → a < F + 120 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 749 ω μ x 68729 ω' μ' x 11 ∧
      ω'[0] = UInt64.ofNat 16 ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat k ∧
      ω'[7] = UInt64.ofNat (B + 232 * k) ∧ ω'[8] = UInt64.ofNat (F + 352) ∧
      ω'[9] = UInt64.ofNat 232 ∧
      (∀ a, a < 4294967296 → (a < F + 88 ∨ F + 96 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r40 : rdN μ (F + 56 + 40) 8 = c := by rw [show F + 56 + 40 = F + 96 by omega]; exact rdN_of m40 (by omega)
  have r48 : rdN μ (F + 56 + 48) 8 = B := by rw [show F + 56 + 48 = F + 104 by omega]; exact rdN_of m48 (by omega)
  have r56 : rdN μ (F + 56 + 56) 8 = k := by rw [show F + 56 + 56 = F + 112 by omega]; exact rdN_of m56 (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hF, r40, r48, r56, hk, hc, hB, hw, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show F + 56 + 296 = F + 352 by omega, show F + 56 + 32 = F + 88 by omega]
    post_simp
    all_goals try assumption

/-- 668 … 677 (`DecodeLoop.s5_more` at frame base F): count the element (length k + 1 at F + 112,
    ω₅ − 1 left) and loop to 680. -/
theorem s5_moreF {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F k r : Nat)
    (hF : 65536 ≤ F ∧ F + 1024 < 4294967296)
    (hk : k < 4294967296) (hr2 : 2 ≤ r) (hrb : r < 4294967296)
    (h1 : ω[1] = UInt64.ofNat (F + 56)) (h5 : ω[5] = UInt64.ofNat r) (h6 : ω[6] = UInt64.ofNat k)
    (hw : ∀ a, F + 112 ≤ a → a < F + 120 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 668 ω μ x 680 ω' (μ.writeN (F + 112) (Num.encodeLE 8 (k + 1))) x 4 ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat (r - 1) := by
  rw [show ω = regsNF ω [] from rfl, show F + 112 = F + 56 + 56 by omega]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hF, hk, hr2, hrb, hw]
  · refine ⟨?_, ?_⟩
    post_simp
    all_goals try assumption

/-- 668 … 677 (`DecodeLoop.s5_last` at frame base F): count the last element and leave for 562. -/
theorem s5_lastF {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F k : Nat)
    (hF : 65536 ≤ F ∧ F + 1024 < 4294967296) (hk : k < 4294967296)
    (h1 : ω[1] = UInt64.ofNat (F + 56)) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat k)
    (hw : ∀ a, F + 112 ≤ a → a < F + 120 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 668 ω μ x 562 ω' (μ.writeN (F + 112) (Num.encodeLE 8 (k + 1))) x 4 ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl, show F + 112 = F + 56 + 56 by omega]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hF, hk, hw]
  · refine ⟨?_, ?_⟩
    post_simp
    all_goals try assumption
