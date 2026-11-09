import Services.Bootstrap.Code
import PVM.Logic.Go

/-!
# `Instruction::decode`: the tag dispatch

`Instruction::decode` (`jam-bootstrap-service-common` 0.1.29) reads the tag octet with the reader
and returns to 20626, with ω₁ = A the function's frame (the tag at A, the return address and the
caller's ω₅, ω₆ saved at A + 48, A + 40, A + 32) and ω₅ = O the 232-octet slot for the result.
From there:

* the reader failed (ω₇ ≠ 0), or the tag is 25 or more: the error word 2^64 − 2 goes to O and the
  function returns (`reject`);
* otherwise the table of 25 relative offsets at 67476 sends tag t to its variant's decoder at
  `handler t` (`dispatch`). The tags are the declaration order of `Instruction`.

The variants without fields, `Checkpoint` (15), `Panic` (16) and `Benchmark` (23), are decoded at
once: their discriminant word 2^63 + t − 1 goes to O and the function returns (`unit_variant`).
-/

namespace Services.Bootstrap.Decode.Tag

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The decoder of the `Instruction` variant with tag t (t < 25), read off the jump table. -/
def handler (t : Nat) : Nat :=
  [20677, 21350, 21132, 21219, 20914, 21522, 21741, 21284, 21918, 21028, 21871, 20857, 20971, 21657,
    20778, 21193, 20752, 21416, 21807, 22072, 21477, 21569, 21975, 22119, 21075].getD t 0

/-- The dispatch table at 67476 (in the read-only data): one 32-bit offset per tag, relative to 67476,
    to the jump-table address of the tag's decoder. -/
def table : List UInt8 :=
  [16, 252, 254, 255, 60, 252, 254, 255, 46, 252, 254, 255, 52, 252, 254, 255, 30, 252, 254, 255,
   72, 252, 254, 255, 84, 252, 254, 255, 56, 252, 254, 255, 96, 252, 254, 255, 38, 252, 254, 255,
   92, 252, 254, 255, 26, 252, 254, 255, 34, 252, 254, 255, 80, 252, 254, 255, 22, 252, 254, 255,
   50, 252, 254, 255, 20, 252, 254, 255, 64, 252, 254, 255, 88, 252, 254, 255, 104, 252, 254, 255,
   68, 252, 254, 255, 76, 252, 254, 255, 100, 252, 254, 255, 108, 252, 254, 255, 42, 252, 254, 255]

/-- The four octets of the table's entry for tag t. -/
theorem table_entry {μ : Memory} (tab : μ.readN 67476 100 = table) (t : Nat) (ht : t < 25) :
    μ.readN (67476 + 4 * t) 4 = (table.drop (4 * t)).take 4 := by
  rw [← tab]
  apply List.ext_getElem
  · simp [Memory.readN]; omega
  · intro j h1 h2
    simp only [Memory.readN, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    congr 1; omega

/-- The low octet of each table entry; the other three are 252, 254, 255. -/
def offs : List Nat := [16, 60, 46, 52, 30, 72, 84, 56, 96, 38, 92, 26, 34, 80, 22, 50, 20, 64, 88, 104, 68, 76,
  100, 108, 42]

theorem sxw_table : ∀ t, t < 25 → sxw 4 (4294900736 + offs.getD t 0) = 18446744073709485056 + offs.getD t 0 := by
  decide

theorem table_val : ∀ t, t < 25 → Num.decodeLE ((table.drop (4 * t)).take 4) = 4294900736 + offs.getD t 0 := by
  decide

/-- One tag: from 20626, with tag t < 25 read without error (ω₇ = 0), the dispatch reaches
    `handler t` in at most 12 steps, changing neither memory nor ω₀, ω₁, ω₅, ω₆. -/
theorem dispatch {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A t : Nat)
    (ht : t < 25) (hA : A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h7 : ω[7] = UInt64.ofNat 0) (tag : μ.read A = UInt8.ofNat t)
    (tab : μ.readN 67476 100 = table) (hr : μ.readable A = true)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 20626 ω μ x (handler t) ω' μ x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rb : rdN μ A 1 = t := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp; omega
  have hrt' : ∀ a, 67476 + 4 * t ≤ a → a < 67476 + 4 * t + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ (67476 + 4 * t) 4 = 4294900736 + offs.getD t 0 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [table_entry tab t ht]
    exact table_val t ht
  rw [show ω = regsNF ω [] from rfl]
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨
      t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;>
  · simp only [offs, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd] at rt hrt'
    simp only [handler, List.getD_cons_succ, List.getD_cons_zero]
    have hsx := sxw_table _ ht
    simp only [offs, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd] at hsx
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [hA, h1, h7, rt, rb, hr, hrt', hsx, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none]

/-- The function's end, from one of its exits: store the word W at O (ω₅), restore ω₀, ω₅, ω₆ and
    sp from the frame at A, and return. The exits are `Checkpoint`'s (21193), `Panic`'s (20752) and
    `Benchmark`'s (22119) decoders, and the error exit (20629), with their words. -/
theorem finish {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (e W A O ret t v5 v6 : Nat)
    (he : (e = 21193 ∧ W = 9223372036854775822) ∨ (e = 20752 ∧ W = 9223372036854775823) ∨
      (e = 22119 ∧ W = 9223372036854775830) ∨ (e = 20629 ∧ W = 18446744073709551614))
    (hA : A + 56 < 4294967296) (hO : O + 8 ≤ 4294967296) (hOA : O + 8 ≤ A + 32 ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 8 → μ.writable a = true)
    (hr : ∀ a, A + 32 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R e ω μ x t ω' (μ.writeN O (Num.encodeLE 8 W)) x 8 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have r0 : rdN μ (A + 48) 8 = ret := by
    show Num.decodeLE _ = _
    rw [s0, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]
  have r5 : rdN μ (A + 40) 8 = v5 := by
    show Num.decodeLE _ = _
    rw [s5, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv5]
  have r6 : rdN μ (A + 32) 8 = v6 := by
    show Num.decodeLE _ = _
    rw [s6, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv6]
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hA, hO, hOA, hw, hr, r0, r5, r6, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', h1]
      all_goals try (congr 1; omega)

/-- To the error exit: from 20626, the reader failed (ω₇ ≠ 0), or it read a tag t ≥ 25. -/
theorem to_error {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A t : Nat)
    (hA : A < 4294967296) (h1 : ω[1] = UInt64.ofNat A)
    (hbad : ω[7] ≠ UInt64.ofNat 0 ∨ (ω[7] = UInt64.ofNat 0 ∧ μ.read A = UInt8.ofNat t ∧ 25 ≤ t ∧ t < 256))
    (hr : μ.readable A = true) :
    ∃ ω', FreeStepsH p R 20626 ω μ x 20629 ω' μ x 5 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hbad with h7 | ⟨h7, tag, ht, ht'⟩
  · have h7' : ¬ (ω[7]).toNat = 0 := fun h => h7 (UInt64.toNat.inj (by rw [h]; rfl))
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h7']
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · have rb : rdN μ A 1 = t := by
      simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
        Num.decodeLE]
      simp; omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [hA, h1, h7, rb, hr, ht, ht', ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none]

/-- The frame `Instruction::decode` returns through: ω₁ = A, ω₅ = O, the return address `ret` (whose
    jump-table entry is `t`) and the caller's ω₅, ω₆ saved at A + 48, A + 40, A + 32, and the access
    the end needs. -/
structure Frame (P : Program) (A O ret t v5 v6 : Nat) (ω : Regs) (μ : Memory) : Prop where
  hA : A + 56 < 4294967296
  hO : O + 8 ≤ 4294967296
  hOA : O + 8 ≤ A + 32 ∨ A + 56 ≤ O
  h1 : ω[1] = UInt64.ofNat A
  h5 : ω[5] = UInt64.ofNat O
  hv5 : v5 < 18446744073709551616
  hv6 : v6 < 18446744073709551616
  s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret
  s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5
  s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6
  hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0
  hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t
  hbt : P.isBlockStart t = true
  hw : ∀ a, O ≤ a → a < O + 8 → μ.writable a = true
  hr : ∀ a, A ≤ a → a < A + 56 → μ.readable a = true

/-- **Reject**: from 20626, if the reader failed or the tag is 25 or more, `Instruction::decode`
    returns the error word 2^64 − 2 in its slot O. -/
theorem reject {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 tag : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hbad : ω[7] ≠ UInt64.ofNat 0 ∨ (ω[7] = UInt64.ofNat 0 ∧ μ.read A = UInt8.ofNat tag ∧ 25 ≤ tag ∧ tag < 256)) :
    ∃ ω', FreeStepsH p R 20626 ω μ x t ω' (μ.writeN O (Num.encodeLE 8 18446744073709551614)) x 13 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := to_error (p := p) (P := P) (R := R) x ω μ A tag (by have := F.hA; omega) F.h1 hbad
    (F.hr A (by omega) (by have := F.hA; omega))
  obtain ⟨ω2, run2, post⟩ := finish (p := p) (P := P) (R := R) x ω1 μ 20629 18446744073709551614 A O ret t v5 v6
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) F.hA F.hO F.hOA (e1.trans F.h1) (e5.trans F.h5) F.hv5 F.hv6
    F.s0 F.s5 F.s6 F.hret F.hjt F.hbt F.hw (fun a h1 h2 => F.hr a (by omega) h2)
  exact ⟨ω2, (run1.trans run2).mono (by omega), post⟩

/-- **The variants without fields**: from 20626, with tag t ∈ {15, 16, 23} (`Checkpoint`, `Panic`,
    `Benchmark`) read without error, `Instruction::decode` returns the variant's discriminant word
    2^63 + t − 1 in its slot O, having read nothing more. -/
theorem unit_variant {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 tag : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (htag : tag = 15 ∨ tag = 16 ∨ tag = 23) (h7 : ω[7] = UInt64.ofNat 0)
    (hrd : μ.read A = UInt8.ofNat tag) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 20626 ω μ x t ω' (μ.writeN O (Num.encodeLE 8 (9223372036854775807 + tag))) x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have h25 : tag < 25 := by omega
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A tag h25 (by have := F.hA; omega) F.h1 h7 hrd
    tab (F.hr A (by omega) (by have := F.hA; omega)) hrt
  have he : (handler tag = 21193 ∧ 9223372036854775807 + tag = 9223372036854775822) ∨
      (handler tag = 20752 ∧ 9223372036854775807 + tag = 9223372036854775823) ∨
      (handler tag = 22119 ∧ 9223372036854775807 + tag = 9223372036854775830) ∨
      (handler tag = 20629 ∧ 9223372036854775807 + tag = 18446744073709551614) := by
    rcases htag with rfl | rfl | rfl <;> simp [handler]
  obtain ⟨ω2, run2, post⟩ := finish (p := p) (P := P) (R := R) x ω1 μ (handler tag) (9223372036854775807 + tag) A O ret t v5 v6
    he F.hA F.hO F.hOA (e1.trans F.h1) (e5.trans F.h5) F.hv5 F.hv6
    F.s0 F.s5 F.s6 F.hret F.hjt F.hbt F.hw (fun a h1 h2 => F.hr a (by omega) h2)
  exact ⟨ω2, (run1.trans run2).mono (by omega), post⟩

end Services.Bootstrap.Decode.Tag
