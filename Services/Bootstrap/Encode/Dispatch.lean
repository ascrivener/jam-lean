import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.CodeX

/-!
# `Instruction::encode_to` (30145): the dispatch, and the variants without fields

Refine's output is the work items' instructions encoded again (GP v0.8.0 Appendix C, the codec of
sequences, here applied to the service's own `Instruction` type). `Instruction::encode_to` encodes one
instruction, the 232-octet value at S (ω₇), onto the end of the `Vec<u8>` `{cap, ptr, len}` at v (ω₈).
From 30145 the function opens a 56-octet frame at F − 56 (ω₀, ω₅, ω₆ at F − 8, F − 16, F − 24; v at
F − 40), reads the value's first word D, and dispatches on `D − (2^63 − 1)` (0 when D is not one of
the 24 niche words 2^63 … 2^63 + 23) through the table of 25 relative offsets at 67376 (read-only data)
to the variant's arm (`dispatch`). For the variant with tag t ≥ 1 the first word is 2^63 + t − 1, as
`Instruction::decode` writes it (`Decode.Tag`).

The variants without fields, `Checkpoint` (15), `Panic` (16) and `Benchmark` (23), write their tag
octet: the arm stores t at F − 32 and calls `Vec<u8>::extend_from_slice` (58508, `Writer.extend_ok`)
for that one octet; then the function restores ω₀, ω₅, ω₆, closes the frame and returns (`tail`).

`EncOk p P enc Rep` is the contract of one element: for any frame base F, a value satisfying `Rep` and
room for `enc` in the writer, the call appends exactly `enc`. `unit` proves it for the three variants.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The dispatch table at 67376 (in the read-only data): one 32-bit offset per index, relative to
    67376, to the jump-table address of the variant's arm. -/
def table : List UInt8 :=
  [142, 251, 254, 255, 236, 251, 254, 255, 218, 251, 254, 255, 230, 251, 254, 255, 184, 251, 254, 255,
   2, 252, 254, 255, 32, 252, 254, 255, 234, 251, 254, 255, 58, 252, 254, 255, 198, 251, 254, 255,
   48, 252, 254, 255, 166, 251, 254, 255, 190, 251, 254, 255, 18, 252, 254, 255, 164, 251, 254, 255,
   228, 251, 254, 255, 162, 251, 254, 255, 244, 251, 254, 255, 38, 252, 254, 255, 76, 252, 254, 255,
   254, 251, 254, 255, 12, 252, 254, 255, 66, 252, 254, 255, 86, 252, 254, 255, 208, 251, 254, 255]

/-- The table's entries, as unsigned 32-bit words. -/
def ents : List Nat :=
  [4294900622, 4294900716, 4294900698, 4294900710, 4294900664, 4294900738, 4294900768, 4294900714,
   4294900794, 4294900678, 4294900784, 4294900646, 4294900670, 4294900754, 4294900644, 4294900708,
   4294900642, 4294900724, 4294900774, 4294900812, 4294900734, 4294900748, 4294900802, 4294900822,
   4294900688]

/-- The four octets of the table's entry for index t. -/
theorem table_entry {μ : Memory} (tab : μ.readN 67376 100 = table) (t : Nat) (ht : t < 25) :
    μ.readN (67376 + 4 * t) 4 = (table.drop (4 * t)).take 4 := by
  rw [← tab]
  apply List.ext_getElem
  · simp [Memory.readN]; omega
  · intro j h1 h2
    simp only [Memory.readN, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop]
    congr 1; omega

theorem table_val : ∀ t, t < 25 → Num.decodeLE ((table.drop (4 * t)).take 4) = ents.getD t 0 := by
  decide

theorem sxw_table : ∀ t, t < 25 → sxw 4 (ents.getD t 0) = 18446744069414584320 + ents.getD t 0 := by
  decide

/-- The jump-table address the dispatch reaches for index t: 67376 plus the entry, mod 2^64. -/
theorem jaddr : ∀ t, t < 25 → (67376 + (18446744069414584320 + ents.getD t 0)) % 18446744073709551616 =
    [702, 796, 778, 790, 744, 818, 848, 794, 874, 758, 864, 726, 750, 834, 724, 788, 722, 804, 854, 892,
      814, 828, 882, 902, 768].getD t 0 := by
  decide

/-- The arm of the variant with dispatch index t, read off the jump table. -/
def arm (t : Nat) : Nat :=
  [17905, 18925, 18778, 18890, 18369, 19117, 19474, 18919, 19789, 18519, 19650, 18163, 18429, 19322, 18138,
    18884, 18132, 18990, 19538, 19983, 19088, 19256, 19870, 20133, 18639].getD t 0

/-- **The dispatch**: from 30145 with the value at S (ω₇) of discriminant word 2^63 + t − 1
    (1 ≤ t ≤ 24) and the writer at v (ω₈), the function opens its frame at F − 56, saves ω₀, ω₅, ω₆ and
    v there and reaches the arm `arm t`, with ω₁ = F − 56, ω₁₀ = v and ω₁₁ = S. -/
theorem dispatch {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F S v ret r5 r6 t : Nat) (ht : 1 ≤ t ∧ t < 25) (hF : 67476 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat S) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616)
    (hS : S + 8 ≤ 4294967296) (hSF : S + 8 ≤ F - 56 ∨ F ≤ S)
    (hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (hrS : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x (arm t) ω' μ' x 24 ∧
      ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[10] = UInt64.ofNat v ∧ ω'[11] = UInt64.ofNat S ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧ μ'.readN (F - 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rD := rd8 (by omega) hD
  have hrt' : ∀ a, 67376 + 4 * t ≤ a → a < 67376 + 4 * t + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ (67376 + 4 * t) 4 = ents.getD t 0 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [table_entry tab t (by omega)]
    exact table_val t (by omega)
  have hsx := sxw_table t (by omega)
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
      t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨
      t = 21 ∨ t = 22 ∨ t = 23 ∨ t = 24 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;>
  · simp only [ents, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMul, Nat.reduceAdd] at rt hrt' hsx
    simp only [arm, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, hF, hS, hSF, hw, hr, hrS, rD, rt, hrt', hsx, rdN_writeN_disjoint,
        ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
        show F - 56 + 32 = F - 24 by omega, show F - 56 + 16 = F - 40 by omega]
      post_simp
      all_goals try assumption

/-- **The variants without fields**, from their arm (t ∈ {15, 16, 23}): the tag octet t goes to sp + 24
    and the arm calls `Vec<u8>::extend_from_slice` (58508) for it, returning to 904 (→ 20155), with the
    writer v (from ω₁₀) in ω₇. -/
theorem unit_arm {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) (hsp : sp + 32 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R (arm t) ω μ x 58508 ω' (μ.writeN (sp + 24) [UInt8.ofNat t]) x 8 ∧
      ω'[0] = UInt64.ofNat 904 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases ht with rfl | rfl | rfl <;>
  · simp only [arm, List.getD_cons_succ, List.getD_cons_zero]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h10, hsp, hw]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, h1, h10]

/-- 20155 … 20167: the function's end: ω₀, ω₅, ω₆ from the frame at sp (sp + 48, + 40, + 32), the frame
    closed (sp + 56), and the return. -/
theorem tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ret t r5 r6 : Nat) (hsp : sp + 56 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN (sp + 48) 8 = Num.encodeLE 8 ret)
    (s5 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r5) (s6 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp + 32 ≤ a → a < sp + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 20155 ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 56) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have r0 := rd8 (by omega) s0
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, r0, r5', r6', hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', h1]
    all_goals try (congr 1; omega)

/-- **One element encodes** (`Instruction::encode_to`, 30145), at any frame base F: called with ω₁ = F,
    the value at S (ω₇) satisfying `Rep` and the writer `{cap, ptr, len}` at v (ω₈) with room for `enc`,
    the function appends exactly `enc` at `ptr + len`, stores `len + |enc|` and returns to `ret` (whose
    jump-table entry is t) with ω₁, ω₅, ω₆ as they were. Memory changes only in the stack below F (its
    frame and its callees', [F − 136, F)), the octets appended and the writer's length. -/
def EncOk (p : ByteArray) (P : Program) (enc : List UInt8) (Rep : List UInt8 → Prop) : Prop :=
  ∀ (X : Type) (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (F S v cap ptr len ret t : Nat),
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat F → ω[7] = UInt64.ofNat S → ω[8] = UInt64.ofNat v →
    67476 + 256 ≤ F → F < 4294967296 → F % 8 = 0 →
    Rep (μ.readN S 232) → 65536 ≤ S → S + 232 ≤ 4294967296 → (S + 232 ≤ F - 136 ∨ F ≤ S) →
    μ.readN v 8 = Num.encodeLE 8 cap → μ.readN (v + 8) 8 = Num.encodeLE 8 ptr →
    μ.readN (v + 16) 8 = Num.encodeLE 8 len → len + enc.length ≤ cap → cap < 18446744073709551616 →
    v + 24 ≤ 4294967296 → (v + 24 ≤ F - 136 ∨ F ≤ v) →
    65536 ≤ ptr + len → ptr + len + enc.length + 16 < 4294967296 →
    (F ≤ ptr + len ∨ ptr + len + enc.length + 16 ≤ F - 136) →
    (ptr + len + enc.length + 24 ≤ S ∨ S + 232 + 24 ≤ ptr + len) →
    (v + 24 ≤ ptr + len ∨ ptr + len + enc.length ≤ v) →
    μ.readN 67376 100 = table → (∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (∀ a, S ≤ a → a < S + 232 → μ.readable a = true) →
    (∀ a, v ≤ a → a < v + 24 → μ.readable a = true) →
    (∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true) →
    (∀ a, ptr + len ≤ a → a < ptr + len + enc.length → μ.writable a = true) →
    (∀ a, F - 136 ≤ a → a < F → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x t ω' μ' x (7 * enc.length + 4000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (ptr + len) enc.length = enc ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + enc.length) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + enc.length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **`Checkpoint`, `Panic`, `Benchmark`** (t = 15, 16, 23): a value whose first word is the
    discriminant 2^63 + t − 1 encodes to the one octet t. -/
theorem unit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) :
    EncOk p P [UInt8.ofNat t] (fun bs => bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 hF hF' hF8 rep hS hS' hSF vc vp vl hroom hcap hv hvF
    hd hd' hdF hdS hdv tab hrt hret hjt hbt hrS hrv hwv hwd hwF
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at *
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have h5' := UInt64.toNat_lt ω[5]
  have h6' := UInt64.toNat_lt ω[6]
  obtain ⟨ω1, μ1, run1, a1, a10, a11, a0', a5', a6', av', afr, ard, awr⟩ := dispatch (p := p) (P := P) (R := R)
    x ω μ F S v ret ω[5].toNat ω[6].toNat t (by omega) ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega) h5' h6'
    (by omega) (by omega) (by omega) hD tab hrt (fun a h1 h2 => hrS a h1 (by omega))
    (fun a h1 h2 => hwF a (by omega) h2)
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := unit_arm (p := p) (P := P) (R := R) x ω1 μ1 (F - 56) v t ht
    (by omega) a1 a10 (fun a h1 h2 => by rw [awr]; exact hwF a (by omega) (by omega))
  -- the octet at F − 32, and what the write keeps
  have back2 : ∀ a, a < 4294967296 → (a < F - 32 ∨ F - 31 ≤ a) →
      (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).read a = μ1.read a := fun a h0 h1 =>
    Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have hrd1 : ∀ a, (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).readable a = μ.readable a := fun a => by
    rw [Memory.readable_writeN, ard]
  have hwr1 : ∀ a, (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).writable a = μ.writable a := fun a => by
    rw [Memory.writable_writeN, awr]
  have keep2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) →
      (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).read a = μ.read a := fun a h0 h1 => by
    rw [back2 a h0 (by omega), afr a h0 h1]
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω2
    (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]) (F - 56) v (F - 56 + 24) 1 cap ptr len 904 20155
    ⟨by omega, by omega, by omega⟩ b0 b1 b7 b8 b9 hroom hcap
    (by rw [Memory.readN_congr (fun j hj => keep2 _ (by omega) (by omega))]; exact vc)
    (by rw [Memory.readN_congr (fun j hj => keep2 _ (by omega) (by omega))]; exact vp)
    (by rw [Memory.readN_congr (fun j hj => keep2 _ (by omega) (by omega))]; exact vl)
    hv (by omega) ⟨hd, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) hdv
    ⟨by decide, by decide, by decide⟩ jte_451 bs_20155
    (fun a h1 h2 => by rw [hrd1]; exact hrv a h1 h2)
    (fun a h1 h2 => by rw [hwr1]; exact hwv a h1 h2)
    (fun a h1 h2 => by rw [hrd1]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
    (fun a h1 h2 => by rw [hwr1]; exact hwd a h1 h2)
    (fun a h1 h2 => by rw [hwr1]; exact hwF a (by omega) (by omega))
  have keep3 : ∀ a, a < 4294967296 → (a < F - 136 ∨ F - 56 ≤ a) → (a < ptr + len ∨ ptr + len + 1 ≤ a) →
      (a < v + 16 ∨ v + 24 ≤ a) → μ3.read a = (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).read a :=
    fun a h0 h1 h2 h3 => cfr a h0 h1 h2 h3
  obtain ⟨ω4, run4, e0, e1, e5, e6⟩ := tail (p := p) (P := P) (R := R) x ω3 μ3 (F - 56) ret t' ω[5].toNat ω[6].toNat
    (by omega) c1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => keep3 _ (by omega) (by omega)
      (by omega) (by omega)), Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega))]; exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => keep3 _ (by omega) (by omega)
      (by omega) (by omega)), Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega))]; exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => keep3 _ (by omega) (by omega)
      (by omega) (by omega)), Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega))]; exact a6')
    h5' h6' hret hjt hbt
    (fun a h1 h2 => by rw [crd, hrd1]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
  refine ⟨ω4, μ3, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), e0,
    by rw [e1]; congr 1; omega, by rw [e5, ← h5], by rw [e6, ← h6], ?_, cl, fun a h0' h1' h2' h3' => ?_, fun a => by
      rw [crd, hrd1], fun a => by rw [cwr, hwr1]⟩
  · rw [cd]
    exact Memory.readN_writeN_same _ _ _ _ rfl (by simp [two32])
  · rw [cfr a h0' (by omega) h2' h3', back2 a h0' (by omega), afr a h0' (by omega)]

end Services.Bootstrap.Encode.Enc
