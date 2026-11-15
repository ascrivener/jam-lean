import Services.Bootstrap.Refine.DecodeVec2

/-!
# `Vec<Instruction>::decode`, every batch: the steps

`Vec<Instruction>::decode` (482) decodes its n elements in batches. The first batch is min(n, 70); each later batch
is min(m, L), where m is the count still to read and L the length so far (so the batches are 70, 70, 140, 280, …),
and before each later batch the buffer is grown to exactly L + min(m, L) slots with `finish_grow` (32989) on the old
buffer, which calls `realloc` (40701). `DecodeVec2.w1` and `v2g` cover the second batch only (L = 70, the previous
batch L). Here the same steps for any batch: `w1G` (562 … 32989) and `v2gG` (607 … 680). GP v0.8.0 Appendix B.4
(Ψ_R running bootstrap's code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVec

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 562 … 602, a batch b done (the count R before it at S + 8, b at S + 16), with m = R − b ≥ 1 more to read,
    the length L ≥ 1 (ω₇) equal to the capacity (S + 40) and the buffer q at S + 32: the next batch
    b' = min(m, L), with m at S + 8, b' at S + 16 and L at S + 32, and `finish_grow` (32989) called for the
    capacity L + b' (ω₁₀) on the old buffer (ω₈ = L, ω₉ = q; alignment 8, element size 232, result at S + 296;
    return address 14 → 607) with ω₅ = m, ω₆ = L + b'. Memory changes only at S + 8 … S + 24 and
    S + 32 … S + 40. -/
theorem w1G {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S Rc b L q : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hb : b + 1 ≤ Rc) (hRc : Rc < 4294967296)
    (hL : 1 ≤ L ∧ L < 4294967296) (hq : q < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 Rc) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 b)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 562 ω μ x 32989 ω' μ' x 40 ∧ ω'[0] = UInt64.ofNat 14 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat (Rc - b) ∧ ω'[6] = UInt64.ofNat (L + min (Rc - b) L) ∧
      ω'[7] = UInt64.ofNat (S + 296) ∧
      ω'[8] = UInt64.ofNat L ∧ ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + min (Rc - b) L) ∧
      ω'[11] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 (Rc - b) ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 (min (Rc - b) L) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ (S + 24 ≤ a ∧ a < S + 32) ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  obtain ⟨m, hm⟩ : ∃ m, m = Rc - b := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = min m L := ⟨_, rfl⟩
  rw [← hm, ← hb']
  have r8 := rd8 (by omega) s8
  have r16 := rd8 (by omega) s16
  have r32 := rd8 hq s32
  have r40 := rd8 (by omega) s40
  have hr : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsub : Rc - b = m := hm.symm
  have hmin : min m L = b' := hb'.symm
  have hLL : L - L = 0 := Nat.sub_self L
  have hm0 : ¬ m = 0 := by omega
  have hb'0 : 0 < b' := by omega
  have hb'L : b' ≤ L := by omega
  have hite : (if m ≤ L then m else L) = b' := by rw [hb']; rfl
  have hb'm : b' % 18446744073709551616 = b' := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS0, hS1, hS8, hL, hq, hw, hr, r8, r16, r32, r40, hsub, hmin, hite, hb'm, hLL, hm0, hb'0, hb'L,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h7, Nat.mod_eq_of_lt hq, hite, hb'm]
    all_goals try (congr 1; omega)
    post_simp

/-- 607 … 635 for any batch and length (`v2g` with S + 32 = L for any L ≥ 1, not only 70): `finish_grow`
    returned `Ok` (0 at S + 296) with the block q (S + 304): the `Vec`'s capacity N (ω₆) and buffer q at S + 40,
    S + 48, q at S + 32, and into the element loop (680) with ω₅ = b (from S + 16). Memory changes only at
    S + 32 … S + 56. -/
theorem v2gG {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S N b q L : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hN : N < 18446744073709551616)
    (hb : 1 ≤ b ∧ b < 18446744073709551616) (hq : q < 18446744073709551616)
    (hL : 1 ≤ L ∧ L < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat N)
    (s296 : μ.readN (S + 296) 8 = Num.encodeLE 8 0) (s304 : μ.readN (S + 304) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 b) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 L)
    (hr : ∀ a, S + 296 ≤ a → a < S + 312 → μ.readable a = true)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 607 ω μ x 680 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat b ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 N ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r296 := rd8 (by decide) s296
  have r304 := rd8 hq s304
  have r16 := rd8 hb.2 s16
  have r32 := rd8 hL.2 s32
  have hb0 : ¬ b = 0 := by omega
  have hL0 : ¬ L = 0 := by omega
  have hr2 : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS0, hS1, hS8, hr, hr2, hw, r296, r304, r16, r32, hb0, hL0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hb.2]
    all_goals try (congr 1; omega)
    post_simp

end Services.Bootstrap.Refine.DecodeVec
