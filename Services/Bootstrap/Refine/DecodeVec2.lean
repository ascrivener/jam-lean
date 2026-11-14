import Services.Bootstrap.Refine.DecodeVec
import Services.Bootstrap.Decode.VecKey336Big

/-!
# `Vec<Instruction>::decode`, the second batch: the steps

For 70 < n < 128 instructions `Vec<Instruction>::decode` (482) reserves and decodes a first batch of 70 and then
a second of n − 70 (`min(n − 70, len)` with len = 70): at the first batch's end (562) it reserves the capacity n
with `finish_grow` (32989) on the old buffer, which calls `realloc` (40701; 232-octet slots at alignment 8), and
decodes the rest into the new block. Here the straight-line pieces: `w1` (562 … 32989), `g3x` (`finish_grow` to
`realloc`) and `v2g` (607 … 680 for any capacity and batch). GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's
code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVec

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 562 … 602, the first batch of L done with m more to read (S + 8 = L + m, S + 16 = L, capacity L at S + 40,
    the buffer q at S + 32, ω₇ = L, 1 ≤ m ≤ L): the second batch m at S + 8 and S + 16, L at S + 32, and
    `finish_grow` (32989) called for the capacity L + m (ω₁₀) on the old buffer (ω₈ = L, ω₉ = q; alignment 8,
    element size 232, result at S + 296; return address 14 → 607) with ω₅ = m, ω₆ = L + m. Memory changes only
    at S + 8 … S + 24 and S + 32 … S + 40. -/
theorem w1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S L m q : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hm : 1 ≤ m ∧ m ≤ L) (hL : L < 4294967296)
    (hq : q < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (L + m)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 L)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 562 ω μ x 32989 ω' μ' x 40 ∧ ω'[0] = UInt64.ofNat 14 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat m ∧ ω'[6] = UInt64.ofNat (L + m) ∧ ω'[7] = UInt64.ofNat (S + 296) ∧
      ω'[8] = UInt64.ofNat L ∧ ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + m) ∧
      ω'[11] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 m ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 m ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ (S + 24 ≤ a ∧ a < S + 32) ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r8 := rd8 (by omega) s8
  have r16 := rd8 (by omega) s16
  have r32 := rd8 hq s32
  have r40 := rd8 (by omega) s40
  have hr : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hsub : L + m - L = m := by omega
  have hmin : min m L = m := by omega
  have hm0 : ¬ m = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS0, hS1, hS8, hm, hL, hq, hw, hr, r8, r16, r32, r40, hsub, hmin, hm0, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h7, Nat.mod_eq_of_lt hq]
    all_goals try (congr 1; omega)
    post_simp

/-- 32989 … 33049: `finish_grow` with an old buffer q of capacity L ≥ 1 (ω₈ = L, ω₉ = q) for the new capacity
    N ≥ 1 (ω₁₀) of 232-octet elements at alignment `al`: as `VecKey336.g3k`, it calls `realloc` (40701) for q to
    232·N octets (ω₇ = q, ω₉ = al, ω₁₀ = 232·N, return address 1524), 232·N also at F + 8. -/
theorem g3x {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F res L q N al r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat L)
    (h9 : ω[9] = UInt64.ofNat q) (h10 : ω[10] = UInt64.ofNat N) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat 232)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hL : 1 ≤ L ∧ L < 4294967296) (hN : 1 ≤ N ∧ 232 * N < 1073741760)
    (hal : 1 ≤ al ∧ al ≤ 32) (hq : q < 18446744073709551616)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40701 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1524 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat al ∧ ω'[10] = UInt64.ofNat (232 * N) ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (232 * N) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : 232 * N < 274877906944 := by omega
  have hEn0 : ¬ 232 * N = 0 := by omega
  have hL0 : ¬ L = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, hF, hw, hr, hL, hL0, hN, hal, hEn, hEn0,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp
    all_goals try (congr 1; omega)

/-- 607 … 635 for any batch (`v2` with the capacity N and the batch b apart): `finish_grow` returned `Ok`
    (0 at S + 296) with the block q (S + 304): the `Vec`'s capacity N (ω₆) and buffer q at S + 40, S + 48, q at
    S + 32, and into the element loop (680) with ω₅ = b (from S + 16). Memory changes only at S + 32 … S + 56. -/
theorem v2g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S N b q : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hN : N < 18446744073709551616)
    (hb : 1 ≤ b ∧ b < 18446744073709551616) (hq : q < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat N)
    (s296 : μ.readN (S + 296) 8 = Num.encodeLE 8 0) (s304 : μ.readN (S + 304) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 b) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 70)
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
  have r32 := rd8 (by decide) s32
  have hb0 : ¬ b = 0 := by omega
  have hr2 : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS0, hS1, hS8, hr, hr2, hw, r296, r304, r16, r32, hb0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hb.2]
    all_goals try (congr 1; omega)
    post_simp

end Services.Bootstrap.Refine.DecodeVec
