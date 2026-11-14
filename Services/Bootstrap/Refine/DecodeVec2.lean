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

/-- 531 … 602, the first batch of b = min(n, 70) (`v1b` for any n): as `v1b`, with n at S + 8, ω₅ = n, and the
    batch b at S + 16, ω₆ and ω₁₀. -/
theorem v1bG {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S n b : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : 1 ≤ b ∧ b = min n 70) (hn64 : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h7 : ω[7] = UInt64.ofNat 0)
    (h9 : ω[9] = UInt64.ofNat 8) (h12 : ω[12] = UInt64.ofNat 70)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 0)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 531 ω μ x 32989 ω' μ' x 30 ∧ ω'[0] = UInt64.ofNat 14 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat b ∧ ω'[7] = UInt64.ofNat (S + 296) ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat b ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 b ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 70 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ (S + 24 ≤ a ∧ a < S + 32) ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r40 := rd8 (by decide) s40
  have hr : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hmin : min n 70 = b := by omega
  have hmin2 : (if n ≤ 70 then n else 70) = b := by split <;> omega
  have hb64 : b % 18446744073709551616 = b := Nat.mod_eq_of_lt (by omega)
  have hb0 : ¬ b = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, h9, h12, hS0, hS1, hS8, hw, hr, r40, hmin, hmin2, hb64, hb0, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h9, Nat.mod_eq_of_lt hn64, hmin2, hb64]
    all_goals try (congr 1; omega)
    post_simp


open Picoalloc Services.Bootstrap.Alloc Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop in
/-- **`Vec<Instruction>::decode` up to the element loop, the first batch of any** (482 … 680): as `vec_pre`, for
    ntot instructions in all, the first batch es of min(ntot, 70) (here 1 ≤ |es| ≤ 70 instructions es,
    their encodings at P0 in the payload's chunk cp, the heap's first chunk, and the reader at rd over them):
    the frame S = ω₁ − 552, the empty `Vec`, `finish_grow` for n slots of 232 octets, and the loop's state
    `InvAF` for k = 0 with the frame F = S − 56 and the buffer q in the new chunk cb (`OkF` holds). The
    wrapper's words at S (output), S + 8, S + 16 (n), S + 528 … S + 552 (ω₆, ω₅, return 922) are set. Or the
    allocation fails. -/
theorem vec_preG {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat}
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (S out rd P0 Lt v5 v6 : Nat) (es : List (List UInt8)) (reps : Nat → List UInt8 → Memory → Prop) (cp : Chunk)
    (ntot : Nat) (hnt : es.length = min ntot 70) (hnt64 : ntot < 4294967296)
    (hn : 1 ≤ es.length ∧ es.length ≤ 70) (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hS : S0 + 2104 ≤ S ∧ S + 552 ≤ rd ∧ rd + 16 ≤ S1 ∧ S % 8 = 0)
    (hout : out < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base)
    (hcpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a) (hP0 : 206864 ≤ P0)
    (hLt : es.flatten.length ≤ Lt ∧ Lt < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 922) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat ntot)
    (sR0 : μ.readN rd 8 = Num.encodeLE 8 P0) (sR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 Lt)
    (pay : μ.readN P0 es.flatten.length = es.flatten)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (q : Nat) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 482 ω μ x 680 ω' μ' x N ∧
      InvAF env pb (S - 56) rd P0 Lt es reps 0 q cp ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ ω' μ' s' ∧
      OkF (S - 56) rd P0 Lt es q ∧
      μ'.readN S 8 = Num.encodeLE 8 out ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 ntot ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (S + 544) 8 = Num.encodeLE 8 922 ∧
      μ'.readN (S + 536) 8 = Num.encodeLE 8 v5 ∧ μ'.readN (S + 528) 8 = Num.encodeLE 8 v6 ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → S + 552 ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ∃ N, Exhausts env cap0 pb p P 482 ω μ x N := by
  obtain ⟨hS0, hSr, hrS, hS8⟩ := hS
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm, hcpu, hcpa⟩ := hcp
  have hSt := H.st
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  rw [hN] at hn hnt ⊢
  have wS : ∀ a, S - 40 ≤ a → a < S + 552 → μ.writable a = true := fun a h1 h2 => hSt a (by omega) (by omega)
  -- 482 … 531, 531 … 32989
  obtain ⟨ω1, μ1, run1, a1, a5, a7, a9, a12, a0', a24, a40, a48, a56, a544, a536, a528, afr, ard, awr⟩ := v1a
    (p := p) (P := P) (R := refineContractK cap0 env) x ω μ S out rd ntot 922 v5 v6 ⟨by omega, by omega, hS8⟩
    (by omega) (by omega) hout (by omega) (by decide) hv5 hv6 h0 h1 h5 h6 h7 h8 h9
    (fun a h1 h2 => wS a (by omega) h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, b10, b11, b12, b8', b16, b32, bfr, brd, bwr⟩ := v1bG (p := p)
    (P := P) (R := refineContractK cap0 env) x ω1 μ1 S ntot n ⟨by omega, by omega, hS8⟩ ⟨hn.1, hnt⟩ (by omega) a1 a5 a7 a9 a12 a40
    (fun a h1 h2 => by rw [awr]; exact wS a (by omega) (by omega))
  -- `finish_grow`, `alloc`, back to 607
  obtain ⟨ω3, μ3, run3, c0, c1, c6, c7, c8, c32, c24, c16, c8', cfr, crd, cwr⟩ := g1x (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 (S - 40) (S + 296) n 8 232 14 ntot n ⟨by omega, by omega⟩ b0
    (by rw [b1]; congr 1; omega) b5 b6 b7 b8 b10 b11 b12 (by decide) (by omega) (by omega) (by omega)
    ⟨by omega, by omega⟩ (by decide) (by decide)
    (fun a h1 h2 => by rw [bwr, awr]; exact wS a h1 (by omega))
  have hlow3 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a h =>
    by rw [cfr a (by omega) (Or.inl (by omega)), bfr a (by omega) (Or.inl (by omega)),
      afr a (by omega) (Or.inl (by omega))]
  have H3 : HeapCtx env pb S0 S1 μ3 s := Decode.GrowOne.ctx_high H hlow3 (fun a => by rw [cwr, bwr, awr])
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω3 μ3 s (S - 40) (232 * n) 8 pb S0 S1 H3
      c1 c7 c8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω4, μ4, ha, run4, H4, keep, hnew, hfresh, hk, e7, stk4, e0, e1, e5, e6⟩ |
    ⟨hna, ω4, μ4, run4, e7, -⟩
  rotate_left
  · exact Or.inr ⟨_, Exhausts.of_alloc (run1.trans (run2.trans (run3.trans run4))) e7 hna⟩
  obtain ⟨hqb, hqT, hqT'⟩ := Decode.VecU8.chunk_in H4.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have hq32 : (q - 32) % 32 = 0 := by
    have ht := H4.wf.2.2.2.1; unfold TilesOk at ht
    have := Decode.VecKey336.tiles_mod _ _ ht _ hnew
    simp only at this
    have := H4.wf.2.1
    omega
  have run5 := alloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω4 μ4 (by rw [e0, c0])
  have hF4 : ∀ a, S - 40 ≤ a → a < 4294967296 → μ4.read a = μ3.read a := fun a h1 h2 => stk4 a h2 h1
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d296, d304, d312, dfr, drd, dwr⟩ := g2 (p := p) (P := P)
    (R := refineContractK cap0 env) x ω4 μ4 (S - 40) (S + 296) (232 * n) q 14 607 ntot n
    ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, c1]) (by rw [e6, c6]) e7 ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
    (by rw [Memory.readN_congr (fun j hj => hF4 _ (by omega) (by omega))]; exact c32)
    (by rw [Memory.readN_congr (fun j hj => hF4 _ (by omega) (by omega))]; exact c24)
    (by rw [Memory.readN_congr (fun j hj => hF4 _ (by omega) (by omega))]; exact c16)
    (by rw [Memory.readN_congr (fun j hj => hF4 _ (by omega) (by omega))]; exact c8')
    ⟨by decide, by decide, by decide⟩ jte_6 bs_607
    (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    (fun a h1 h2 => H4.st a (by omega) (by omega))
  -- the stack from S up, μ6 against μ2
  have k62 : ∀ a, a < 4294967296 → S ≤ a → (a < S + 296 ∨ S + 320 ≤ a) → μ6.read a = μ2.read a := fun a h0 h1 h2 => by
    rw [dfr a h0 h2, hF4 a (by omega) h0, cfr a h0 (Or.inr (by omega))]
  have r62 : ∀ a l, S ≤ a → a + l ≤ 4294967296 → (a + l ≤ S + 296 ∨ S + 320 ≤ a) → μ6.readN a l = μ2.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => k62 _ (by omega) (by omega) (by omega))
  obtain ⟨ω7, μ7, run7, f1, f5, f32, f40, f48, ffr, frd, fwr⟩ := v2 (p := p) (P := P)
    (R := refineContractK cap0 env) x ω6 μ6 S n q ⟨by omega, by omega, hS8⟩ (by omega) (by omega)
    (by rw [d1]; congr 1; omega) d6 d296 d304
    (by rw [r62 _ _ (by omega) (by omega) (by omega)]; exact b16)
    (by rw [r62 _ _ (by omega) (by omega) (by omega)]; exact b32)
    (fun a h1 h2 => by rw [drd]; exact Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    (fun a h1 h2 => by rw [dwr]; exact H4.st a (by omega) (by omega))
  have run := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  -- memory: the stack above S + 552, the heap's chunks, the low globals
  have k7 : ∀ a, a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → (a < S + 296 ∨ S + 320 ≤ a) → S ≤ a →
      μ7.read a = μ2.read a := fun a h0 h1 h2 h3 => by rw [ffr a h0 h1, k62 a h0 h3 h2]
  have r7 : ∀ a l, S ≤ a → a + l ≤ 4294967296 → (a + l ≤ S + 32 ∨ S + 56 ≤ a) → (a + l ≤ S + 296 ∨ S + 320 ≤ a) →
      μ7.readN a l = μ2.readN a l :=
    fun a l h0 h1 h2 h3 => Memory.readN_congr (fun j hj => k7 _ (by omega) (by omega) (by omega) (by omega))
  have r21 : ∀ a l, a + l ≤ 4294967296 → (a + l ≤ S + 8 ∨ (S + 24 ≤ a ∧ a + l ≤ S + 32) ∨ S + 40 ≤ a) →
      μ2.readN a l = μ1.readN a l := fun a l h0 h1 => Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))
  have r10 : ∀ a l, a + l ≤ 4294967296 → S + 552 ≤ a → μ1.readN a l = μ.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
  have ht4 := H4.wf.2.2.2.1
  unfold TilesOk at ht4
  have hD : ∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ7.read a = μ.read a := fun c hc hu a ha => by
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
    have ha' := ha; unfold InData at ha'
    rw [ffr a (by omega) (Or.inl (by omega)), dfr a (by omega) (Or.inl (by omega)),
      hk.hkeep a (off_hdr_data H4.wf H4.hb0 H4.hbT (keep c hc hu) ha'.1 ha'.2), hlow3 a (by omega)]
  have hlow7 : ∀ a, a < 2147483648 → μ7.read a = μ4.read a := fun a h =>
    by rw [ffr a (by omega) (Or.inl (by omega)), dfr a (by omega) (Or.inl (by omega))]
  have w74 : ∀ a, μ7.writable a = μ4.writable a := fun a => by rw [fwr, dwr]
  have H7 : HeapCtx env pb S0 S1 μ7 s' := Decode.GrowOne.ctx_high H4 hlow7 w74
  obtain ⟨tab7, rtab7⟩ := ExitRun.ro_keep H run (a := 67476) (l := 100) (by omega)
  -- the buffer after the payload: the payload's chunk is the heap's first
  have hcp4 := keep cp hcpm hcpu
  have hcpne := hfresh cp hcpm hcpu
  have hflat : 1 ≤ es.flatten.length := by
    have h0 := off_lt es 0 (by omega)
    have h1 := hne 0 (by omega)
    omega
  have hfl : P0 + es.flatten.length ≤ cp.addr + 32 * cp.size := by
    have := hcpd (P0 + es.flatten.length - 1) (by omega) (by omega)
    unfold InData at this
    omega
  have hap := PassLoop.chunk_apart H4.wf hcp4 hnew hcpne
  simp only at hap
  have hcpsz : 1 ≤ cp.size := by
    have := hcpd P0 (Nat.le_refl _) (by omega)
    unfold InData at this; omega
  have hqP : P0 + es.flatten.length ≤ q := by
    rcases hap with h | h
    · omega
    · omega
  have hqa : q % 8 = 0 := by
    have := H4.wf.2.1
    omega
  refine Or.inl ⟨ω7, μ7, s', q, _, run, ⟨by rw [f1]; congr 1; omega, by rw [f5, hN, Nat.sub_zero],
    ?_, by rw [show S - 56 + 96 = S + 40 by omega, f40, hN], by rw [show S - 56 + 104 = S + 48 by omega]; exact f48,
    ?_, ?_, ?_, ?_, tab7.trans tab, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun a h1 h2 => by rw [w74]; exact H4.st a (by omega) (by omega),
    fun a h1 h2 => by rw [w74]; exact H4.st a (by omega) (by omega),
    fun a h1 h2 => by rw [rtab7 a h1 h2]; exact rt a h1 h2, H7, ⟨hcp4, hcpu⟩, hcpd, ⟨hnew, rfl⟩,
    fun a h1 h2 => ⟨by simp; omega, by simp; omega⟩⟩,
    ⟨by omega, hqP, hqa, by omega, fun j hj => hne j (by omega), hP0, hLt.1, hLt.2, by omega, by omega, by omega,
      by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc hu => ⟨keep c hc hu, hD c hc hu⟩, hfresh, fun a h0 h1 => ?_,
    fun a ha => ?_⟩
  · rw [show S - 56 + 80 = S + 24 by omega, r7 _ _ (by omega) (by omega) (by omega) (by omega),
      r21 _ _ (by omega) (by omega)]; exact a24
  · rw [show S - 56 + 112 = S + 56 by omega, r7 _ _ (by omega) (by omega) (by omega) (by omega),
      r21 _ _ (by omega) (by omega)]; exact a56
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega),
      r10 _ _ (by omega) (by omega)]; simpa [off] using sR0
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega),
      r10 _ _ (by omega) (by omega)]; simpa [off] using sR8
  · rw [Memory.readN_congr (fun j hj => hD cp hcpm hcpu _ (hcpd _ (by omega) (by omega)))]; exact pay
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega)]; exact a0'
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega)]; exact b8'
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega)]; exact b16
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega)]; exact a544
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega)]; exact a536
  · rw [r7 _ _ (by omega) (by omega) (by omega) (by omega), r21 _ _ (by omega) (by omega)]; exact a528
  · rw [k7 a h0 (by omega) (by omega) (by omega), bfr a h0 (by omega), afr a h0 (by omega)]
  · have hg := ha; unfold Glob at hg
    rw [hlow7 a (by omega), hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht4.mem_lt c hc).1; omega)) a ha,
      hlow3 a (by omega)]


end Services.Bootstrap.Refine.DecodeVec
