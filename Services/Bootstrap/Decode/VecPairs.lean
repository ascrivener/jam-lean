import Services.Bootstrap.Decode.VecU8Heap
import Services.Bootstrap.Decode.VecEmpty

/-!
# `Vec<(u64, u64)>`: the pair reader at 3100

The element reader at 3100 (`Import`'s items) reads n pairs of `u64`s into a fresh `Vec` of 16-octet
elements: it reserves min(n, 1024) elements through `finish_grow` (32989, alignment 8, element
size 16), then reads each pair (two 8-octet reads) and pushes it.
-/

namespace Services.Bootstrap.Decode.VecPairs

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 32989 … 33084, `finish_grow` with no old buffer (ω₈ = 0), the new capacity n ≥ 1 (ω₁₀), alignment
    `al` (ω₁₁) and element size E (ω₁₂), the n·E octets fitting below 2⁶³ − al: as `VecU8.g1`, it calls
    `alloc` (40494) for n·E octets at alignment `al` (return address 1526). -/
theorem g1e {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n al E r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat al) (h12 : ω[12] = UInt64.ofNat E)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ n < 4294967296) (hal : 1 ≤ al ∧ al ≤ 32)
    (hE : 1 ≤ E ∧ E ≤ 64)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat (E * n) ∧ ω'[8] = UInt64.ofNat al ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (E * n) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : E * n < 274877906944 := by
    have : E * n ≤ 64 * n := Nat.mul_le_mul_right n hE.2
    omega
  have hEn0 : ¬ E * n = 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) (by omega))
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h10, h11, h12, hF, hw, hr, hn, hal, hE, hEn, hEn0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
    all_goals rw [rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)]

/-- 3100 … 3208, n ≥ 1 pairs: the reader opens a 120-octet frame at S = sp − 120 (ω₀, ω₅, ω₆ at
    S + 112, S + 104, S + 96, rd at S + 32, the empty `Vec` `{cap 0, ptr 8, len 0}` at S + 48, O at S),
    and calls `finish_grow` for the first c = min(n, 1024) elements (ω₁₀ = c, alignment 8, element size
    16, the result slot S + 72, c also at S + 24, 1024 at S + 40; return address 76). -/
theorem p1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd n ret v5 v6 : Nat) (hsp : 65536 + 160 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hret : ret < 18446744073709551616) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hn : 1 ≤ n ∧ n < 4294967296)
    (hw : ∀ a, sp - 120 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3100 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 76 ∧ ω'[1] = UInt64.ofNat (sp - 120) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat (min n 1024) ∧ ω'[7] = UInt64.ofNat (sp - 120 + 72) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat (min n 1024) ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 16 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (sp - 88) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (sp - 120) 8 = Num.encodeLE 8 O ∧ μ'.readN (sp - 96) 8 = Num.encodeLE 8 (min n 1024) ∧
      μ'.readN (sp - 80) 8 = Num.encodeLE 8 1024 ∧ μ'.readN (sp - 56) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 120 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 120 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn0 : ¬ n = 0 := by omega
  have hmin : min n 1024 = if n ≤ 1024 then n else 1024 := by split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hn, hn0, rdN_writeN_disjoint, rdN_writeN_same8,
      rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show sp - 120 + 112 = sp - 8 by omega, show sp - 120 + 104 = sp - 16 by omega,
      show sp - 120 + 96 = sp - 24 by omega, show sp - 120 + 32 = sp - 88 by omega,
      show sp - 120 + 48 = sp - 72 by omega, show sp - 120 + 56 = sp - 64 by omega,
      show sp - 120 + 64 = sp - 56 by omega, show sp - 120 + 40 = sp - 80 by omega,
      show sp - 120 + 24 = sp - 96 by omega]); post_simp
    all_goals try decide

/-- 3213 … 3242: `finish_grow` returned `Ok` with the buffer q (S + 72 holds 0, S + 80 holds q): the
    reader records the `Vec` `{cap c, ptr q}` at S + 48 (c from S + 24), n at S + 16 and c at S + 8, and
    enters its read loop (3277). -/
theorem p4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q n c : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat c)
    (hq : q < 18446744073709551616) (hc : c < 18446744073709551616) (hn : n < 18446744073709551616)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 0) (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 q)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 c) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 1024)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3213 ω μ x 3277 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat c ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 c ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 24 ≤ a) → (a < S + 48 ∨ S + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r72 := rd8' (by decide) s72
  have r80 := rd8' hq s80
  have r24 := rd8' hc s24
  have r40 := rd8' (by decide) s40
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r72, r80, r24, r40, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide
    all_goals assumption

/-- 3277 … 3291: a pass of the read loop begins: the reader zeroes the word at S + 72 and calls the
    reader for 8 octets into it from rd (at S + 32; return address 78). -/
theorem b1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hrd : rd < 18446744073709551616) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3277 ω μ x 58434 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 78 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 72) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (∀ a, a < 4294967296 → (a < S + 72 ∨ S + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r32 := rd8' hrd s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hw, hr, r32, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals assumption

/-- 3297 … 3318: the first read succeeded (ω₇ = 0): the reader keeps the word a from S + 72 at
    S + 40, zeroes S + 72 again and calls the reader for the next 8 octets (ω₅ = rd; return
    address 80). -/
theorem b2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd a0 : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0) (ha : a0 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 a0)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3297 ω μ x 58434 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 80 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 72) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 a0 ∧
      (∀ a, a < 4294967296 → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 72 ∨ S + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r72 := rd8' ha s72
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hS, hw, hr, r72, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals first | assumption | (congr 1; exact Nat.mod_eq_of_lt hrd)

/-- 3324 … 3274, the second read succeeded (ω₇ = 0) with b at S + 72 and more of the chunk to read (r ≥ 2): the reader pushes (a, b) as element k of the buffer q (len k < cap, from S + 64 and S + 48), counts r down and goes back to its loop head (3277). -/
theorem b3c {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q cap k r a0 b0 : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h6 : ω[6] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat 0) (hr : 2 ≤ r) (hrb : r < 4294967296)
    (hk : k < cap ∧ cap < 4294967296) (hq : q + 16 * cap < 4294967296) (ha : a0 < 18446744073709551616)
    (hb : b0 < 18446744073709551616)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 cap) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 k)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 b0) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 a0) (hqS : q + 16 * cap ≤ S)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true)
    (hwq : ∀ a, q + 16 * k ≤ a → a < q + 16 * k + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3324 ω μ x 3277 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ 
      μ'.readN (q + 16 * k) 8 = Num.encodeLE 8 a0 ∧ μ'.readN (q + 16 * k + 8) 8 = Num.encodeLE 8 b0 ∧
      μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → (a < S + 64 ∨ S + 72 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrS : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r48 := rd8' (by omega) s48
  have r64 := rd8' (by omega) s64
  have r72 := rd8' hb s72
  have r56 := rd8' (by omega) s56
  have r40 := rd8' ha s40
  have hkc : ¬ k = cap := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hr, hrb, hS, hw, hrS, hwq, r48, r64, r72, r56, r40, hk, hkc, hq, hqS, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show q + k * 16 = q + 16 * k by omega]); post_simp
    all_goals try assumption

/-- 3324 … 3274, as `b3c`, for the last element of the chunk (r = 1): after the push the reader leaves its loop for its chunk check (3169), with ω₇ = k + 1. -/
theorem b3l {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q cap k r a0 b0 : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h6 : ω[6] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat 0) (hr : r = 1)
    (hk : k < cap ∧ cap < 4294967296) (hq : q + 16 * cap < 4294967296) (ha : a0 < 18446744073709551616)
    (hb : b0 < 18446744073709551616)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 cap) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 k)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 b0) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 a0) (hqS : q + 16 * cap ≤ S)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true)
    (hwq : ∀ a, q + 16 * k ≤ a → a < q + 16 * k + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3324 ω μ x 3169 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ ω'[7] = UInt64.ofNat (k + 1) ∧
      μ'.readN (q + 16 * k) 8 = Num.encodeLE 8 a0 ∧ μ'.readN (q + 16 * k + 8) 8 = Num.encodeLE 8 b0 ∧
      μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → (a < S + 64 ∨ S + 72 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrS : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r48 := rd8' (by omega) s48
  have r64 := rd8' (by omega) s64
  have r72 := rd8' hb s72
  have r56 := rd8' (by omega) s56
  have r40 := rd8' ha s40
  have hkc : ¬ k = cap := by omega
  subst hr
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hS, hw, hrS, hwq, r48, r64, r72, r56, r40, hk, hkc, hq, hqS, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show q + k * 16 = q + 16 * k by omega]); post_simp
    all_goals try assumption

/-- 3169 … 3184: every element read (n from S + 16 equals the chunk c from S + 8): the reader leaves
    its reserve loop for its end (3445). Memory is unchanged. -/
theorem ex1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hn : n < 18446744073709551616)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3169 ω μ x 3445 ω' μ x 8 ∧ ω'[1] = UInt64.ofNat S := by
  have r16 := rd8' hn s16
  have r8 := rd8' hn s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, r16, r8, ↓rdN_fold]
  · post_simp
    all_goals try assumption

/-- 3445 … 3443: the reader stores the `Vec` `{cap, ptr q, len}` (from S + 48, S + 56, S + 64) at O
    (from S), restores ω₀, ω₅, ω₆ and returns. -/
theorem ex2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O cap q len ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ S ∨ S + 120 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S)
    (hcap : cap < 4294967296) (hq : q < 4294967296) (hlen : len < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 cap) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 len) (s0 : μ.readN S 8 = Num.encodeLE 8 O)
    (s112 : μ.readN (S + 112) 8 = Num.encodeLE 8 ret) (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 v5)
    (s96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3445 ω μ x t ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 120) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 72 ∨ S + 88 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r48 := rd8' (by omega) s48
  have r56 := rd8' (by omega) s56
  have r64 := rd8' (by omega) s64
  have r0 := rd8' (by omega) s0
  have r112 := rd8' (by omega) s112
  have r104 := rd8' hv5 s104
  have r96 := rd8' hv6 s96
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hO, hOS, hw, hr, hwO, r48, r56, r64, r0, r112, r104, r96, hcap, hq, hlen, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide

/-- **One pass of the read loop** (3277 … 3277, or 3169 after the last element of the chunk): with
    k < n elements pushed into q (S + 56; cap n at S + 48, len k at S + 64), r = n − k left in the
    chunk (ω₆), and the reader rd (S + 32) at ptr₀ + 16k, the reader reads the next 16 octets as a
    pair and pushes it as element k. The payload and the buffer lie below the reader's frames. -/
theorem pass {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q n k r rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 120 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 1 ≤ r ∧ k + r = n)
    (hn : n < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 n)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 k)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * k))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * k))
    (hlen : 16 * n ≤ len0 ∧ len0 < 4294967296) (hrd : S + 120 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 16 * n + 16 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 16 * n + 16 ≤ S - 88)
    (hpq : q + 16 * n ≤ ptr0 ∨ ptr0 + 16 * n ≤ q)
    (hws : ∀ a, S - 88 ≤ a → a < S + 120 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwq : ∀ a, q ≤ a → a < q + 16 * n → μ.writable a = true)
    (hra : ∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 3277 ω μ x (if r = 1 then 3169 else 3277) ω' μ' x 260 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
      μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
      μ'.readN (q + 16 * k) 16 = μ.readN (ptr0 + 16 * k) 16 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (k + 1)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (k + 1)) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  -- the first u64
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ :=
    b1 (p := p) (P := P) (R := R) x ω μ S rd ⟨by omega, by omega⟩ h1 hrd64 s32
      (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, ⟨c0, c1, -, -, -, c5, c6, -, c7, cR0, cR8, cbuf, cfr, crd, cwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 78 3297 S rd (S + 72) (ptr0 + 16 * k) (len0 - 16 * k) 8 a0 a1
      a7 a8 a9 (by decide) jte_38 bs_3297 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8)
  have hA : μ2.readN (S + 72) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) := by
    rw [cbuf, encodeLE_rdN]
    exact Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))
  -- the second u64
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, d7, d8, d9, d40, fr3, rd3, wr3⟩ :=
    b2 (p := p) (P := P) (R := R) x ω2 μ2 S rd (rdN μ (ptr0 + 16 * k) 8) ⟨by omega, by omega⟩
      (by rw [c1, a1]) (by rw [c5, a5]) c7 (rdN_lt64 _ _) hrd64 hA
      (fun a h1 h2 => by rw [cwr, wr1]; exact hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨e0, e1, -, -, -, e5, e6, -, e7, eR0, eR8, ebuf, efr, erd, ewr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 80 3324 S rd (S + 72) (ptr0 + 16 * k + 8) (len0 - 16 * k - 8) 8
      d0 d1 d7 d8 d9 (by decide) jte_39 bs_3324 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, crd, rd1]; exact hra a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (by omega) (by omega))]; exact cR0)
      (by rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (by omega) (by omega)),
            show len0 - 16 * k - 8 = len0 - 16 * k - 8 from rfl]; exact cR8)
  have hB : μ4.readN (S + 72) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k + 8) 8) := by
    rw [ebuf, encodeLE_rdN]
    exact Memory.readN_congr (fun j hj => (fr3 _ (by omega) (by omega) (by omega)).trans
      ((cfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
        (fr1 _ (by omega) (by omega))))
  -- the stack slots the reads keep
  have k4 : ∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 72 ∨ S + 80 ≤ a) →
      (a < rd ∨ rd + 16 ≤ a) → μ4.read a = μ.read a := fun a h0 h1 h2 h3 h4 =>
    (efr a h0 h1 h4 h3).trans ((fr3 a h0 h2 h3).trans ((cfr a h0 h1 h4 h3).trans (fr1 a h0 h3)))
  have w4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [ewr, wr3, cwr, wr1]
  have r4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [erd, rd3, crd, rd1]
  have h40 : μ4.readN (S + 40) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) := by
    rw [Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega))]; exact d40
  have run14 := run1.trans (run2.trans (run3.trans run4))
  have fin : ∀ (ω5 : Regs) (μ5 : Memory) (pc : Nat), FreeStepsH p R 3324 ω4 μ4 x pc ω5 μ5 x 20 →
      ω5[1] = UInt64.ofNat S → ω5[6] = UInt64.ofNat (r - 1) →
      μ5.readN (q + 16 * k) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) →
      μ5.readN (q + 16 * k + 8) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k + 8) 8) →
      μ5.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) →
      (∀ a, a < 4294967296 → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → (a < S + 64 ∨ S + 72 ≤ a) →
        μ5.read a = μ4.read a) →
      (∀ a, μ5.readable a = μ4.readable a) → (∀ a, μ5.writable a = μ4.writable a) →
      ∃ ω' μ', FreeStepsH p R 3277 ω μ x pc ω' μ' x 260 ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
        μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
        μ'.readN (q + 16 * k) 16 = μ.readN (ptr0 + 16 * k) 16 ∧
        μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (k + 1)) ∧
        μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (k + 1)) ∧
        (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
          (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
    intro ω5 μ5 pc run5 f1 f6 fa fb f64 ffr frd fwr
    refine ⟨ω5, μ5, (run14.trans run5).mono (by omega), f1, f6, f64, ?_, ?_, ?_,
      fun a h0 h1 h2 h3 h4 h5 => (ffr a h0 h5 (by omega)).trans (k4 a h0 h1 h2 (by omega) h4),
      fun a => by rw [frd, r4], fun a => by rw [fwr, w4]⟩
    · rw [show (16 : Nat) = 8 + 8 from rfl, readN_split, readN_split, fa, encodeLE_rdN,
        show q + 16 * k + 8 = q + 16 * k + 8 from rfl]
      rw [fb, encodeLE_rdN]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))), eR0,
        show ptr0 + 16 * k + 8 + 8 = ptr0 + 16 * (k + 1) by omega]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))), eR8,
        show len0 - 16 * k - 8 - 8 = len0 - 16 * (k + 1) by omega]
  by_cases hr1 : r = 1
  · subst hr1
    rw [if_pos rfl]
    obtain ⟨ω5, μ5, run5, f1, f6, -, fa, fb, f64, ffr, frd, fwr⟩ :=
      b3l (p := p) (P := P) (R := R) x ω4 μ4 S q n k 1 (rdN μ (ptr0 + 16 * k) 8) (rdN μ (ptr0 + 16 * k + 8) 8)
        ⟨by omega, by omega⟩ (by rw [e1, d1]) (by rw [e6, d6, c6, a6, h6]) e7 rfl ⟨by omega, hn⟩
        (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s64)
        hB
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s56)
        h40 (by omega)
        (fun a h1 h2 => by rw [w4]; exact hws a (by omega) (by omega))
        (fun a h1 h2 => by rw [w4]; exact hwq a (by omega) (by omega))
    exact fin ω5 μ5 3169 run5 f1 f6 fa fb f64 ffr frd fwr
  · rw [if_neg hr1]
    obtain ⟨ω5, μ5, run5, f1, f6, fa, fb, f64, ffr, frd, fwr⟩ :=
      b3c (p := p) (P := P) (R := R) x ω4 μ4 S q n k r (rdN μ (ptr0 + 16 * k) 8) (rdN μ (ptr0 + 16 * k + 8) 8)
        ⟨by omega, by omega⟩ (by rw [e1, d1]) (by rw [e6, d6, c6, a6, h6]) e7 (by omega) (by omega)
        ⟨by omega, hn⟩ (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s64)
        hB
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s56)
        h40 (by omega)
        (fun a h1 h2 => by rw [w4]; exact hws a (by omega) (by omega))
        (fun a h1 h2 => by rw [w4]; exact hwq a (by omega) (by omega))
    exact fin ω5 μ5 3277 run5 f1 f6 fa fb f64 ffr frd fwr

/-- **The read loop** (3277 … 3169): from k < n elements pushed, r = n − k left, as `pass`, the reader
    pushes the remaining pairs: the buffer q then holds the payload's first 16n octets and the reader
    is advanced to ptr₀ + 16n. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S q n rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 120 < 4294967296) (hn : n < 4294967296)
    (hlen : 16 * n ≤ len0 ∧ len0 < 4294967296) (hrd : S + 120 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 16 * n + 16 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 16 * n + 16 ≤ S - 88)
    (hpq : q + 16 * n ≤ ptr0 ∨ ptr0 + 16 * n ≤ q) :
    ∀ r k (ω : Regs) (μ : Memory), ω[1] = UInt64.ofNat S → ω[6] = UInt64.ofNat r → 1 ≤ r → k + r = n →
    μ.readN (S + 32) 8 = Num.encodeLE 8 rd → μ.readN (S + 48) 8 = Num.encodeLE 8 n →
    μ.readN (S + 56) 8 = Num.encodeLE 8 q → μ.readN (S + 64) 8 = Num.encodeLE 8 k →
    μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * k) → μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * k) →
    μ.readN q (16 * k) = μ.readN ptr0 (16 * k) →
    (∀ a, S - 88 ≤ a → a < S + 120 → μ.writable a = true) →
    (∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) →
    (∀ a, q ≤ a → a < q + 16 * n → μ.writable a = true) →
    (∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ.readable a = true) →
    ∃ ω' μ', FreeStepsH p R 3277 ω μ x 3169 ω' μ' x (260 * r) ∧
      ω'[1] = UInt64.ofNat S ∧ μ'.readN (S + 64) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (16 * n) = μ.readN ptr0 (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * n) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * n ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro r
  induction r with
  | zero => intro k ω μ _ _ h; exact absurd h (by decide)
  | succ r ih =>
  intro k ω μ h1 h6 hr1 hkr s32 s48 s56 s64 hR0 hR8 hdat hws hwr hwq hra
  obtain ⟨ω1, μ1, run1, a1, a6, a64, adat, aR0, aR8, afr, ard, awr⟩ :=
    pass (p := p) (P := P) (R := R) x ω μ S q n k (r + 1) rd ptr0 len0 hS h1 h6 ⟨hr1, hkr⟩ hn s32 s48 s56 s64
      hR0 hR8 hlen hrd hptr hq hpq hws hwr hwq hra
  have hpay : ∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ1.read a = μ.read a := fun a h1 h2 =>
    afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by rcases hpq with h | h <;> omega)
  have hdat1 : μ1.readN q (16 * (k + 1)) = μ1.readN ptr0 (16 * (k + 1)) := by
    rw [show 16 * (k + 1) = 16 * k + 16 by omega, readN_split, readN_split, adat,
      Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega))), hdat,
      Memory.readN_congr (μ' := μ1) (a := ptr0) (n := 16 * k) (fun j hj => hpay _ (by omega) (by omega)),
      Memory.readN_congr (μ' := μ1) (a := ptr0 + 16 * k) (n := 16) (fun j hj => hpay _ (by omega) (by omega))]
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos rfl] at run1
    have hk : k + 1 = n := by omega
    refine ⟨ω1, μ1, run1.mono (by omega), a1, by rw [a64, hk], ?_, by rw [aR0, hk], by rw [aR8, hk],
      fun a h0 h1 h2 h3 h4 h5 => afr a h0 h1 h2 h3 h4 (by omega), ard, awr⟩
    rw [← hk, hdat1]
    exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
  · rw [if_neg (by omega)] at run1
    obtain ⟨ω', μ', run', e1, e64, edat, eR0, eR8, efr, erd, ewr⟩ :=
      ih (k + 1) ω1 μ1 a1 (by rw [a6]; congr 1) (by omega) (by omega)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s32)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s56)
        a64 aR0 aR8 hdat1
        (fun a h1 h2 => by rw [awr]; exact hws a h1 h2) (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
        (fun a h1 h2 => by rw [awr]; exact hwq a h1 h2) (fun a h1 h2 => by rw [ard]; exact hra a h1 h2)
    refine ⟨ω', μ', (run1.trans run').mono (by rw [Nat.mul_succ]; omega), e1, e64, ?_, eR0, eR8,
      fun a h0 h1 h2 h3 h4 h5 => (efr a h0 h1 h2 h3 h4 (by omega)).trans (afr a h0 h1 h2 h3 h4 (by omega)),
      fun a => by rw [erd, ard], fun a => by rw [ewr, awr]⟩
    rw [edat]; exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA in
/-- **Reading 1 … 1024 pairs into a fresh `Vec<(u64, u64)>`, the payload in the heap** (3100): with
    ω₇ = O, ω₈ = rd, ω₉ = n, the allocator's context `HeapCtx` (under `refineContractK cap`, cap ≥ 2²⁷)
    and the 16n payload octets inside an allocated chunk's data, either the model's `alloc` of
    ⌈16n/32⌉ units gives `(q, s')` and the reader returns to t with the `Vec` `{cap n, ptr q, len n}` at
    O, q holding the payload's 16n octets (the n pairs, each two little-endian `u64`s), the context kept
    for `s'` and every allocated chunk of `s` kept with its data; or the model's `alloc` fails and the
    run reaches the `alloc` wrapper's return (40611) with null. -/
theorem vec_pairs_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 16 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 328 ≤ sp ∧ sp ≤ S1) (hsp : 2147483976 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 1024) (hnl : 16 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 3100 ω μ x t ω' μ' x (260 * n + 800) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q (16 * n) = μ.readN ptr (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 16 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 16 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 3100 ω μ x 40611 ω' μ' x (260 * n + 800) ∧
      ω'[7] = UInt64.ofNat 0) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  have hmin : min n 1024 = n := by omega
  -- the frame and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m88, m120, m96, m80, m56, fr1,
      rd1, wr1⟩ := p1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 (by omega) hv5 hv6 (by omega) (by omega) ⟨hn.1, by omega⟩
    (fun a h1 h2 => hst a (by omega) (by omega))
  rw [hmin] at a6 a10 m96
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 160) (sp - 120 + 72) n 8 16 76 n n
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨hn.1, by omega⟩ (by decide) (by decide)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 160 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 160) (16 * n) 8 pb S0 S1 H2 b1
      b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ⟨hna, ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), e7⟩
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 160 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 160) (sp - 120 + 72) (16 * n) q 76 3213 n n
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_37 bs_3213
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  -- the frame S = sp − 120 in μ5
  have hS5 : ∀ a, sp - 120 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d1, d6, d48, d56, d16, d8, fr6, rd6, wr6⟩ :=
    p4 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 120) q n n ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega)
      (by rw [show sp - 120 + 72 = sp - 120 + 72 from rfl]; exact cres)
      (by rw [show sp - 120 + 80 = sp - 120 + 72 + 8 by omega]; exact cres8)
      (by rw [show sp - 120 + 24 = sp - 96 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 120 + 40 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS6 : ∀ a, sp - 120 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → (a < sp - 112 ∨ sp - 96 ≤ a) →
      (a < sp - 72 ∨ sp - 56 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (fr6 a h2 (by omega) (by omega)).trans (hS5 a h1 h2 h3)
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans
      (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hdq : q + 16 * n ≤ ptr ∨ ptr + 16 * n ≤ q := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the loop
  obtain ⟨ω7, μ7, run7, f1, f64, fdat, fR0, fR8, ffr, frd, fwr⟩ :=
    loop (p := p) (P := P) (R := refineContractK cap env) x (sp - 120) q n rd ptr len ⟨by omega, by omega⟩
      (by omega) ⟨hnl, hlen⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hdq n 0 ω6 μ6 d1 d6
      hn.1 (by omega)
      (by rw [show sp - 120 + 32 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
      d48 d56
      (by rw [show sp - 120 + 64 = sp - 56 by omega, Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m56)
      (by rw [show ptr + 16 * 0 = ptr by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [show len - 16 * 0 = len by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      rfl
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  have h76 : ∀ a, sp - 120 ≤ a → a < sp → (a < sp - 80 ∨ sp - 72 ≤ a) → (a < sp - 56 ∨ sp - 40 ≤ a) →
      μ7.read a = μ6.read a := fun a h1 h2 h3 h4 =>
    ffr a (by omega) (Or.inr (by omega)) (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))
  obtain ⟨ω8, run8, g81⟩ :=
    ex1 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (sp - 120) n ⟨by omega, by omega⟩ f1 (by omega)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d16)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d8)
      (fun a h1 h2 => by rw [frd]; exact Memory.readable_of_writable (by rw [wr36]; exact H3.st a (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, z0, z1, z5, z6, zO, zO8, zO16, fr9, rd9, wr9⟩ :=
    ex2 (p := p) (P := P) (R := refineContractK cap env) x ω8 μ7 (sp - 120) O n q n ret t v5 v6 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) g81 (by omega) (by omega) (by omega) hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d48)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d56)
      f64
      (by rw [Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega) (by omega)).trans
            (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m120)
      (by rw [show sp - 120 + 112 = sp - 8 by omega, Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega) (by omega)).trans
            (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m8)
      (by rw [show sp - 120 + 104 = sp - 16 by omega, Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega) (by omega)).trans
            (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m16)
      (by rw [show sp - 120 + 96 = sp - 24 by omega, Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega) (by omega)).trans
            (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => by rw [fwr, wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr, wr36]; exact H3.st a (by omega) (by omega))
  -- the heap after the loop and the return
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 16 * n ≤ a) → μ9.read a = μ3.read a := fun a h1 h3 =>
    (fr9 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((ffr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (by omega)).trans (h63 a h1))
  have run19 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans run9)))))))
  have wr9' : ∀ a, μ9.writable a = μ3.writable a := fun a => by rw [wr9, fwr, wr36]
  refine Or.inl ⟨q, s', ω9, μ9, ha, run19.mono (by omega), z0, by rw [z1]; congr 1; omega, z5, z6, zO, zO8, zO16,
    ?_, ?_, ?_, ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr9', keep, hnew,
    hfresh, ?_, FreeStepsH.pagesOut H.bd run19, ?_⟩
  · rw [Memory.readN_congr (fun j hj => fr9 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))), fdat]
    exact Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)
  · rw [Memory.readN_congr (fun j hj => fr9 _ (by omega) (Or.inr (by omega)) (by omega)), fR0]
  · rw [Memory.readN_congr (fun j hj => fr9 _ (by omega) (Or.inr (by omega)) (by omega)), fR8]
  · intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2 h3
    rw [fr9 a h0 (Or.inr (by omega)) h3, ffr a h0 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) h2
      (Or.inr (by omega))]
    exact hhigh a h0 h1

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecEmpty in
/-- **`Import { items }` with 1 … 1024 items, the payload in the heap**: from 20626 with tag 9 read
    without error, and the reader `{ptr, len}` at rd (ω₆) holding ℰ(n) (w octets) and the n items (16
    octets each), all inside an allocated chunk of the allocator's state `s` (context `HeapCtx`, under
    `refineContractK cap`): either the model's `alloc` of ⌈16n/32⌉ units gives `(q, s')` and
    `Instruction::decode` returns `Import` in O (the discriminant word 2^63 + 8 and the `Vec`
    `{cap n, ptr q, len n}` at O + 8, q holding the 16n item octets), the reader advanced by w + 16n,
    the context kept for `s'` and every allocated chunk of `s` kept with its data; or the model's `alloc`
    fails and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem import_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (htg : μ.read A = UInt8.ofNat 9) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 376 ≤ A ∧ A + 56 ≤ S1) (hA8 : 2147484024 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 1024)
    (hlen : (Blob.encodeNat n).length + 16 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat n).length + 16 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (260 * n + 2000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775816 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (16 * n) = μ.readN (ptr + (Blob.encodeNat n).length) (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat n).length + 16 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat n).length - 16 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a)) ∨
    (alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (260 * n + 2000) ∧
      ω'[7] = UInt64.ofNat 0) := by
  have hA2 := F.hA
  have hS1 := H.hS1
  have hst := H.st
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen hpay henc hw1 ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hs : Shape 21028 956 1106 1108 3100 := by unfold Shape; simp
  obtain ⟨bs1, bs2, bs3⟩ := shape_bs (p := p) (P := P) hs
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 9
    (by decide) (by omega) F.h1 h7 htg tab (F.hr A (by omega) (by omega)) hrt
  rw [show handler 9 = 21028 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    e1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ 21028 956 1106 1108 3100 A O rd hs ⟨by omega, by omega⟩
      (e1'.trans F.h1) (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
  have hra : ∀ a, ptr ≤ a → a < ptr + w + 16 * n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω3, μ3, run3, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1106 _ (A - 48) rd ptr len b0 b1 b7
      (by decide) rfl bs2 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [brd]; exact hra a h1 (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := e2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    21028 956 1106 1108 3100 (A - 48) n hs (by omega) (by omega) (by rw [d1, b1]) d7 d8
  have b3 : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [dwr, bwr]
  have H3 : HeapCtx env pb S0 S1 μ3 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr3
  have run04 := run1.trans (run2.trans (run3.trans run4))
  rcases vec_pairs_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48) rd (ptr + w)
      (len - w) n 1108 _ O rd pb S0 S1 H3 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) (by rw [c6, d6, b6]) c7
      (by rw [c8, d6, b6]) c9 (by decide) rfl bs3 hO64 (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω5, μ5, ha, run5, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H5, keep, cm5, hfresh, kd5, pg5, vfr⟩ |
    ⟨hna, ω5, μ5, run5, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω5, μ5, (run04.trans run5).mono (by omega), f7⟩
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + 16 * n < 2147483648 := by
    have := chunk_in H5.wf cm5 rfl; simp only at this; rw [hbase'] at this; omega
  have hfrH : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))).trans
      (dfr a (by omega) (by omega) (Or.inl (by omega)))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fO, fO8, fO16, fO24, ffr, frd, fwr⟩ :=
    e3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 21028 956 1106 1108 3100 9223372036854775816
      (A - 48) O n q n O rd hs (by simp) ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega)
      (by omega) (by omega) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
      μ6.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (ffr a h0 h3).trans ((vfr a h0 (by omega) h2 (Or.inr (by omega))).trans (b3 a h0 (Or.inr h1) h2))
  have hlow : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a h => ffr a (by omega) (Or.inl (by omega))
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H5 cm5 (fun a h1 _ => hlow a h1) fwr
  obtain ⟨ω7, run7, g0, g1, g5, g6⟩ := e4 (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    21028 956 1106 1108 3100 A ret t v5 v6 hs ⟨by omega, by omega⟩ (by rw [f1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => Memory.readable_of_writable (H6.st a (by omega) (by omega)))
  have run := run04.trans (run5.trans (run6.trans run7))
  refine Or.inl ⟨q, s', ω7, μ6, ha, run.mono (by omega), g0, g1, g5, g6, fO, fO8, fO16, fO24, ?_, ?_, ?_,
    H6, keep, cm5, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      have hia' := hia
      unfold InData at hia'
      rw [hlow a (by omega), kd5 c hc hu a hia]
      exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, hfar⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
  · have e : ∀ j, j < 8 → μ6.read (rd + j) = μ5.read (rd + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ6.read (rd + 8 + j) = μ5.read (rd + 8 + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR8]


end Services.Bootstrap.Decode.VecPairs
