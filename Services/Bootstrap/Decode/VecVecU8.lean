import Services.Bootstrap.Decode.VecPairs

/-!
# `Vec<Vec<u8>>`: the element reader at 8

The element reader at 8 (the items of `DeleteItems`, `Export` and `Imported`) reads n byte strings
into a fresh `Vec` of 24-octet elements (each a `Vec<u8>`): it reserves min(n, 682) elements through
`finish_grow` (32989, alignment 8, element size 24), then for each element decodes its length with the
length decoder (31894), reads its octets with `read_vec` (3473) and pushes the `Vec<u8>` it gets.
-/

namespace Services.Bootstrap.Decode.VecVecU8

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 8 … 114, n ≥ 1 elements: the reader opens a 128-octet frame at S = sp − 128 (ω₀, ω₅, ω₆ at
    S + 120, S + 112, S + 104, rd at S + 24, O at S + 16, the empty `Vec` `{cap 0, ptr 8, len 0}` at
    S + 32), and calls `finish_grow` for the first c = min(n, 682) elements (ω₁₀ = c, alignment 8,
    element size 24, the result slot S + 80, c also at S, 682 at S + 8; return address 2). -/
theorem q1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd n ret v5 v6 : Nat) (hsp : 65536 + 168 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hret : ret < 18446744073709551616) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hn : 1 ≤ n ∧ n < 4294967296)
    (hw : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2 ∧ ω'[1] = UInt64.ofNat (sp - 128) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat (min n 682) ∧ ω'[7] = UInt64.ofNat (sp - 128 + 80) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat (min n 682) ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 24 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (sp - 104) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (sp - 112) 8 = Num.encodeLE 8 O ∧ μ'.readN (sp - 128) 8 = Num.encodeLE 8 (min n 682) ∧
      μ'.readN (sp - 120) 8 = Num.encodeLE 8 682 ∧ μ'.readN (sp - 80) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn0 : ¬ n = 0 := by omega
  have hc : 0 < (if n ≤ 682 then n else 682) % 18446744073709551616 := by split <;> omega
  have hc' : (if n ≤ 682 then n else 682) = min n 682 := by split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hn, hn0, hc, rdN_writeN_disjoint, rdN_writeN_same8,
      rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [hc'])
    all_goals (try simp only [show sp - 128 + 120 = sp - 8 by omega, show sp - 128 + 112 = sp - 16 by omega,
      show sp - 128 + 104 = sp - 24 by omega, show sp - 128 + 24 = sp - 104 by omega,
      show sp - 128 + 16 = sp - 112 by omega, show sp - 128 + 32 = sp - 96 by omega,
      show sp - 128 + 40 = sp - 88 by omega, show sp - 128 + 48 = sp - 80 by omega,
      show sp - 128 + 8 = sp - 120 by omega]); post_simp
    all_goals try decide

/-- 120 … 147: `finish_grow` returned `Ok` with the buffer q (S + 80 holds 0, S + 88 holds q): the
    reader records the `Vec` `{cap c, ptr q}` at S + 32 (c from S), n at S + 8 and c at S, and enters
    its read loop (197). -/
theorem q4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q n c : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat c)
    (hq : q < 18446744073709551616) (hc : c < 18446744073709551616) (hn : n < 18446744073709551616)
    (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 0) (s88 : μ.readN (S + 88) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 c) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 682)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 120 ω μ x 197 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat c ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 c ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN S 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 16 ≤ a) → (a < S + 32 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r80 := rd8' (by decide) s80
  have r88 := rd8' hq s88
  have r0 := rd8' hc s0
  have r8 := rd8' (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r80, r88, r0, r8, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide
    all_goals assumption

/-- 197 … 202: a pass of the read loop begins: the reader loads rd (from S + 24) into ω₅ and ω₇ and
    calls the length decoder (31894; return address 4). -/
theorem r1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hrd : rd < 18446744073709551616) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd)
    (hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 197 ω μ x 31894 ω' μ x 4 ∧ ω'[0] = UInt64.ofNat 4 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat rd ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat rd := by
  have r24 := rd8' hrd s24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, r24, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals (try simp only [Nat.mod_eq_of_lt hrd])
    all_goals try assumption

/-- 207 … 224: the length decoder returned `Ok` (ω₇ = 0) with the length m (ω₈): the reader calls
    `read_vec` (3473) for m octets from rd (ω₅) into the slot S + 56 (return address 6). Memory is
    unchanged. -/
theorem r2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd m : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat m)
    (hm : m < 4294967296) (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 207 ω μ x 3473 ω' μ x 7 ∧ ω'[0] = UInt64.ofNat 6 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat rd ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (S + 56) ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat m := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, h8, hS, hm]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals (try simp only [Nat.mod_eq_of_lt hrd])
    all_goals try assumption

/-- 229 … 194, k < cap: `read_vec` stored the `Vec<u8>` `{e0, e1, e2}` at S + 56 (e0 ≠ 2⁶⁴ − 1): the
    reader pushes it as element k of the buffer q (S + 40; cap at S + 32, len k at S + 48), at
    q + 24k, and with r ≥ 2 left in the chunk (ω₆) starts the next pass (197). -/
theorem r3c {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q cap k r e0 e1 e2 : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h6 : ω[6] = UInt64.ofNat r) (hr : 2 ≤ r) (hrb : r < 4294967296)
    (hk : k < cap ∧ cap < 4294967296) (hq : q + 24 * cap < 4294967296)
    (he0 : e0 < 4294967296) (he1 : e1 < 4294967296) (he2 : e2 < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 k)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 e0)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 e1) (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 e2)
    (hqS : q + 24 * cap ≤ S)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true)
    (hwq : ∀ a, q + 24 * k ≤ a → a < q + 24 * k + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 229 ω μ x 197 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
      μ'.readN (q + 24 * k) 8 = Num.encodeLE 8 e0 ∧ μ'.readN (q + 24 * k + 8) 8 = Num.encodeLE 8 e1 ∧
      μ'.readN (q + 24 * k + 16) 8 = Num.encodeLE 8 e2 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) → (a < S + 48 ∨ S + 56 ≤ a) →
        (a < S + 80 ∨ S + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrS : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r32 := rd8' (by omega) s32
  have r48 := rd8' (by omega) s48
  have r40 := rd8' (by omega) s40
  have r56 := rd8' (by omega) s56
  have r64 := rd8' (by omega) s64
  have r72 := rd8' (by omega) s72
  have hkc : ¬ k = cap := by omega
  have he0' : ¬ e0 = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hr, hrb, hS, hw, hrS, hwq, r32, r48, r40, r56, r64, r72, hk, hkc, hq, hqS, he0', he0, he1, he2,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show k * 8 + k * 16 + q = q + 24 * k by omega, show q + (k * 16 + k * 8) = q + 24 * k by omega]); post_simp
    all_goals try assumption

/-- 229 … 194, as `r3c`, for the last element of the chunk (r = 1): after the push the reader leaves
    its loop for its chunk check (77), with ω₇ = k + 1. -/
theorem r3l {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q cap k r e0 e1 e2 : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h6 : ω[6] = UInt64.ofNat r) (hr : r = 1)
    (hk : k < cap ∧ cap < 4294967296) (hq : q + 24 * cap < 4294967296)
    (he0 : e0 < 4294967296) (he1 : e1 < 4294967296) (he2 : e2 < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 k)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 e0)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 e1) (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 e2)
    (hqS : q + 24 * cap ≤ S)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true)
    (hwq : ∀ a, q + 24 * k ≤ a → a < q + 24 * k + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 229 ω μ x 77 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ ω'[7] = UInt64.ofNat (k + 1) ∧
      μ'.readN (q + 24 * k) 8 = Num.encodeLE 8 e0 ∧ μ'.readN (q + 24 * k + 8) 8 = Num.encodeLE 8 e1 ∧
      μ'.readN (q + 24 * k + 16) 8 = Num.encodeLE 8 e2 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) → (a < S + 48 ∨ S + 56 ≤ a) →
        (a < S + 80 ∨ S + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrS : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r32 := rd8' (by omega) s32
  have r48 := rd8' (by omega) s48
  have r40 := rd8' (by omega) s40
  have r56 := rd8' (by omega) s56
  have r64 := rd8' (by omega) s64
  have r72 := rd8' (by omega) s72
  have hkc : ¬ k = cap := by omega
  have he0' : ¬ e0 = 18446744073709551615 := by omega
  subst hr
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, hw, hrS, hwq, r32, r48, r40, r56, r64, r72, hk, hkc, hq, hqS, he0', he0, he1, he2,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show k * 8 + k * 16 + q = q + 24 * k by omega, show q + (k * 16 + k * 8) = q + 24 * k by omega]); post_simp
    all_goals try assumption

/-- 77 … 91: every element read (n from S + 8 equals the chunk c from S): the reader leaves its
    reserve loop for its end (456). Memory is unchanged. -/
theorem x1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hn : n < 18446744073709551616)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n) (s0 : μ.readN S 8 = Num.encodeLE 8 n)
    (hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 77 ω μ x 456 ω' μ x 8 ∧ ω'[1] = UInt64.ofNat S := by
  have r8 := rd8' hn s8
  have r0 := rd8' hn s0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, r8, r0, ↓rdN_fold]
  · post_simp
    all_goals try assumption

/-- 456 … 454: the reader stores the `Vec` `{cap, ptr q, len}` (from S + 32, S + 40, S + 48) at O
    (from S + 16), restores ω₀, ω₅, ω₆ and returns. -/
theorem x2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O cap q len ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ S ∨ S + 128 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S)
    (hcap : cap < 4294967296) (hq : q < 4294967296) (hlen : len < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 len) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 O)
    (s120 : μ.readN (S + 120) 8 = Num.encodeLE 8 ret) (s112 : μ.readN (S + 112) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 456 ω μ x t ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 128) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 80 ∨ S + 96 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r32 := rd8' (by omega) s32
  have r40 := rd8' (by omega) s40
  have r48 := rd8' (by omega) s48
  have r16 := rd8' (by omega) s16
  have r120 := rd8' (by omega) s120
  have r112 := rd8' hv5 s112
  have r104 := rd8' hv6 s104
  have hc' : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hO, hOS, hw, hr, hwO, r32, r40, r48, r16, r120, r112, r104, hcap, hc', hq, hlen, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide

/-- 229 … 194, any r ≥ 1 left in the chunk: `r3c` (r ≥ 2, back to 197) or `r3l` (r = 1, on to 77). -/
theorem r3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q cap k r e0 e1 e2 : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h6 : ω[6] = UInt64.ofNat r) (hr : 1 ≤ r ∧ r < 4294967296)
    (hk : k < cap ∧ cap < 4294967296) (hq : q + 24 * cap < 4294967296)
    (he0 : e0 < 4294967296) (he1 : e1 < 4294967296) (he2 : e2 < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 k)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 e0)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 e1) (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 e2)
    (hqS : q + 24 * cap ≤ S)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true)
    (hwq : ∀ a, q + 24 * k ≤ a → a < q + 24 * k + 24 → μ.writable a = true) :
    ∃ j ω' μ', FreeStepsH p R 229 ω μ x j ω' μ' x 30 ∧
      (2 ≤ r → j = 197) ∧ (r = 1 → j = 77 ∧ ω'[7] = UInt64.ofNat (k + 1)) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
      μ'.readN (q + 24 * k) 8 = Num.encodeLE 8 e0 ∧ μ'.readN (q + 24 * k + 8) 8 = Num.encodeLE 8 e1 ∧
      μ'.readN (q + 24 * k + 16) 8 = Num.encodeLE 8 e2 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) → (a < S + 48 ∨ S + 56 ≤ a) →
        (a < S + 80 ∨ S + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  by_cases h2 : 2 ≤ r
  · obtain ⟨ω', μ', run, a1, a6, a0, a8, a16, a48, afr, ard, awr⟩ :=
      r3c (p := p) (P := P) (R := R) x ω μ S q cap k r e0 e1 e2 hS h1 h6 h2 hr.2 hk hq he0 he1 he2 s32 s48 s40 s56 s64 s72 hqS hw hwq
    exact ⟨197, ω', μ', run, fun _ => rfl, fun h => absurd h (by omega), a1, a6, a0, a8, a16, a48, afr, ard, awr⟩
  · obtain ⟨ω', μ', run, a1, a6, a7, a0, a8, a16, a48, afr, ard, awr⟩ :=
      r3l (p := p) (P := P) (R := R) x ω μ S q cap k r e0 e1 e2 hS h1 h6 (by omega) hk hq he0 he1 he2 s32 s48 s40 s56 s64 s72 hqS hw hwq
    exact ⟨77, ω', μ', run, fun h => absurd h h2, fun _ => ⟨rfl, a7⟩, a1, a6, a0, a8, a16, a48, afr, ard, awr⟩

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **One element read** (197 … 229): with the reader rd (S + 24) at ptr, whose next octets are
    ℰ(m) ++ e (m = |e| ≤ 16384) inside an allocated chunk, the reader decodes the length and calls
    `read_vec`, which leaves the `Vec<u8>` `{m, qe, m}` at S + 56: for m = 0 the dangling pointer 1
    and no allocation; for m ≥ 1 a fresh block qe (a new allocated chunk, listed in `cs`) holding e,
    or the model's `alloc` fails. The context, every allocated chunk of `s` with its data, the
    frame above S off S + 56 … S + 80 and rd, and the globals are kept. -/
theorem elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (S r rd ptr len pb S0 S1 : Nat) (e : List UInt8)
    (H : HeapCtx env pb S0 S1 μ s)
    (hS : S0 + 432 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147483968 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : r < 18446744073709551616)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hm : e.length ≤ 16384)
    (hlen : (Blob.encodeNat e.length).length + e.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ cp ∈ chunks s, cp.used = true ∧ cp.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat e.length).length + e.length ≤ cp.addr + 32 * cp.size)
    (henc : μ.readN ptr ((Blob.encodeNat e.length).length + e.length) = Blob.encodeNat e.length ++ e) :
    (∃ s' ω' μ' qe, ∃ cs : List Chunk, FreeStepsH p (refineContractK cap env) 197 ω μ x 229 ω' μ' x (2 * e.length + 1800) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat r ∧ qe < 4294967296 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (S + 64) 8 = Num.encodeLE 8 qe ∧
      μ'.readN (S + 72) 8 = Num.encodeLE 8 e.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat e.length).length + e.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat e.length).length - e.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) → μ''.readN qe e.length = e) ∧
      (∀ a, a < 4294967296 → S ≤ a → (a < S + 56 ∨ S + 80 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 197 ω μ x (2 * e.length + 1800) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨m, hM⟩ : ∃ m, e.length = m := ⟨_, rfl⟩
  simp only [hM] at hlen hcp2 henc hm ⊢
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat m).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen hcp2 henc ⊢
  have hw1 : 1 ≤ w := by
    rw [← hW]; unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hencw : μ.readN ptr w = Blob.encodeNat m := by
    have := readN_sub μ ptr (w + m) 0 w _ henc (by omega)
    simp only [Nat.add_zero] at this
    rw [this, List.drop_zero, List.take_left' hW]
  have hdat : μ.readN (ptr + w) m = e := by
    rw [readN_sub μ ptr (w + m) w m _ henc (by omega), List.drop_left' hW]
    exact List.take_of_length_le (by omega)
  have hra : ∀ a, ptr ≤ a → a < ptr + w + m → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  -- the length
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := r1 (p := p) (P := P) (R := refineContractK cap env) x ω μ S rd
    ⟨by omega, by omega⟩ h1 (by omega) s24 (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
  obtain ⟨ω2, μ2, run2, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ 4 207 S rd ptr len a0 a1 a7
      (by decide) jte_1 bs_207 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega)) hR0 hR8 m
      (by omega) (by rw [hW]; omega) (fun a h1 h2 => by rw [hW] at h2; exact hra a h1 (by omega))
      (by rw [hW]; exact hencw)
  rw [hW] at dR0 dR8
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8, c9⟩ := r2 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2
    S rd m ⟨by omega, by omega⟩ (by rw [d1, a1]) (by rw [d5, a5]) d7 d8 (by omega) (by omega)
  have b2 : ∀ a, a < 4294967296 → (a < S - 128 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => dfr a h0 h1 h2
  have wr2 : ∀ a, μ2.writable a = μ.writable a := dwr
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr2
  have run03 := run1.trans (run2.trans run3)
  have hc6 : ω3[6] = UInt64.ofNat r := by rw [c6, d6, a6, h6]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- an empty element: no allocation
    subst hm0
    have he : e = [] := List.eq_nil_of_length_eq_zero hM
    obtain ⟨ω4, μ4, run4, f0, f1, f5, f6, fO, fO8, fO16, ffr, frd, fwr⟩ :=
      vec_u8_empty (p := p) (P := P) (R := refineContractK cap env) x ω3 μ2 S (S + 56) rd (len - w) 6 229 rd r
        ⟨by omega, by omega⟩ c0 c1 c5 hc6 c7 c8 c9 (by omega) hr (by decide) jte_2 bs_229 (by omega)
        (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (rd8'' (by omega) dR8)
        (fun a h1 h2 => by rw [drd]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => by rw [dwr]; exact hst a (by omega) (by omega))
        (fun a h1 h2 => by rw [dwr]; exact hst a (by omega) (by omega))
    have b4 : ∀ a, a < 4294967296 → (a < S - 128 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < S + 56 ∨ S + 80 ≤ a) →
        μ4.read a = μ.read a := fun a h0 h1 h2 h3 => (ffr a h0 (by omega) h3).trans (b2 a h0 h1 h2)
    have H4 : HeapCtx env pb S0 S1 μ4 s :=
      ctx_congr_data H hcpm (fun a h1 _ => b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
        (fun a => by rw [fwr, dwr])
    refine Or.inl ⟨s, ω4, μ4, 1, [], (run03.trans run4).mono (by omega), f1, f6, by decide, fO, fO8, fO16,
      ?_, ?_, H4, fun c hc _ => hc, ?_, fun c hc => by simp at hc, fun μ'' _ => by rw [he]; rfl, ?_, ?_⟩
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega) (Or.inr (by omega))), dR0, Nat.add_zero]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega) (Or.inr (by omega))), dR8, Nat.sub_zero]
    · intro c hc hu a ha
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at ha
      exact b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    · intro a h0 h1 h2 h3
      exact b4 a h0 (Or.inr h1) h3 h2
    · intro a ha
      unfold Glob at ha
      exact b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  · -- a non-empty element: `read_vec` allocates
    rcases vec_u8_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω3 μ2 s S (S + 56) rd (ptr + w) (len - w)
        m 6 229 rd r pb S0 S1 H2 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        c0 c1 c5 hc6 c7 c8 c9 (by decide) jte_2 bs_229 (by omega) hr ⟨hm0, hm⟩ (by omega) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
      ⟨qe, s', ω4, μ4, ha, run4, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H4, keep, cm, hfresh, kd, -, vfr,
        -, vgl, -⟩ | ⟨hna, ω4, μ4, run4, f7⟩
    · have hqm := chunk_in H4.wf cm rfl
      simp only at hqm
      have hbase' : s'.base = s.base := alloc_base H.wf ha
      rw [hbase'] at hqm
      refine Or.inl ⟨s', ω4, μ4, qe, [⟨qe - 32, (m + 31) / 32 + 1, true⟩], (run03.trans run4).mono (by omega),
        v1, v6', by omega, vc, vp, vl, ?_, ?_, H4, keep, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vR0]
      · rw [vR8]
      · intro c hc hu a hia
        have := (chunk_in H.wf hc hu).2.2
        have hia' := hia
        unfold InData at hia'
        rw [kd c hc hu a hia]
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨cm, rfl, hfresh⟩
      · intro μ'' hag
        rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), vdata]
        exact Memory.readN_congr (fun j hj => b2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))) |>.trans hdat
      · intro a h0 h1 h2 h3
        rw [vfr a h0 h1 h3 h2]
        exact b2 a h0 (Or.inr h1) h3
      · intro a ha'
        have hg := ha'
        unfold Glob at hg
        rw [vgl a ha']
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · exact Or.inr ((Exhausts.pre run03 (Exhausts.of_alloc run4 f7 hna)).mono (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA in
/-- **One pass of the read loop** (197 … 197, or 77 after the last element of the chunk): `elem`, then
    the push of the `Vec<u8>` `{m, qe, m}` as element k < cap of the buffer q (S + 40, inside the
    allocated chunk `cb`; cap at S + 32, len k at S + 48), with r ≥ 1 left in the chunk (ω₆). The
    data of every allocated chunk of `s` is kept off the new element's 24 octets. -/
theorem pass {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (S q c k r rd ptr len pb S0 S1 : Nat) (cb : Chunk) (e : List UInt8)
    (H : HeapCtx env pb S0 S1 μ s)
    (hS : S0 + 432 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147483968 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 1 ≤ r ∧ r < 4294967296)
    (hk : k < c ∧ c ≤ 682)
    (hcb : cb ∈ chunks s) (hcbu : cb.used = true) (hq1 : cb.addr + 32 ≤ q)
    (hq2 : q + 24 * c ≤ cb.addr + 32 * cb.size)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 c) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 k)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hm : e.length ≤ 16384)
    (hlen : (Blob.encodeNat e.length).length + e.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ cp ∈ chunks s, cp.used = true ∧ cp.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat e.length).length + e.length ≤ cp.addr + 32 * cp.size)
    (henc : μ.readN ptr ((Blob.encodeNat e.length).length + e.length) = Blob.encodeNat e.length ++ e) :
    (∃ s' ω' μ' j qe, ∃ cs : List Chunk,
      FreeStepsH p (refineContractK cap env) 197 ω μ x j ω' μ' x (2 * e.length + 1900) ∧
      (2 ≤ r → j = 197) ∧ (r = 1 → j = 77 ∧ ω'[7] = UInt64.ofNat (k + 1)) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
      μ'.readN (q + 24 * k) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (q + 24 * k + 8) 8 = Num.encodeLE 8 qe ∧
      μ'.readN (q + 24 * k + 16) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (k + 1) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat e.length).length + e.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat e.length).length - e.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) → μ''.readN qe e.length = e) ∧
      (∀ a, a < 4294967296 → S ≤ a → (a < S + 48 ∨ S + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 197 ω μ x (2 * e.length + 1900) := by
  have hS1 := H.hS1
  obtain ⟨hcbb, hcbT, hcbT'⟩ := chunk_in H.wf hcb hcbu
  have hbT := H.hbT
  rcases elem (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S r rd ptr len pb S0 S1 e H hS hSa h1 h6
      (by omega) s24 hrd hR0 hR8 hm hlen hpay henc with
    ⟨s', ω4, μ4, qe, cs, run4, e1, e6, hqe, s56, s64, s72, R0, R8, H4, keep, kd, hcs, hrep, fr4, gl4⟩ | ex
  · have hcb' := keep cb hcb hcbu
    have hst4 := H4.st
    have u32 : μ4.readN (S + 32) 8 = Num.encodeLE 8 c := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s32
    have u40 : μ4.readN (S + 40) 8 = Num.encodeLE 8 q := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s40
    have u48 : μ4.readN (S + 48) 8 = Num.encodeLE 8 k := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s48
    obtain ⟨j, ω5, μ5, run5, hj1, hj2, f1, f6, fe0, fe1, fe2, f48, ffr, frd, fwr⟩ :=
      r3 (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 S q c k r e.length qe e.length
        ⟨by omega, by omega⟩ e1 e6 hr ⟨hk.1, by omega⟩ (by omega) (by omega) hqe (by omega) u32 u48 u40 s56 s64 s72
        (by omega) (fun a h1 h2 => hst4 a (by omega) (by omega))
        (fun a h1 h2 => heap_writable H4 hcb' hcbu ⟨by omega, by omega⟩)
    have low5 : ∀ a, a < 2147483648 → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) → μ5.read a = μ4.read a :=
      fun a h0 h1 => ffr a (by omega) h1 (Or.inl (by omega)) (Or.inl (by omega))
    refine Or.inl ⟨s', ω5, μ5, j, qe, cs, (run4.trans run5).mono (by omega), hj1, hj2, f1, f6, fe0, fe1, fe2, f48,
      ?_, ?_, ctx_congr_data H4 hcb' (fun a h1 h2 => low5 a h1 (by omega)) fwr, keep, ?_, hcs, ?_, ?_, ?_⟩
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)))]
      exact R0
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)))]
      exact R8
    · intro d hd hu a hia hout
      have := (chunk_in H.wf hd hu).2.2
      have hia' := hia
      unfold InData at hia'
      rw [low5 a (by omega) hout]
      exact kd d hd hu a hia
    · intro μ'' hag
      apply hrep
      intro d hdc a hia
      obtain ⟨hdm, hdu, hdf⟩ := hcs d hdc
      have hdis := data_disj H4.wf hdm hcb' (fun e' => hdf cb hcb hcbu e'.symm) hia
      have := (chunk_in H4.wf hdm hdu).2.2
      have hbase := H4.hbT
      have hia' := hia
      unfold InData at hia'
      rw [hag d hdc a hia, low5 a (by omega) (by omega)]
    · intro a h0 h1 h2 h3
      rw [ffr a h0 (Or.inr (by omega)) (by omega) (by omega)]
      exact fr4 a h0 h1 (by omega) h3
    · intro a ha'
      have hg := ha'
      unfold Glob at hg
      have hb04 := H4.hb0
      have hcbb' := (chunk_in H4.wf hcb' hcbu).1
      rw [low5 a (by omega) (Or.inl (by omega))]
      exact gl4 a ha'
  · exact Or.inr (ex.mono (by omega))

/-- The encodings of the elements: each ℰ(|e|) ++ e. -/
def encs (es : List (List UInt8)) : List (List UInt8) := es.map (fun e => Blob.encodeNat e.length ++ e)

theorem encs_length (es : List (List UInt8)) : (encs es).length = es.length := by simp [encs]

theorem encs_get (es : List (List UInt8)) (k : Nat) (hk : k < (encs es).length) :
    (encs es)[k] = Blob.encodeNat (es[k]'(by rw [← encs_length es]; exact hk)).length ++
      es[k]'(by rw [← encs_length es]; exact hk) := by
  simp [encs]

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **The read loop** (197 … 77): with k elements of the n = |es| pushed and i = n − k left (ω₆), the
    reader rd at the k-th encoding of the payload (the elements' encodings ℰ(|e|) ++ e, laid end to end
    at ptr0 inside the allocated chunk `cp`), each pass reads an element (`pass`) until the last leaves
    for 77. Either every remaining element j is pushed at q + 24j as `{|es[j]|, qs j, |es[j]|}` with
    qs j holding es[j] in fresh chunks `cs`, or an allocation fails. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) {hb : Nat}
    (S q rd ptr0 len0 pb S0 S1 : Nat) (cb cp : Chunk) (es : List (List UInt8))
    (hS : S0 + 432 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147483968 ≤ S ∧ S % 8 = 0)
    (hn : 1 ≤ es.length ∧ es.length ≤ 682) (hes : ∀ e ∈ es, e.length ≤ 16384)
    (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1) (hcbcp : cb ≠ cp)
    (hq1 : cb.addr + 32 ≤ q) (hq2 : q + 24 * es.length ≤ cb.addr + 32 * cb.size)
    (hp1 : cp.addr + 32 ≤ ptr0) (hp2 : ptr0 + (encs es).flatten.length ≤ cp.addr + 32 * cp.size)
    (hlen : (encs es).flatten.length ≤ len0 ∧ len0 < 4294967296) :
    ∀ i k (s : State) (ω : Regs) (μ : Memory), k + i = es.length → 1 ≤ i →
      HeapCtx env pb S0 S1 μ s → cb ∈ chunks s → cb.used = true → cp ∈ chunks s → cp.used = true →
      ω[1] = UInt64.ofNat S → ω[6] = UInt64.ofNat i →
      μ.readN (S + 32) 8 = Num.encodeLE 8 es.length → μ.readN (S + 40) 8 = Num.encodeLE 8 q →
      μ.readN (S + 48) 8 = Num.encodeLE 8 k → μ.readN (S + 24) 8 = Num.encodeLE 8 rd →
      μ.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) k) →
      μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) k) →
      μ.readN ptr0 (encs es).flatten.length = (encs es).flatten →
      (∃ s' ω' μ', ∃ cs : List Chunk, ∃ qs : Nat → Nat,
        FreeStepsH p (refineContractK cap env) 197 ω μ x 77 ω' μ' x (34668 * i) ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat es.length ∧
        (∀ j (hj : j < es.length), k ≤ j →
          μ'.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧
          μ'.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
          μ'.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length) ∧
        μ'.readN (S + 48) 8 = Num.encodeLE 8 es.length ∧
        μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + (encs es).flatten.length) ∧
        μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - (encs es).flatten.length) ∧
        HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
        (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < q + 24 * k ∨ q + 24 * es.length ≤ a) →
          μ'.read a = μ.read a) ∧
        (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          ∀ j (hj : j < es.length), k ≤ j → μ''.readN (qs j) es[j].length = es[j]) ∧
        (∀ a, a < 4294967296 → S ≤ a → (a < S + 48 ∨ S + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
          μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a)) ∨
      Exhausts env cap pb p P 197 ω μ x (34668 * i) := by
  intro i
  induction i with
  | zero => intro k s ω μ _ h; exact absurd h (by decide)
  | succ i ih =>
  intro k s ω μ hki _ H hcb hcbu hcp hcpu h1 h6 s32 s40 s48 s24 R0 R8 pay
  have hk : k < es.length := by omega
  have hkE : k < (encs es).length := by rw [encs_length]; exact hk
  have hEk := encs_get es k hkE
  have hoff := off_lt (encs es) k hkE
  rw [hEk] at hoff
  simp only [List.length_append] at hoff
  have hm := hes es[k] (List.getElem_mem hk)
  have henc : μ.readN (ptr0 + off (encs es) k)
      ((Blob.encodeNat es[k].length).length + es[k].length) = Blob.encodeNat es[k].length ++ es[k] := by
    rw [readN_sub μ ptr0 _ _ _ _ pay (by omega)]
    have := flatten_at (encs es) k hkE
    rw [hEk] at this
    simpa using this
  have hS1 := H.hS1
  rcases pass (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S q es.length k (i + 1) rd
      (ptr0 + off (encs es) k) (len0 - off (encs es) k) pb S0 S1 cb es[k] H hS hSa h1 h6 ⟨by omega, by omega⟩
      ⟨hk, hn.2⟩ hcb hcbu hq1 hq2 s32 s40 s48 s24 hrd R0 R8 hm ⟨by omega, by omega⟩
      ⟨cp, hcp, hcpu, by omega, by omega⟩ henc with
    ⟨s1, ω1, μ1, j, qe, cs1, run1, hj1, hj2, f1, f6, fe0, fe1, fe2, f48, fR0, fR8, H1, keep1, kd1, hcs1, hrep1,
      ffr1, fgl1⟩ | ex
  rotate_left
  · exact Or.inr (ex.mono (by omega))
  have hcb1 := keep1 cb hcb hcbu
  have hcp1 := keep1 cp hcp hcpu
  obtain ⟨hcbb, hcbT, -⟩ := chunk_in H.wf hcb hcbu
  have hb0 := H.hb0
  -- the payload is kept: it lies in cp, the push in cb
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + (encs es).flatten.length → μ1.read a = μ.read a := fun a h1 h2 =>
    kd1 cp hcp hcpu a ⟨by omega, by omega⟩ (by
      have := data_disj H.wf hcp hcb (Ne.symm hcbcp) (a := a) ⟨by omega, by omega⟩
      omega)
  have hoff1 : off (encs es) (k + 1) = off (encs es) k + ((Blob.encodeNat es[k].length).length + es[k].length) := by
    rw [off_succ (encs es) k hkE, hEk, List.length_append]
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · -- the last element: on to 77
    subst hi0
    obtain ⟨rfl, f7⟩ := hj2 rfl
    have hkn : k + 1 = es.length := by omega
    have hoffn : off (encs es) (k + 1) = (encs es).flatten.length := by
      unfold off; rw [hkn, ← encs_length es, List.take_length]
    refine Or.inl ⟨s1, ω1, μ1, cs1, fun _ => qe, run1.mono (by omega), f1, by rw [f7, hkn], ?_, by rw [f48, hkn],
      ?_, ?_, H1, keep1, ?_, hcs1, ?_, ffr1, fgl1⟩
    · intro j' hj' hkj
      obtain rfl : j' = k := by omega
      exact ⟨fe0, fe1, fe2⟩
    · rw [fR0, ← hoffn, hoff1]; congr 1; omega
    · rw [fR8, ← hoffn, hoff1]; congr 1; omega
    · intro c hc hu a hia hout
      exact kd1 c hc hu a hia (by omega)
    · intro μ'' hag j' hj' hkj
      obtain rfl : j' = k := by omega
      exact hrep1 μ'' hag
  · -- more to read: the next pass
    have hj197 := hj1 (by omega)
    subst hj197
    have u32 : μ1.readN (S + 32) 8 = Num.encodeLE 8 es.length := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s32
    have u40 : μ1.readN (S + 40) 8 = Num.encodeLE 8 q := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s40
    have u24 : μ1.readN (S + 24) 8 = Num.encodeLE 8 rd := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s24
    rcases ih (k + 1) s1 ω1 μ1 (by omega) hi0 H1 hcb1 hcbu hcp1 hcpu f1 (by rw [f6]; congr 1) u32 u40 f48 u24
        (by rw [fR0, hoff1]; congr 1; omega) (by rw [fR8, hoff1]; congr 1; omega)
        (by rw [Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))]; exact pay) with
      ⟨s2, ω2, μ2, cs2, qs2, run2, g1, g7, gel, g48, gR0, gR8, H2, keep2, kd2, hcs2, hrep2, gfr, ggl⟩ | ex
    · have hcb2 := keep2 cb hcb1 hcbu
      refine Or.inl ⟨s2, ω2, μ2, cs1 ++ cs2, fun j' => if j' = k then qe else qs2 j',
        (run1.trans run2).mono (by omega), g1, g7, ?_, g48, gR0, gR8, H2,
        fun c hc hu => keep2 c (keep1 c hc hu) hu, ?_, ?_, ?_, ?_, ?_⟩
      · intro j' hj' hkj
        by_cases hjk : j' = k
        · subst hjk
          simp only [ite_true]
          have kk : ∀ t, t < 24 → μ2.read (q + 24 * j' + t) = μ1.read (q + 24 * j' + t) := fun t ht =>
            kd2 cb hcb1 hcbu _ ⟨by omega, by omega⟩ (Or.inl (by omega))
          have k8 : μ2.readN (q + 24 * j' + 8) 8 = μ1.readN (q + 24 * j' + 8) 8 :=
            Memory.readN_congr (fun t ht => by
              have := kk (8 + t) (by omega); rwa [show q + 24 * j' + (8 + t) = q + 24 * j' + 8 + t by omega] at this)
          have k16 : μ2.readN (q + 24 * j' + 16) 8 = μ1.readN (q + 24 * j' + 16) 8 :=
            Memory.readN_congr (fun t ht => by
              have := kk (16 + t) (by omega); rwa [show q + 24 * j' + (16 + t) = q + 24 * j' + 16 + t by omega] at this)
          refine ⟨?_, ?_, ?_⟩
          · rw [Memory.readN_congr (fun t ht => kk t (by omega))]; exact fe0
          · rw [k8]; exact fe1
          · rw [k16]; exact fe2
        · simp only [hjk, ite_false]
          exact gel j' hj' (by omega)
      · intro c hc hu a hia hout
        have hc1 := keep1 c hc hu
        by_cases hin : q + 24 * k ≤ a ∧ a < q + 24 * k + 24
        · rcases Classical.em (c = cb) with hcbc | hne
          · subst hcbc
            omega
          · have := data_disj H.wf hc hcb hne hia
            omega
        · rw [kd2 c hc1 hu a hia (by omega)]
          exact kd1 c hc hu a hia (by omega)
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨hcm, hcu, hcf⟩ := hcs1 c hc
          exact ⟨keep2 c hcm hcu, hcu, hcf⟩
        · obtain ⟨hcm, hcu, hcf⟩ := hcs2 c hc
          exact ⟨hcm, hcu, fun d hd hu => hcf d (keep1 d hd hu) hu⟩
      · intro μ'' hag j' hj' hkj
        by_cases hjk : j' = k
        · subst hjk
          simp only [ite_true]
          apply hrep1
          intro c hc a hia
          obtain ⟨hcm, hcu, -⟩ := hcs1 c hc
          rw [hag c (List.mem_append_left _ hc) a hia]
          have := (chunk_in H1.wf hcm hcu).2.2
          have hne : c ≠ cb := fun e => by
            obtain ⟨-, -, hf⟩ := hcs1 c hc
            exact hf cb hcb hcbu e.symm
          have hdis := data_disj H1.wf hcm hcb1 hne hia
          have hia' := hia
          unfold InData at hia'
          exact kd2 c hcm hcu a hia (by omega)
        · simp only [hjk, ite_false]
          exact hrep2 μ'' (fun c hc a hia => hag c (List.mem_append_right _ hc) a hia) j' hj' (by omega)
      · intro a h0 h1 h2 h3
        rw [gfr a h0 h1 h2 h3]
        exact ffr1 a h0 h1 h2 h3
      · intro a ha
        rw [ggl a ha]; exact fgl1 a ha
    · exact Or.inr ((Exhausts.pre run1 ex).mono (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop in
/-- **Reading 1 … 682 byte strings into a fresh `Vec<Vec<u8>>`, the payload in the heap** (8): with
    ω₇ = O, ω₈ = rd, ω₉ = n = |es|, every element at most 16384 octets, the allocator's context
    `HeapCtx` (under `refineContractK cap`, cap ≥ 2²⁷) and the payload (each element's ℰ(|e|) ++ e, end
    to end) inside an allocated chunk's data, the reader returns to t with the `Vec` `{cap n, ptr q,
    len n}` at O, element j at q + 24j as the `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` with qs j holding
    es[j]; the buffer and the elements' blocks are fresh allocated chunks (`cs`), and the context,
    every allocated chunk of `s` with its data, memory below 196608, the globals and the stack's
    access are kept. Or an allocation fails. -/
theorem vec_vec_u8_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len ret t v5 v6 pb S0 S1 : Nat) (es : List (List UInt8))
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (encs es).flatten.length ≤ c.addr + 32 * c.size)
    (hS : S0 + 560 ≤ sp ∧ sp ≤ S1) (hsp : 2147484096 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat es.length)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ es.length ∧ es.length ≤ 682) (hes : ∀ e ∈ es, e.length ≤ 16384)
    (hlen : (encs es).flatten.length ≤ len ∧ len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hpd : μ.readN ptr (encs es).flatten.length = (encs es).flatten) :
    (∃ s' ω' μ' q, ∃ cs : List Chunk, ∃ qs : Nat → Nat,
      FreeStepsH p (refineContractK cap env) 8 ω μ x t ω' μ' x (34668 * es.length + 800) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 es.length ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (encs es).flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (encs es).flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
        ∀ j (hj : j < es.length),
          μ''.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
          μ''.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (qs j) es[j].length = es[j]) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 8 ω μ x (34668 * es.length + 800) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  rw [hN] at h9 hn
  have hmin : min n 682 = n := by omega
  -- the frame and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m104, m112, m128, m120, m80, fr1,
      rd1, wr1⟩ := q1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 (by omega) hv5 hv6 (by omega) (by omega) ⟨hn.1, by omega⟩
    (fun a h1 h2 => hst a (by omega) (by omega))
  rw [hmin] at a6 a10 m128
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    VecPairs.g1e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 168) (sp - 128 + 80) n 8 24 2 n n
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨hn.1, by omega⟩ (by decide) (by decide)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 168 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 168) (24 * n) 8 pb S0 S1 H2 b1
      b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (24 * n + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 168 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 168) (sp - 128 + 80) (24 * n) q 2 120 n n
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_0 bs_120
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  -- the frame S = sp − 128 in μ5
  have hS5 : ∀ a, sp - 128 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d1, d6, d32, d40, d8, d0, fr6, rd6, wr6⟩ :=
    q4 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 128) q n n ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega)
      (by rw [show sp - 128 + 80 = sp - 128 + 80 from rfl]; exact cres)
      (by rw [show sp - 128 + 88 = sp - 128 + 80 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m128)
      (by rw [show sp - 128 + 8 = sp - 120 by omega,
            Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m120)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS6 : ∀ a, sp - 128 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → (a < sp - 128 ∨ sp - 112 ≤ a) →
      (a < sp - 96 ∨ sp - 80 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (fr6 a h2 (by omega) (by omega)).trans (hS5 a h1 h2 h3)
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, ptr ≤ a → a < ptr + (encs es).flatten.length → μ6.read a = μ.read a := fun a h1 h2 =>
    (h63 a (by omega)).trans ((kd cp hcpm hcpu a ⟨by omega, by omega⟩).trans
      (hlow a (by omega) (Or.inl (by omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H3 hnew (fun a h1 _ => h63 a h1) wr36
  -- the loop
  have hoff0 : off (encs es) 0 = 0 := by simp [off]
  rcases loop (p := p) (P := P) (hb := hb) env cap hcap1 hcap x (sp - 128) q rd ptr len pb S0 S1
      ⟨q - 32, (24 * n + 31) / 32 + 1, true⟩ cp es ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by rw [hN]; exact hn)
      hes ⟨by omega, by omega⟩ (Ne.symm hcpne) (by simp only; omega) (by simp only; rw [hN]; omega) hcp1 hcp2 hlen
      n 0 s' ω6 μ6 (by omega) hn.1 H6 hnew rfl hcp' hcpu d1 d6
      (by rw [hN]; exact d32) d40
      (by rw [show sp - 128 + 48 = sp - 80 by omega,
            Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m80)
      (by rw [show sp - 128 + 24 = sp - 104 by omega,
            Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m104)
      (by rw [hoff0, Nat.add_zero, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [hoff0, Nat.sub_zero, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by rw [Memory.readN_congr (fun j hj => hpay6 _ (by omega) (by omega))]; exact hpd) with
    ⟨s2, ω7, μ7, cs, qs, run7, g1, g7, gel, g48, gR0, gR8, H7, keep7, kd7, hcs7, hrep7, gfr, ggl⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) ex).mono
      (by omega))
  rw [hN] at g7 g48
  have h76 : ∀ a, sp - 128 ≤ a → a < sp → (a < sp - 80 ∨ sp - 24 ≤ a) → μ7.read a = μ6.read a := fun a h1 h2 h3 =>
    gfr a (by omega) h1 (by omega) (Or.inl (by omega))
  obtain ⟨ω8, run8, g81⟩ :=
    x1 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (sp - 128) n ⟨by omega, by omega⟩ g1 (by omega)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d8)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d0)
      (fun a h1 h2 => Memory.readable_of_writable (H7.st a (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, z0, z1, z5, z6, zO, zO8, zO16, fr9, rd9, wr9⟩ :=
    x2 (p := p) (P := P) (R := refineContractK cap env) x ω8 μ7 (sp - 128) O n q n ret t v5 v6 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) g81 (by omega) (by omega) (by omega) hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d32)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d40)
      g48
      (by rw [show sp - 128 + 16 = sp - 112 by omega,
            Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega)).trans
              (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m112)
      (by rw [show sp - 128 + 120 = sp - 8 by omega,
            Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega)).trans
              (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m8)
      (by rw [show sp - 128 + 112 = sp - 16 by omega,
            Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega)).trans
              (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m16)
      (by rw [show sp - 128 + 104 = sp - 24 by omega,
            Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega) (by omega)).trans
              (hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => H7.st a (by omega) (by omega)) (fun a h1 h2 => H7.st a (by omega) (by omega))
  have hlow9 : ∀ a, a < 2147483648 → μ9.read a = μ7.read a := fun a h1 => fr9 a (by omega) (Or.inl (by omega))
    (Or.inl (by omega))
  have run19 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans run9)))))))
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run19
  have hst7 := H7.st
  have ht3 := H3.wf.2.2.2.1
  unfold TilesOk at ht3
  refine Or.inl ⟨s2, ω9, μ9, q, ⟨q - 32, (24 * n + 31) / 32 + 1, true⟩ :: cs, qs, run19.mono (by omega), z0,
    by rw [z1]; congr 1; omega, z5, z6, by rw [hN]; exact zO, zO8, by rw [hN]; exact zO16, ?_, ?_,
    ctx_congr_data H7 (keep7 cp hcp' hcpu) (fun a h1 _ => hlow9 a h1) wr9,
    fun c hc hu => keep7 c (keep c hc hu) hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => fr9 _ (by omega) (Or.inr (by omega)) (by omega))]; exact gR0
  · rw [Memory.readN_congr (fun j hj => fr9 _ (by omega) (Or.inr (by omega)) (by omega))]; exact gR8
  · intro c hc hu a hia
    have hc' := keep c hc hu
    have hne : c ≠ ⟨q - 32, (24 * n + 31) / 32 + 1, true⟩ := hfresh c hc hu
    have hdis := data_disj H3.wf hc' hnew hne hia
    simp only at hdis
    have := (chunk_in H.wf hc hu).2.2
    have hia' := hia
    unfold InData at hia'
    rw [hlow9 a (by omega), kd7 c hc' hu a hia (by omega), h63 a (by omega), kd c hc hu a hia]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨keep7 _ hnew rfl, rfl, hfresh⟩
    · obtain ⟨hcm, hcu, hcf⟩ := hcs7 c hc
      exact ⟨hcm, hcu, fun d hd hu => hcf d (keep d hd hu) hu⟩
  · intro μ'' hag j hj
    have hj' : j < es.length := by omega
    have hcbs : ∀ a, InData (⟨q - 32, (24 * n + 31) / 32 + 1, true⟩ : Chunk) a → μ''.read a = μ7.read a :=
      fun a hia => by
        have hia' := hia
        unfold InData at hia'
        simp only at hia'
        rw [hag _ List.mem_cons_self a hia, hlow9 a (by omega)]
    obtain ⟨w0, w8, w16⟩ := gel j hj' (Nat.zero_le _)
    refine ⟨?_, ?_, ?_, hrep7 μ'' (fun c hc a hia => (hag c (List.mem_cons_of_mem _ hc) a hia).trans
      (by
        obtain ⟨hcm, hcu, -⟩ := hcs7 c hc
        have := (chunk_in H7.wf hcm hcu).2.2
        have hb7 := H7.hbT
        have hia' := hia
        unfold InData at hia'
        exact hlow9 a (by omega))) j hj' (Nat.zero_le _)⟩
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w0
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w8
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w16
  · intro a h0 h1 h2 h3
    rw [fr9 a h0 (Or.inr (by omega)) h3, gfr a h0 (by omega) (Or.inr (by omega)) h2]
    exact hhigh a h0 h1
  · intro a ha'
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    have hb3 := H3.hb0
    rw [hlow9 a (by omega), ggl a ha', h63 a (by omega),
      hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht3.mem_lt c hc).1; omega)) a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.VecVecU8
