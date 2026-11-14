import Services.Bootstrap.Refine.DecodeTail
import Services.Bootstrap.Decode.LoopAPass
import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.Decode.AllocOk

/-!
# `Vec<Instruction>::decode` (482 … its return), one batch

`Vec<Instruction>::decode` (482), called with the output at ω₇, the reader at ω₈ and the length n at ω₉,
opens a 552-octet frame S = ω₁ − 552, starts with an empty `Vec` `{0, 8, 0}` at S + 40 and decodes in batches
of min(n, 70) elements: it reserves each batch exactly (`finish_grow`, 32989; 232-octet elements at alignment
8), decodes it (the element loop 680 … 562, `Decode.LoopA.loopAF`), and after the last batch writes the `Vec`
`{cap, ptr, len}` to the output and returns. Here: one batch (1 ≤ n ≤ 70). GP v0.8.0 Appendix B.4 (Ψ_R running
bootstrap's code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVec

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 482 … 530 (n ≠ 0): the frame S = ω₁ − 552 (return address, ω₅, ω₆ at S + 544, S + 536, S + 528), the
    reader at S + 24, the output at S, the empty `Vec` `{0, 8, 0}` at S + 40; on to 531 with ω₅ = n, ω₇ = 0
    (elements so far), ω₉ = 8, ω₁₂ = 70. Memory changes only in [S, S + 64) and [S + 528, S + 552). -/
theorem v1a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : n ≠ 0)
    (hn64 : n < 18446744073709551616) (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hw : ∀ a, S ≤ a → a < S + 552 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 482 ω μ x 531 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 70 ∧
      μ'.readN S 8 = Num.encodeLE 8 out ∧ μ'.readN (S + 24) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 8 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 544) 8 = Num.encodeLE 8 r0 ∧
      μ'.readN (S + 536) 8 = Num.encodeLE 8 v5 ∧ μ'.readN (S + 528) 8 = Num.encodeLE 8 v6 ∧
      (∀ a, a < 4294967296 → (a < S ∨ (S + 64 ≤ a ∧ a < S + 528) ∨ S + 552 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have hn' : ¬ n = 0 := hn
  have hr : ∀ a, S ≤ a → a < S + 552 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS0, hS1, hS8, hn', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hn64,
      Nat.mod_eq_of_lt hout, Nat.mod_eq_of_lt hrd, Nat.mod_eq_of_lt hr0, Nat.mod_eq_of_lt hv5,
      Nat.mod_eq_of_lt hv6]
    all_goals try (congr 1; omega)
    post_simp

/-- 531 … 602, the first batch (the `Vec` empty, 1 ≤ n ≤ 70): the batch n (= min(n, 70)) at S + 8 and S + 16, 70
    at S + 32, and `finish_grow` (32989) called for the capacity n (ω₁₀; old capacity ω₈ = 0, alignment 8,
    element size 232, result at S + 296; return address 14 → 607) with ω₅ = ω₆ = n. Memory changes only at
    S + 8 … S + 24 and S + 32 … S + 40. -/
theorem v1b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S n : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : 1 ≤ n ∧ n ≤ 70)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h7 : ω[7] = UInt64.ofNat 0)
    (h9 : ω[9] = UInt64.ofNat 8) (h12 : ω[12] = UInt64.ofNat 70)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 0)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 531 ω μ x 32989 ω' μ' x 30 ∧ ω'[0] = UInt64.ofNat 14 ∧ ω'[1] = UInt64.ofNat S ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (S + 296) ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 232 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 70 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ (S + 24 ≤ a ∧ a < S + 32) ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r40 := rd8 (by decide) s40
  have hr : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hmin : min n 70 = n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, h9, h12, hS0, hS1, hS8, hn, hw, hr, r40, hmin, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h9]
    all_goals try (congr 1; omega)
    post_simp

/-- 32989 … 33084: `finish_grow` with no old buffer (ω₈ = 0) for n ≥ 1 elements of E ≤ 256 octets at alignment
    al (`Decode.VecPairs.g1e` for larger elements): its 40-octet frame at F = ω₁ − 40, and `alloc` (40494) for
    E·n octets (return address 1526). -/
theorem g1x {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n al E r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat al) (h12 : ω[12] = UInt64.ofNat E)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ n < 4294967296) (hal : 1 ≤ al ∧ al ≤ 32)
    (hE : 1 ≤ E ∧ E ≤ 256)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat (E * n) ∧ ω'[8] = UInt64.ofNat al ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (E * n) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : E * n < 1099511627776 := by
    have : E * n ≤ 256 * n := Nat.mul_le_mul_right n hE.2
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


/-- 607 … 635, `finish_grow` returned `Ok` (0 at S + 296) with the block q (S + 304): the `Vec`'s capacity n
    (ω₆) and buffer q at S + 40, S + 48, q at S + 32, and into the element loop (680) with ω₅ = n (from S + 16).
    Memory changes only at S + 32 … S + 56. -/
theorem v2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S n q : Nat)
    (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0) (hn : n < 18446744073709551616)
    (hq : q < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat n)
    (s296 : μ.readN (S + 296) 8 = Num.encodeLE 8 0) (s304 : μ.readN (S + 304) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 70)
    (hr : ∀ a, S + 296 ≤ a → a < S + 312 → μ.readable a = true)
    (hw : ∀ a, S ≤ a → a < S + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 607 ω μ x 680 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r296 := rd8 (by decide) s296
  have r304 := rd8 hq s304
  have r16 := rd8 hn s16
  have r32 := rd8 (by decide) s32
  have hr2 : ∀ a, S ≤ a → a < S + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS0, hS1, hS8, hr, hr2, hw, r296, r304, r16, r32, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt hq]
    all_goals try (congr 1; omega)
    post_simp

/-- 562 … 901, the last batch done (n − batch = 0 from S + 8, S + 16): the `Vec`'s buffer and length copied to
    S + 296, S + 304, and on to 842 with the output (from S) in ω₇ and the capacity (not the error word) in ω₁₁.
    Memory changes only at S + 296 … S + 312. -/
theorem v3a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out n cap q len : Nat) (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0)
    (hout : out < 18446744073709551616) (hn : n < 18446744073709551616) (hcap : cap < 18446744073709551615)
    (hq : q < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S)
    (s0 : μ.readN S 8 = Num.encodeLE 8 out) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 len)
    (hw : ∀ a, S ≤ a → a < S + 552 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 562 ω μ x 842 ω' μ' x 30 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat out ∧
      ω'[11] = UInt64.ofNat cap ∧
      μ'.readN (S + 296) 8 = Num.encodeLE 8 q ∧ μ'.readN (S + 304) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 296 ∨ S + 312 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have r0 := rd8 hout s0
  have r8 := rd8 hn s8
  have r16 := rd8 hn s16
  have r40 := rd8 (by omega) s40
  have r48 := rd8 hq s48
  have r56 := rd8 hlen s56
  have hce : ¬ cap = 18446744073709551615 := by omega
  have hr : ∀ a, S ≤ a → a < S + 552 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS0, hS1, hS8, hce, hr, hw, r0, r8, r16, r40, r48, r56, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hout,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt (show cap < 18446744073709551616 by omega)]
    all_goals try (congr 1; omega)
    post_simp

/-- 842 … 875: the `Vec` `{cap, q, len}` written to the output (ω₇), and the return (922 → 20420) with
    ω₁ = S + 552 and ω₅, ω₆ restored from S + 536, S + 528. Memory changes only at out … out + 24. -/
theorem v3b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out cap q len v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 552 ≤ 4294967296 ∧ S % 8 = 0)
    (hout : 65536 ≤ out ∧ out + 24 ≤ 4294967296 ∧ (out + 24 ≤ S + 296 ∨ S + 552 ≤ out))
    (hcap : cap < 18446744073709551616) (hq : q < 18446744073709551616)
    (hlen : len < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat out) (h11 : ω[11] = UInt64.ofNat cap)
    (s296 : μ.readN (S + 296) 8 = Num.encodeLE 8 q) (s304 : μ.readN (S + 304) 8 = Num.encodeLE 8 len)
    (s544 : μ.readN (S + 544) 8 = Num.encodeLE 8 922) (s536 : μ.readN (S + 536) 8 = Num.encodeLE 8 v5)
    (s528 : μ.readN (S + 528) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, S + 296 ≤ a → a < S + 552 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 842 ω μ x 20420 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat (S + 552) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN out 8 = Num.encodeLE 8 cap ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  obtain ⟨ho0, ho1, ho2⟩ := hout
  have r296 := rd8 hq s296
  have r304 := rd8 hlen s304
  have r544 := rd8 (by decide) s544
  have r536 := rd8 hv5 s536
  have r528 := rd8 hv6 s528
  have hr2 : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, h11, hS0, hS1, hS8, ho0, ho1, ho2, hr, hr2, hwo, r296, r304, r544, r536, r528,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv5,
      Nat.mod_eq_of_lt hv6, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hcap]
    all_goals try (congr 1; omega)
    post_simp

end Services.Bootstrap.Refine.DecodeVec
