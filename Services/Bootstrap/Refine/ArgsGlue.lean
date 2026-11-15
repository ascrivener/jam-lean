import Services.Bootstrap.Decode.VecEmpty
import Services.Bootstrap.Memzero
import PVM.Logic.Go

/-!
# Refine's argument decode: the glue around the payload's `Vec` and the hash

Refine's frame M = 4278058376 holds an inner frame at sp = M − 112. After the decodes of c, i, s and
|y| = n (each by `decodeU32`), at 35130:

* `glue_pre_vec` (35130 … 35149): the decoder's error flag ω₇ is tested (≠ 0 traps at 35292), n is
  zero-extended from ω₈ into ω₉, and `read_vec` (3473) is called with the `Vec` at sp + 56 (ω₇), the
  reader at sp + 40 (ω₈), n (ω₉) and the return address 1642 (→ 35155, `jte_820`): the registers
  `vec_u8_args` / `vec_u8_args_big` take.
* `glue_post_vec` (35155 … 35196): the `Vec`'s capacity word at sp + 56 is not the error niche
  2^64 − 1 (which traps at 35292); its pointer and length go to sp + 8 and sp, the 32 octets at
  sp + 56 are zeroed, and `read_big` (58434) is called for the 32-octet hash with the reader at
  sp + 40, the buffer at sp + 56 and the return address 1644 (→ 35202, `jte_821`). The capacity stays
  in ω₆.
* `glue_tail` (35202 … 35273): `read_big` succeeded (ω₇ = 0, else 35275); the result struct at
  O = ω₅ (M + 168) gets cap, q, len at O, O + 8, O + 16, the hash at O + 24 … O + 56, i (`u32`, from
  sp + 24) at O + 56, s (`u32`, from sp + 16) at O + 60 and c (`u16`, from sp + 32) at O + 64; then
  ω₀, ω₅, ω₆ are restored from sp + 104, sp + 96, sp + 88, sp becomes sp + 112 and the code jumps
  through the jump table (152 → `jte_75` → 4680 at the call site).

None makes a host call, so each holds under any host relation.
-/

namespace Services.Bootstrap.Refine.ArgsGlue

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.VecEmpty

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- **35130 → 3473**: with the decoder's error flag ω₇ = 0 and n (< 2^32) in ω₈, the call of
    `read_vec` with ω₀ = 1642 (→ 35155), ω₇ = sp + 56 (the `Vec`), ω₈ = sp + 40 (the reader),
    ω₉ = n. Memory is unchanged; ω₁ … ω₆, ω₁₀ … ω₁₂ are kept. -/
theorem glue_pre_vec {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp n : Nat) (hsp : sp + 56 < 4294967296) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 35130 ω μ x 3473 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 1642 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 56) ∧
      ω'[8] = UInt64.ofNat (sp + 40) ∧ ω'[9] = UInt64.ofNat n ∧
      ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hsp, hn]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try rfl

macro "ag_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- **35155 → 58434**, the success path: the `Vec` `{cap, q, len}` that `read_vec` left at sp + 56
    (cap ≠ 2^64 − 1, the error niche): q to sp + 8, len to sp, the 32 octets at sp + 56 zeroed, and the
    call of `read_big` with ω₀ = 1644 (→ 35202), ω₇ = sp + 40 (the reader), ω₈ = sp + 56 (the hash
    buffer), ω₉ = 32; cap stays in ω₆. Memory changes only at [sp, sp + 16) and [sp + 56, sp + 88). -/
theorem glue_post_vec {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp cap q len : Nat) (hsp : sp + 112 ≤ 4294967296)
    (hcap : cap < 18446744073709551615) (hq : q < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s56 : μ.readN (sp + 56) 8 = Num.encodeLE 8 cap) (s64 : μ.readN (sp + 64) 8 = Num.encodeLE 8 q)
    (s72 : μ.readN (sp + 72) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, sp + 56 ≤ a → a < sp + 80 → μ.readable a = true)
    (hw0 : ∀ a, sp ≤ a → a < sp + 16 → μ.writable a = true)
    (hw56 : ∀ a, sp + 56 ≤ a → a < sp + 88 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35155 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1644 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[6] = UInt64.ofNat cap ∧
      ω'[7] = UInt64.ofNat (sp + 40) ∧ ω'[8] = UInt64.ofNat (sp + 56) ∧ ω'[9] = UInt64.ofNat 32 ∧
      ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧
      ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] ∧
      μ'.readN sp 8 = Num.encodeLE 8 len ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (sp + 56) 8 = Num.encodeLE 8 0 ∧ μ'.readN (sp + 64) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (sp + 72) 8 = Num.encodeLE 8 0 ∧ μ'.readN (sp + 80) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 16 ≤ a) → (a < sp + 56 ∨ sp + 88 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) s56
  have rq := rd8 hq s64
  have rl := rd8 hlen s72
  have hc : ¬ cap = 18446744073709551615 := by omega
  have hr0 : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw0 a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hw0, hw56, hr, hr0, rc, rq, rl, hc, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    ag_simp

/-- **35202 → t** (the stores and the return), on the hash as four words: see `glue_tail`. -/
theorem glue_tail_w {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O cap q len w0 w1 w2 w3 I S C ret t v5 v6 : Nat)
    (hsp : sp + 112 ≤ O) (hO : O + 66 ≤ 4294967296)
    (hcap : cap < 18446744073709551616) (hq : q < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hw3 : w3 < 18446744073709551616)
    (hI : I < 4294967296) (hS : S < 4294967296) (hC : C < 65536)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat cap)
    (h7 : ω[7] = UInt64.ofNat 0)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 len) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 S) (s24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 I)
    (s32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 C)
    (s56 : μ.readN (sp + 56) 8 = Num.encodeLE 8 w0) (s64 : μ.readN (sp + 64) 8 = Num.encodeLE 8 w1)
    (s72 : μ.readN (sp + 72) 8 = Num.encodeLE 8 w2) (s80 : μ.readN (sp + 80) 8 = Num.encodeLE 8 w3)
    (s88 : μ.readN (sp + 88) 8 = Num.encodeLE 8 v6) (s96 : μ.readN (sp + 96) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (sp + 104) 8 = Num.encodeLE 8 ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp ≤ a → a < sp + 112 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 66 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35202 ω μ x t ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧
      μ'.readN (O + 24) 8 = Num.encodeLE 8 w0 ∧ μ'.readN (O + 32) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (O + 40) 8 = Num.encodeLE 8 w2 ∧ μ'.readN (O + 48) 8 = Num.encodeLE 8 w3 ∧
      μ'.readN (O + 56) 4 = Num.encodeLE 4 I ∧ μ'.readN (O + 60) 4 = Num.encodeLE 4 S ∧
      μ'.readN (O + 64) 2 = Num.encodeLE 2 C ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 66 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 hlen s0
  have r8 := rd8 hq s8
  have r16 := rd8 (by omega) s16
  have r24 := rd8 (by omega) s24
  have r32 := rd8 (by omega) s32
  have r56 := rd8 hw0 s56
  have r64 := rd8 hw1 s64
  have r72 := rd8 hw2 s72
  have r80 := rd8 hw3 s80
  have r88 := rd8 hv6 s88
  have r96 := rd8 hv5 s96
  have r104 := rd8 (by omega) s104
  have hrO : ∀ a, O ≤ a → a < O + 66 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hsp, hO, hw, hr, hrO, r0, r8, r16, r24, r32, r56, r64, r72, r80, r88, r96, r104,
      hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    ag_simp

theorem readN_32 (ν : Memory) (a : Nat) :
    ν.readN a 32 = ν.readN a 8 ++ (ν.readN (a + 8) 8 ++ (ν.readN (a + 16) 8 ++ ν.readN (a + 24) 8)) := by
  have e1 := Memory.readN_split ν a 8 24
  have e2 := Memory.readN_split ν (a + 8) 8 16
  have e3 := Memory.readN_split ν (a + 8 + 8) 8 8
  simp only [Nat.reduceAdd, Nat.add_assoc] at e1 e2 e3
  rw [e1, e2, e3]

/-- **35202 → t = 4680**, the success path of the hash's read (ω₇ = 0): the result struct at
    O = ω₅ (M + 168, at or above sp + 112): cap (ω₆) at O, q (sp + 8) at O + 8, len (sp) at O + 16, the
    32 octets of the hash (sp + 56) at O + 24, i (sp + 24, `u32`) at O + 56, s (sp + 16, `u32`) at
    O + 60, c (sp + 32, `u16`) at O + 64; then ω₀, ω₅, ω₆ restored from sp + 104, sp + 96, sp + 88,
    sp + 112 in ω₁, and the jump through the jump table to t (ret = 152, `jte_75`: t = 4680). Memory
    changes only at [O, O + 66). -/
theorem glue_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O cap q len I S C ret t v5 v6 : Nat)
    (hsp : sp + 112 ≤ O) (hO : O + 66 ≤ 4294967296)
    (hcap : cap < 18446744073709551616) (hq : q < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hI : I < 4294967296) (hS : S < 4294967296) (hC : C < 65536)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat cap)
    (h7 : ω[7] = UInt64.ofNat 0)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 len) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 S) (s24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 I)
    (s32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 C)
    (s88 : μ.readN (sp + 88) 8 = Num.encodeLE 8 v6) (s96 : μ.readN (sp + 96) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (sp + 104) 8 = Num.encodeLE 8 ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp ≤ a → a < sp + 112 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 66 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35202 ω μ x t ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧ μ'.readN (O + 24) 32 = μ.readN (sp + 56) 32 ∧
      μ'.readN (O + 56) 4 = Num.encodeLE 4 I ∧ μ'.readN (O + 60) 4 = Num.encodeLE 4 S ∧
      μ'.readN (O + 64) 2 = Num.encodeLE 2 C ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 66 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω', μ', run, o0, o1, o5, o6, oc, oq, ol, ow0, ow1, ow2, ow3, oI, oS, oC, fr, rd, wr⟩ :=
    glue_tail_w (R := R) x ω μ sp O cap q len (rdN μ (sp + 56) 8) (rdN μ (sp + 64) 8) (rdN μ (sp + 72) 8)
      (rdN μ (sp + 80) 8) I S C ret t v5 v6 hsp hO hcap hq hlen (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (rdN_lt64 _ _) hI hS hC hv5 hv6 h1 h5 h6 h7 s0 s8 s16 s24 s32 (encodeLE_rdN μ _ 8).symm
      (encodeLE_rdN μ _ 8).symm (encodeLE_rdN μ _ 8).symm (encodeLE_rdN μ _ 8).symm s88 s96 s104 hret hjt hbt
      hr hw
  refine ⟨ω', μ', run, o0, o1, o5, o6, oc, oq, ol, ?_, oI, oS, oC, fr, rd, wr⟩
  rw [readN_32, readN_32, ow0, ow1, ow2, ow3, encodeLE_rdN, encodeLE_rdN, encodeLE_rdN, encodeLE_rdN]

/-- `glue_tail` at refine's call site: the saved return address 152 leads to 4680 (`jte_75`). -/
theorem glue_tail_4680 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O cap q len I S C v5 v6 : Nat)
    (hsp : sp + 112 ≤ O) (hO : O + 66 ≤ 4294967296)
    (hcap : cap < 18446744073709551616) (hq : q < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hI : I < 4294967296) (hS : S < 4294967296) (hC : C < 65536)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat cap)
    (h7 : ω[7] = UInt64.ofNat 0)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 len) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 S) (s24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 I)
    (s32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 C)
    (s88 : μ.readN (sp + 88) 8 = Num.encodeLE 8 v6) (s96 : μ.readN (sp + 96) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (sp + 104) 8 = Num.encodeLE 8 152)
    (hr : ∀ a, sp ≤ a → a < sp + 112 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 66 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35202 ω μ x 4680 ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat (sp + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧ μ'.readN (O + 24) 32 = μ.readN (sp + 56) 32 ∧
      μ'.readN (O + 56) 4 = Num.encodeLE 4 I ∧ μ'.readN (O + 60) 4 = Num.encodeLE 4 S ∧
      μ'.readN (O + 64) 2 = Num.encodeLE 2 C ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 66 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) :=
  glue_tail (P := P) x ω μ sp O cap q len I S C 152 4680 v5 v6 hsp hO hcap hq hlen hI hS hC hv5 hv6 h1 h5 h6 h7 s0 s8
    s16 s24 s32 s88 s96 s104 (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_75]) bs_4680 hr hw

end Services.Bootstrap.Refine.ArgsGlue
