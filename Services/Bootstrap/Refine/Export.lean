import Services.Bootstrap.Refine.Pass
import Services.Bootstrap.Refine.HostSteps
import Services.Bootstrap.Refine.Exit

/-!
# Refine's `Export` handler (5587 … 5042)

`Instruction::ExportSegs { data: Vec<Vec<u8>> }` (dispatch index 10): for each segment, refine calls `export`
(host 8, Ω_E: GP v0.8.0 Appendix B.4) on its octets, formats and logs the result (5744 → 59375, 5784,
5800), then pushes `Exported(n)` with n the number of segments (quirk Q11: attempts are counted, failed
exports included), frees the segments and their `Vec`, and goes round (5042). The staged element is at
M + 304, its `Vec<Vec<u8>>` `{cap, ptr, len}` at M + 312.
-/

namespace Services.Bootstrap.Refine.Export

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 5095 … 5587: back from the staging copy, an element of index 10 (`ExportSegs`, D = 2^63 + 9) goes to
    the handler at 5587, with ω₈ = 10. -/
theorem xd {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : M + 632 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat (9223372036854775807 + 10))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, M + 128 ≤ a → a < M + 144 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5095 ω μ x 5587 ω' μ x 10 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[8] = UInt64.ofNat 10 := by
  have r128 := rd8 (by decide) s128
  have r136 := rd8 (by decide) s136
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hM, hr, r128, r136, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      List.lookup_nil, Option.getD_none, Option.getD_some]

/-- 5587 … 5639: the handler keeps the index 10 at M + 72 and the segments' `Vec` `{cap, ptr, len}` (from the
    element at `cur`, ω₅) at M + 64, M + 104, M + 56, with 24·len at M + 96; with len ≠ 0 it keeps the end
    ptr + 24·len at M + 152 and goes to the first segment (5653) with ω₅ = ptr. Memory changes only at
    M + 56 … M + 112 and M + 152 … M + 160. -/
theorem xa {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cur cap ptr len : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcur : cur + 32 ≤ 4294967296) (hcM : cur + 32 ≤ M + 56 ∨ M + 160 ≤ cur)
    (hcap : cap < 18446744073709551616) (hptr : ptr + 24 * len < 18446744073709551616) (hlen : len ≠ 0)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cur) (h8 : ω[8] = UInt64.ofNat 10)
    (s8 : μ.readN (cur + 8) 8 = Num.encodeLE 8 cap) (s16 : μ.readN (cur + 16) 8 = Num.encodeLE 8 ptr)
    (s24 : μ.readN (cur + 24) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, cur + 8 ≤ a → a < cur + 32 → μ.readable a = true)
    (hw : ∀ a, M + 56 ≤ a → a < M + 160 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5587 ω μ x 5653 ω' μ' x 20 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat ptr ∧
      μ'.readN (M + 72) 8 = Num.encodeLE 8 10 ∧ μ'.readN (M + 64) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (M + 104) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (M + 96) 8 = Num.encodeLE 8 (24 * len) ∧
      μ'.readN (M + 56) 8 = Num.encodeLE 8 len ∧ μ'.readN (M + 152) 8 = Num.encodeLE 8 (ptr + 24 * len) ∧
      (∀ a, a < 4294967296 → (a < M + 56 ∨ (M + 112 ≤ a ∧ a < M + 152) ∨ M + 160 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s8
  have rp := rd8 (by omega) s16
  have rl := rd8 (by omega) s24
  have hl0 : ¬ len = 0 := hlen
  have hr2 : ∀ a, M + 56 ≤ a → a < M + 160 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h8, hM0, hM1, hM8, hcur, hcM, hl0, hr, hr2, hw, rc, rp, rl, Exit.rdN_writeN_enc8,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5653 … 5661: segment g (a `Vec<u8>` `{cap, ptr, len}` at g, ω₅ = g): g is kept at M + 552 and the
    `export` call gets ω₇ = ptr, ω₈ = len. Memory changes only at M + 552 … M + 560. -/
theorem xs1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M g sp sl : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hg : g + 24 ≤ 4294967296) (hgM : g + 24 ≤ M + 552 ∨ M + 560 ≤ g) (hsp : sp < 18446744073709551616)
    (hsl : sl < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat g)
    (s8 : μ.readN (g + 8) 8 = Num.encodeLE 8 sp) (s16 : μ.readN (g + 16) 8 = Num.encodeLE 8 sl)
    (hr : ∀ a, g + 8 ≤ a → a < g + 24 → μ.readable a = true)
    (hw : ∀ a, M + 552 ≤ a → a < M + 560 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5653 ω μ x 5664 ω' μ' x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat sl ∧ μ'.readN (M + 552) 8 = Num.encodeLE 8 g ∧
      (∀ a, a < 4294967296 → (a < M + 552 ∨ M + 560 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rp := rd8 hsp s8
  have rl := rd8 hsl s16
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hM0, hM1, hM8, hg, hgM, hr, hw, rp, rl, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    post_simp

/-- 5667 … 5744, after `export` returned v ≠ 2^64 − 1 in ω₇: the `Result<u64, HostCallError>` goes to
    M + 560 (tag 0 and v at M + 568 when v < 2^64 − 9; tag 1 and the code (2^64 − 2 − v) mod 2^8 at
    M + 561 otherwise), the `format!` arguments [(M + 552, 1250), (M + 560, 692)] to M + 168 … M + 200, and
    `alloc::fmt::format` (59375) is called for the `String` at M + 584 with template 66196 and return
    address 182 (→ 5751). Memory changes only at M + 168 … M + 200 and M + 560 … M + 576. -/
theorem xs2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M v : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hv : v < 18446744073709551616) (hv1 : v ≠ 18446744073709551615)
    (h1 : ω[1] = UInt64.ofNat M) (h7 : ω[7] = UInt64.ofNat v)
    (hw : ∀ a, M + 168 ≤ a → a < M + 200 → μ.writable a = true)
    (hw2 : ∀ a, M + 560 ≤ a → a < M + 576 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5667 ω μ x 59375 ω' μ' x 24 ∧ ω'[0] = UInt64.ofNat 182 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (M + 584) ∧ ω'[8] = UInt64.ofNat 66196 ∧
      ω'[9] = UInt64.ofNat (M + 168) ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 (M + 552) ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 1250 ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 (M + 560) ∧ μ'.readN (M + 192) 8 = Num.encodeLE 8 692 ∧
      (v < 18446744073709551607 → μ'.readN (M + 560) 1 = [UInt8.ofNat 0] ∧ μ'.readN (M + 568) 8 = Num.encodeLE 8 v) ∧
      (18446744073709551607 ≤ v → μ'.readN (M + 560) 1 = [UInt8.ofNat 1] ∧
        μ'.readN (M + 561) 1 = [UInt8.ofNat (18446744073709551614 - v)]) ∧
      (∀ a, a < 4294967296 → (a < M + 168 ∨ M + 200 ≤ a) → (a < M + 560 ∨ M + 576 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hv1' : ¬ v = 18446744073709551615 := hv1
  rw [show ω = regsNF ω [] from rfl]
  by_cases hok : v < 18446744073709551607
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hM0, hM1, hM8, hv, hok, hw, hw2, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun h => absurd h (by omega),
        fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
      post_simp
      all_goals try exact ⟨trivial, trivial⟩
  · have hge : 18446744073709551607 ≤ v := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hM0, hM1, hM8, hv, hok, hge, hv1', hw, hw2, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h hok, fun _ => ?_,
        fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
      post_simp
      all_goals try exact ⟨trivial, trivial⟩

/-- 5751 … 5780: the `String` `{cap, ptr, len}` at M + 584 (cap kept at M + 160): the `log` arguments, level 2,
    target 66793 (4 octets), message (ptr, len), with ω₆ = ptr. -/
theorem xl {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap ptr len : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hcap : cap < 18446744073709551616) (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s584 : μ.readN (M + 584) 8 = Num.encodeLE 8 cap) (s592 : μ.readN (M + 592) 8 = Num.encodeLE 8 ptr)
    (s600 : μ.readN (M + 600) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 584 ≤ a → a < M + 608 → μ.readable a = true)
    (hw : ∀ a, M + 160 ≤ a → a < M + 168 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5751 ω μ x 5784 ω' μ' x 12 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat ptr ∧ μ'.readN (M + 160) 8 = Num.encodeLE 8 cap ∧
      (∀ a, a < 4294967296 → (a < M + 160 ∨ M + 168 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s584
  have rp := rd8 hptr s592
  have rl := rd8 hlen s600
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hw, rc, rp, rl, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    post_simp

/-- 5787 … 5800, the `String`'s capacity (at M + 160) nonzero: `dealloc(ω₆, cap, 1)` (40613, return address
    186 → 5807). -/
theorem xf {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap : Nat) (hM : M + 168 ≤ 4294967296) (hcap : cap ≠ 0) (hcap' : cap < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (s160 : μ.readN (M + 160) 8 = Num.encodeLE 8 cap)
    (hr : ∀ a, M + 160 ≤ a → a < M + 168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5787 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 186 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] := by
  have rc := rd8 hcap' s160
  have hc0 : ¬ cap = 0 := hcap
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hc0, hr, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    all_goals try simp

/-- 5787 … 5791, capacity 0: on to the next segment (5641). -/
theorem xf0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : M + 168 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s160 : μ.readN (M + 160) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, M + 160 ≤ a → a < M + 168 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5787 ω μ x 5641 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] := by
  have rc := rd8 (by decide) s160
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, ↓rdN_fold]
  · refine ⟨?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5807: back from the `String`'s `dealloc`, on to the next segment (5641). -/
theorem xf1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) : FreeStepsH p R 5807 ω μ x 5641 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go []

/-- 5641 … 5649: the next segment g + 24, back to 5653, or after the last (g + 24 = end at M + 152) on to
    5810. -/
theorem xn {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M g en : Nat) (hM : M + 160 ≤ 4294967296) (hg : g + 24 < 18446744073709551616)
    (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat g) (s152 : μ.readN (M + 152) 8 = Num.encodeLE 8 en)
    (hr : ∀ a, M + 152 ≤ a → a < M + 160 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5641 ω μ x (if g + 24 = en then 5810 else 5653) ω' μ x 4 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (g + 24) := by
  have re := rd8 hen s152
  rw [show ω = regsNF ω [] from rfl]
  by_cases he : g + 24 = en
  · simp only [he, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hM, hg, hr, re, he, ↓rdN_fold]
    · refine ⟨?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)
  · simp only [he, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hM, hg, hr, re, he, ↓rdN_fold]
    · refine ⟨?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)

/-- 5810 … 5819, with room in the output (`len ≠ cap`, M + 264, M + 248): on to 5832 with ω₅ = len. -/
theorem xp0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap len : Nat) (hM : M + 272 ≤ 4294967296) (hne : len ≠ cap)
    (hcap : cap < 18446744073709551616) (hlen : len < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5810 ω μ x 5832 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat len := by
  have rc := rd8 hcap sc
  have rl := rd8 hlen sl
  have hne' : ¬ len = cap := hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hne', hr, rc, rl, ↓rdN_fold]
  · refine ⟨?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5810 … 5826, the output full (`len = cap`): `RawVec::grow_one` (32785) on the output at M + 248, return
    address 188 (→ 5832), with ω₅ = len. -/
theorem xpg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M len : Nat) (hM : M + 272 ≤ 4294967296) (hlen : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len) (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5810 ω μ x 32785 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 188 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat len ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (M + 248) := by
  have rc := rd8 hlen sc
  have rl := rd8 hlen sl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, rl, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hlen]

/-- 5832 … 5865: the slot `ptr + 232 len` (ptr at M + 256, len in ω₅) gets `Exported(n)`: its first word
    2^63 + 19 (from M + 136), its count n (from M + 56); len + 1 goes to M + 264; then the segments are freed
    (5868) when n ≠ 0, else on to 5909. Memory changes only in the slot's first 16 octets and M + 264. -/
theorem xps {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M ptr len n : Nat) (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0)
    (hd : ptr + 232 * len + 16 ≤ 4294967296) (hdM : ptr + 232 * len + 16 ≤ M + 56 ∨ M + 272 ≤ ptr + 232 * len)
    (hlen : len + 1 < 18446744073709551616) (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat len)
    (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr) (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (s56 : μ.readN (M + 56) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, M + 56 ≤ a → a < M + 272 → μ.readable a = true)
    (hw : ∀ a, ptr + 232 * len ≤ a → a < ptr + 232 * len + 16 → μ.writable a = true)
    (hw2 : ∀ a, M + 264 ≤ a → a < M + 272 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5832 ω μ x (if n = 0 then 5909 else 5868) ω' μ' x 12 ∧ ω'[1] = ω[1] ∧
      μ'.readN (ptr + 232 * len) 8 = Num.encodeLE 8 (9223372036854775807 + 20) ∧
      μ'.readN (ptr + 232 * len + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      (∀ a, a < 4294967296 → (a < ptr + 232 * len ∨ ptr + 232 * len + 16 ≤ a) → (a < M + 264 ∨ M + 272 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rp := rd8 (by omega) sp
  have r136 := rd8 (by decide) s136
  have rn := rd8 hn s56
  have e1 : (len * 232 + ptr) % 18446744073709551616 = ptr + 232 * len := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hr2 : ∀ a, ptr + 232 * len ≤ a → a < ptr + 232 * len + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, hM0, hM1, hM8, hd, hdM, hlen, hr, hr2, hw, hw2, rp, r136, rn, e1, rdN_writeN_disjoint,
        ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try simp only [show ptr + len * 232 = ptr + 232 * len by omega]
      post_simp
  · have hn0' : ¬ n = 0 := hn0
    simp only [hn0', ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, hM0, hM1, hM8, hd, hdM, hlen, hn0', hr, hr2, hw, hw2, rp, r136, rn, e1, rdN_writeN_disjoint,
        ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try simp only [show ptr + len * 232 = ptr + 232 * len by omega]
      post_simp

/-- 5868 … 5880: the free loop over the n segments at ptr (M + 104; 24·n at M + 96) starts at 5888 with
    ω₅ = ptr + 8 and ω₆ = ptr + 8 + 24·n. -/
theorem xr0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M ptr n : Nat) (hM : M + 112 ≤ 4294967296) (hp : ptr + 8 + 24 * n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M)
    (s104 : μ.readN (M + 104) 8 = Num.encodeLE 8 ptr) (s96 : μ.readN (M + 96) 8 = Num.encodeLE 8 (24 * n))
    (hr : ∀ a, M + 96 ≤ a → a < M + 112 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5868 ω μ x 5888 ω' μ x 6 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (ptr + 8) ∧
      ω'[6] = UInt64.ofNat (ptr + 8 + 24 * n) := by
  have rp := rd8 (by omega) s104
  have rn := rd8 (by omega) s96
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rp, rn, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    all_goals try (congr 1; omega)

/-- 5888 … 5900, segment `{cap, q, len}` at ω₅ − 8 with cap ≠ 0: `dealloc(q, cap, 1)` (return address 190 →
    5907). -/
theorem xr1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (g cap q : Nat) (hg : 8 ≤ g ∧ g + 8 ≤ 4294967296) (hcap : cap ≠ 0) (hcap' : cap < 18446744073709551616)
    (hq : q < 18446744073709551616) (h5 : ω[5] = UInt64.ofNat g)
    (s0 : μ.readN (g - 8) 8 = Num.encodeLE 8 cap) (s8 : μ.readN g 8 = Num.encodeLE 8 q)
    (hr : ∀ a, g - 8 ≤ a → a < g + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5888 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 190 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have e : (g + 18446744073709551608) % 18446744073709551616 = g - 8 := by omega
  have rc := rd8 hcap' s0
  have rq := rd8 hq s8
  have hc0 : ¬ cap = 0 := hcap
  have rc2 : rdN μ (g + 18446744073709551608) 8 = cap := by
    have hrd : μ.readN (g + 18446744073709551608) 8 = μ.readN (g - 8) 8 := readN_congr2 (fun j hj => by
      unfold Memory.read
      rw [show (g + 18446744073709551608 + j) % two32 = (g - 8 + j) % two32 by unfold two32; omega])
    unfold rdN; rw [hrd]; exact rc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, hg, hc0, hr, rc2, rq, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]

/-- 5888 … 5892, a segment with capacity 0: on to 5882. -/
theorem xr1z {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (g : Nat) (hg : 8 ≤ g ∧ g ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat g)
    (s0 : μ.readN (g - 8) 8 = Num.encodeLE 8 0) (hr : ∀ a, g - 8 ≤ a → a < g → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5888 ω μ x 5882 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have e : (g + 18446744073709551608) % 18446744073709551616 = g - 8 := by omega
  have rc := rd8 (by decide) s0
  have rc2 : rdN μ (g + 18446744073709551608) 8 = 0 := by
    have hrd : μ.readN (g + 18446744073709551608) 8 = μ.readN (g - 8) 8 := readN_congr2 (fun j hj => by
      unfold Memory.read
      rw [show (g + 18446744073709551608 + j) % two32 = (g - 8 + j) % two32 by unfold two32; omega])
    unfold rdN; rw [hrd]; exact rc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, hg, hr, rc2, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]

/-- 5907: back from a segment's `dealloc`, to 5882. -/
theorem xr1r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) : FreeStepsH p R 5907 ω μ x 5882 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go []

/-- 5882 … 5885: the next segment, back to 5888 while ω₅ + 24 ≠ ω₆, else on to 5909. -/
theorem xr2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (g e : Nat) (hg : g + 24 < 18446744073709551616) (he : e < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat g) (h6 : ω[6] = UInt64.ofNat e) :
    ∃ ω', FreeStepsH p R 5882 ω μ x (if g + 24 = e then 5909 else 5888) ω' μ x 2 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (g + 24) ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hh : g + 24 = e
  · simp only [hh, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, h6, hg, he, hh]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]
      all_goals try (congr 1; omega)
  · simp only [hh, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, h6, hg, he, hh]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]
      all_goals try (congr 1; omega)

/-- 5909 … 5931, the segments' `Vec` capacity c (M + 64) nonzero: `dealloc(ptr, 24 c, 8)` with ptr from M + 104
    (return address 192 → 5938). -/
theorem xt0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M c ptr : Nat) (hM : M + 112 ≤ 4294967296) (hc : c ≠ 0) (hc' : 24 * c < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat M)
    (s64 : μ.readN (M + 64) 8 = Num.encodeLE 8 c) (s104 : μ.readN (M + 104) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, M + 64 ≤ a → a < M + 112 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5909 ω μ x 40613 ω' μ x 10 ∧ ω'[0] = UInt64.ofNat 192 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have rc := rd8 (by omega) s64
  have rp := rd8 hptr s104
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hc0, hr, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5909 … 5913, capacity 0: on to 5938. -/
theorem xt0z {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : M + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s64 : μ.readN (M + 64) 8 = Num.encodeLE 8 0) (hr : ∀ a, M + 64 ≤ a → a < M + 72 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5909 ω μ x 5938 ω' μ x 4 ∧ ω'[1] = ω[1] := by
  have rc := rd8 (by decide) s64
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 5938 … 5956: index 10 (M + 72) with bit 10 of the mask at M + 40 set: no drop of the staged element; back
    to the loop head 5042. -/
theorem xt1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M : Nat) (hM : M + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s72 : μ.readN (M + 72) 8 = Num.encodeLE 8 10) (s40 : μ.readN (M + 40) 8 = Num.encodeLE 8 2098688)
    (hr : ∀ a, M + 40 ≤ a → a < M + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5938 ω μ x 5042 ω' μ x 10 ∧ ω'[1] = ω[1] := by
  have r72 := rd8 (by decide) s72
  have r40 := rd8 (by decide) s40
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, r72, r40, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Refine.Export
