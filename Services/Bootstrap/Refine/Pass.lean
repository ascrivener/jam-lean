import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.CodeX
import Services.Bootstrap.CodeRAll

/-!
# Refine's transform loop: the instructions passed through unchanged

Refine's body walks the decoded instructions (232 octets each, from `cur` to `end`, kept at M + 144 and
M + 120 of its frame at M) and builds its output `Vec<Instruction>` `{cap, ptr, len}` at M + 248. For
each element it stages the element at M + 304 (its first word, then the other 224 octets by `memcpy`,
`pa`), dispatches on the index `D − (2^63 − 1)` of its first word D (`pd`): every index but 8 (`Lookup`),
9 (`Import`), 10 (`Export`) and 21 (`RandomStorageRefine`) goes to 5561, which, when the output has room
(`len ≠ cap`), copies the 232 staged octets to `ptr + 232 len` (`pc`) and stores `len + 1` (`pi`).
The growth path (`len = cap`, `RawVec::grow_one`, 32785) is not covered here.
-/

namespace Services.Bootstrap.Refine.Pass

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 5042 … 5088: with `cur ≠ end` (M + 144, M + 120) and the element's first word D at `cur` not the
    error word 2^64 − 2, the loop stores `cur + 232` at M + 280 and M + 144, D at M + 304, and calls
    `memcpy` for the element's other 224 octets, from `cur + 8` to M + 312 (return address 162 → 5095). -/
theorem pa {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cur en D : Nat) (hM : M + 632 ≤ 4294967296) (hcur : cur + 232 < 4294967296)
    (hcM : cur + 8 ≤ M + 120 ∨ M + 320 ≤ cur) (hne : cur ≠ en) (hen : en < 18446744073709551616)
    (hD : D < 18446744073709551616) (hDe : D ≠ 18446744073709551614)
    (h1 : ω[1] = UInt64.ofNat M) (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 cur)
    (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en) (sD : μ.readN cur 8 = Num.encodeLE 8 D)
    (hr : ∀ a, M + 120 ≤ a → a < M + 152 → μ.readable a = true)
    (hrc : ∀ a, cur ≤ a → a < cur + 8 → μ.readable a = true)
    (hw : ∀ a, M + 144 ≤ a → a < M + 312 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5042 ω μ x 68729 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 162 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[6] = UInt64.ofNat D ∧
      ω'[7] = UInt64.ofNat (M + 312) ∧ ω'[8] = UInt64.ofNat (cur + 8) ∧ ω'[9] = UInt64.ofNat 224 ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 304) 8 = Num.encodeLE 8 D ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (cur + 232) ∧
      (∀ a, a < 4294967296 → (a < M + 144 ∨ (M + 152 ≤ a ∧ a < M + 280) ∨ (M + 288 ≤ a ∧ a < M + 304) ∨
        M + 312 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) s144
  have re := rd8 hen s120
  have rD := rd8 hD sD
  have hne' : ¬ cur = en := hne
  have hDe' : ¬ D = 18446744073709551614 := hDe
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM, hcur, hcM, hne', hDe', hr, hrc, hw, rc, re, rD, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hD]
    post_simp
    all_goals try assumption

/-- The indices refine passes through unchanged: every index of a variant but `Lookup` (8), `Import`
    (9), `Export` (10) and `RandomStorageRefine` (21). -/
def PassIdx (t : Nat) : Prop := 1 ≤ t ∧ t < 25 ∧ t ≠ 8 ∧ t ≠ 9 ∧ t ≠ 10 ∧ t ≠ 21

/-- 5095 … 5561: back from the copy, the loop computes the index of D = 2^63 + t − 1 (with the constants
    2^63 + 24 and 2^63 + 1 at M + 128, M + 136) and, for an index passed through, goes to 5561. -/
theorem pd {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M t : Nat) (ht : PassIdx t) (hM : M + 632 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat (9223372036854775807 + t))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, M + 128 ≤ a → a < M + 144 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5095 ω μ x 5561 ω' μ x 10 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] := by
  have r128 := rd8 (by decide) s128
  have r136 := rd8 (by decide) s136
  rw [show ω = regsNF ω [] from rfl]
  unfold PassIdx at ht
  have : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨
      t = 15 ∨ t = 16 ∨ t = 17 ∨ t = 18 ∨ t = 19 ∨ t = 20 ∨ t = 22 ∨ t = 23 ∨ t = 24 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hM, hr, r128, r136, ↓rdN_fold]
    · refine ⟨?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        List.lookup_nil, Option.getD_none]

/-- 5561 … 5027, with room in the output (`len ≠ cap`, at M + 264 and M + 248): the loop calls `memcpy` for
    the 232 staged octets, from M + 304 to `ptr + 232 len` (ptr at M + 256; return address 160 → 5034),
    with len in ω₅. -/
theorem pc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M cap ptr len : Nat) (hM : M + 632 ≤ 4294967296) (hne : len ≠ cap)
    (hcap : cap < 18446744073709551616) (hptr : ptr + 232 * len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap)
    (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr) (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5561 ω μ x 68729 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 160 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[7] = UInt64.ofNat (ptr + 232 * len) ∧ ω'[8] = UInt64.ofNat (M + 304) ∧ ω'[9] = UInt64.ofNat 232 := by
  have rc := rd8 hcap sc
  have rp := rd8 (by omega) sp
  have rl := rd8 (by omega) sl
  have hne' : ¬ len = cap := hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hne', hr, rc, rp, rl, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    all_goals try (congr 1; omega)

/-- 5034 … 5042: back from the copy, the loop stores `len + 1` at M + 264 and goes round. -/
theorem pi {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M len : Nat) (hM : M + 632 ≤ 4294967296) (hl : len + 1 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat len)
    (hw : ∀ a, M + 264 ≤ a → a < M + 272 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5034 ω μ x 5042 ω' μ' x 4 ∧ ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      (∀ a, a < 4294967296 → (a < M + 264 ∨ M + 272 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hM, hw]
  · refine ⟨?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 5561 … 5578, with the output full (`len = cap`): the loop calls `RawVec::grow_one` (32785) on the
    output at M + 248 (return address 180 → 5584), with len in ω₅. -/
theorem pg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M len : Nat) (hM : M + 632 ≤ 4294967296) (hl : len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 len)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, M + 248 ≤ a → a < M + 272 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5561 ω μ x 32785 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 180 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (M + 248) := by
  have rc := rd8 hl sc
  have rl := rd8 hl sl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hM, hr, rc, rl, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hl]

/-- 5584 … 5027: back from `grow_one`, the loop calls `memcpy` for the 232 staged octets, from M + 304
    to `ptr + 232 len` (ptr at M + 256, len in ω₅; return address 160 → 5034). -/
theorem pc2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M ptr len : Nat) (hM : M + 632 ≤ 4294967296) (hptr : ptr + 232 * len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat len)
    (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, M + 256 ≤ a → a < M + 264 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5584 ω μ x 68729 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 160 ∧ ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[7] = UInt64.ofNat (ptr + 232 * len) ∧ ω'[8] = UInt64.ofNat (M + 304) ∧ ω'[9] = UInt64.ofNat 232 := by
  have rp := rd8 (by omega) sp
  have hl : len < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hM, hr, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hl]
    all_goals try (congr 1; omega)

theorem readN_add2 (μ : Memory) (a n m : Nat) : μ.readN a (n + m) = μ.readN a n ++ μ.readN (a + n) m := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.add_assoc]

/-- **One instruction passed through** (5042 … 5042): with the element at `cur` (≠ `end`) of an index
    passed through (`PassIdx`) and room in the output (`len ≠ cap`), the loop copies the element's 232
    octets unchanged to `ptr + 232 len`, and stores `cur + 232` and `len + 1`. Memory changes only in the
    frame [M − 48, M + 632) and the output slot. -/
theorem pass_elem {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X)
    (ω : Regs) (μ : Memory) (M cur en t cap ptr len : Nat) (ht : PassIdx t)
    (hM : 65536 + 48 ≤ M ∧ M + 632 + 16 < 4294967296 ∧ M % 8 = 0)
    (hcur : 65536 ≤ cur ∧ cur + 232 + 24 < 4294967296) (hcM : cur + 232 + 24 ≤ M - 48 ∨ M + 632 ≤ cur)
    (hne : cur ≠ en) (hen : en < 18446744073709551616) (hl : len ≠ cap) (hcap : cap < 18446744073709551616)
    (hd : 65536 ≤ ptr + 232 * len ∧ ptr + 232 * len + 232 + 24 < 4294967296)
    (hdM : ptr + 232 * len + 232 + 16 ≤ M - 48 ∨ M + 632 ≤ ptr + 232 * len)
    (hdc : ptr + 232 * len + 232 + 24 ≤ cur ∨ cur + 232 + 24 ≤ ptr + 232 * len)
    (h1 : ω[1] = UInt64.ofNat M)
    (s144 : μ.readN (M + 144) 8 = Num.encodeLE 8 cur) (s120 : μ.readN (M + 120) 8 = Num.encodeLE 8 en)
    (sD : μ.readN cur 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (sc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (sp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (M + 264) 8 = Num.encodeLE 8 len)
    (hrc : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true)
    (hwM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true)
    (hwd : ∀ a, ptr + 232 * len ≤ a → a < ptr + 232 * len + 232 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 5042 ω μ x 5042 ω' μ' x 4000 ∧ ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (cur + 232) ∧ μ'.readN (M + 264) 8 = Num.encodeLE 8 (len + 1) ∧
      μ'.readN (ptr + 232 * len) 232 = μ.readN cur 232 ∧
      μ'.readN (M + 120) 8 = Num.encodeLE 8 en ∧
      μ'.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832 ∧
      μ'.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809 ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 ptr ∧
      (∀ a, a < 4294967296 → (a < M - 48 ∨ M + 632 ≤ a) → (a < ptr + 232 * len ∨ ptr + 232 * len + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (cur + 232) ∧
      (∀ a, (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 264) ∨ (M + 272 ≤ a ∧ a < M + 280) ∨
        (M + 288 ≤ a ∧ a < M + 304) ∨ (M + 536 ≤ a ∧ a < M + 632) → μ'.read a = μ.read a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hr : ∀ a, M - 48 ≤ a → a < M + 632 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwM a h1 h2)
  obtain ⟨ω1, μ1, run1, a0, a1, a6, a7, a8, a9, a144, a304, a280, afr, ard, awr⟩ := pa (p := p) (P := P) (R := R) x ω μ
    M cur en (9223372036854775807 + t) (by omega) (by omega) (by omega) hne hen (by unfold PassIdx at ht; omega)
    (by unfold PassIdx at ht; omega) h1 s144 s120 sD (fun a h1 h2 => hr a (by omega) (by omega))
    (fun a h1 h2 => hrc a h1 (by omega)) (fun a h1 h2 => hwM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bd, bfr, brd, bwr⟩ := memcpy_any (p := p) (P := P) (R := R) x ω1 μ1
    162 5095 M (M + 312) (cur + 8) 224 a0 a1 a7 a8 a9 ⟨by decide, by decide, by decide⟩ jte_80 bs_5095
    ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [ard]; exact hrc a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact hwM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact hwM a (by omega) (by omega))
  -- outside [M − 48, M) and [M + 144, M + 536), μ2 is μ
  have k2 : ∀ a, a < 4294967296 → (a < M - 48 ∨ (M ≤ a ∧ a < M + 144) ∨ (M + 152 ≤ a ∧ a < M + 280) ∨
      M + 536 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 => by rw [bfr a h0 (by omega) (by omega), afr a h0 (by omega)]
  obtain ⟨ω3, run3, c1, c5⟩ := pd (p := p) (P := P) (R := R) x ω2 μ2 M t ht (by omega) b1
    (by rw [b6, a6])
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136)
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
  obtain ⟨ω4, run4, d0, d1, d5, d7, d8, d9⟩ := pc (p := p) (P := P) (R := R) x ω3 μ2 M cap ptr len (by omega) hl hcap
    (by omega) (c1.trans b1)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sc)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sp)
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sl)
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
  -- the staged element
  have stage : μ2.readN (M + 304) 232 = μ.readN cur 232 := by
    rw [show (232 : Nat) = 8 + 224 from rfl, readN_add2, readN_add2, show M + 304 + 8 = M + 312 by omega, bd,
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega)), a304, ← sD,
      Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ed, efr, erd, ewr⟩ := memcpy_any (p := p) (P := P) (R := R) x ω4 μ2
    160 5034 M (ptr + 232 * len) (M + 304) 232 d0 d1 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_79 bs_5034
    ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) (by omega))
    (fun a h1 h2 => by rw [bwr, awr]; exact hwd a h1 h2)
    (fun a h1 h2 => by rw [bwr, awr]; exact hwM a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, f1, f264, ffr, frd, fwr⟩ := pi (p := p) (P := P) (R := R) x ω5 μ5 M len (by omega)
    (by omega) e1 (by rw [e5, d5])
    (fun a h1 h2 => by rw [ewr, bwr, awr]; exact hwM a (by omega) (by omega))
  -- μ6 against μ2, away from the output slot and M + 264
  have k6 : ∀ a, a < 4294967296 → (a < M - 48 ∨ M ≤ a) → (a < M + 264 ∨ M + 272 ≤ a) →
      (a < ptr + 232 * len ∨ ptr + 232 * len + 232 ≤ a) → μ6.read a = μ2.read a := fun a h0 h1 h2 h3 => by
    rw [ffr a h0 h2, efr a h0 h3 (by omega)]
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega), f1,
    ?_, f264, ?_, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 => ?_, fun a => by rw [frd, erd, brd, ard],
    fun a => by rw [fwr, ewr, bwr, awr], ?_, fun a ha => ?_⟩
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a144
  · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), ed]; exact stage
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s120
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s128
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact s136
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sc
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact sp
  · rw [k6 a h0 (by omega) (by omega) h2, k2 a h0 (by omega)]
  · rw [Memory.readN_congr (fun j hj => k6 _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]; exact a280
  · rw [k6 a (by omega) (by omega) (by omega) (by omega)]
    rcases ha with h | h | h | h | h
    · exact k2 a (by omega) (by omega)
    · exact k2 a (by omega) (by omega)
    · exact k2 a (by omega) (by omega)
    · rw [bfr a (by omega) (by omega) (by omega), afr a (by omega) (by omega)]
    · exact k2 a (by omega) (by omega)

end Services.Bootstrap.Refine.Pass
