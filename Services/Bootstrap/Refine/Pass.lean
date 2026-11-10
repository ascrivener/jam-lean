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
      (∀ a, a < 4294967296 → (a < M + 144 ∨ M + 312 ≤ a) → μ'.read a = μ.read a) ∧
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
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
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

end Services.Bootstrap.Refine.Pass
