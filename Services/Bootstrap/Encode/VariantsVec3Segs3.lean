import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `Designate` (13)

`Designate`'s arm (19322 … 19471): the tag 13, the `Vec`'s length n (S + 24, checked against 2^32:
the code traps at 19351 → 20397 otherwise) and its length prefix, then a loop over the n 336-octet keys
from q (S + 16): the octets left 336 i at sp + 8, the next key at sp, and each key at a appended in four
calls straight from the heap, its octets [a + 128, a + 160), [a + 160, a + 192), [a + 192, a + 336) and
[a, a + 128), the writer in ω₅. The end is 20118. One theorem per piece, proved by symbolic execution
(`pvm_go`), as in `Encode.VecSegs`.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 19322 … 19336 (`Designate`, tag 13): the tag octet at sp + 24 and the call for it (return 836 →
    19343), with S (ω₁₁) in ω₅ and the writer (ω₁₀) in ω₇. -/
theorem seg_19322 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19322 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 836 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat S ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 13] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 19343 … 19367 (`Designate`): the `Vec`'s length n < 2^32 (S + 24, ω₅ = S) as a 32-bit word to
    sp + 24 and its pointer q (S + 16) in ω₆; the call of the length prefix with ω₇ = sp + 24, the writer
    (from sp + 16) in ω₈ and n in ω₅ (return 838 → 19373). -/
theorem seg_19343 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19343 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 838 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat q ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have rv := rd8 hv v16
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hr : ∀ a, sp + 16 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, hS, hw, hr, hrS, r16, r24, rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 19373 (`Designate`, no keys): n = 0, on to the end at 20118. -/
theorem seg_19373_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 19373 ω μ x 20118 ω' μ x 1 ∧ ω' = ω := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · rfl

/-- 19373 … 19384 (`Designate`, n > 0 keys): ω₇ = 336 n, the writer (from sp + 16) in ω₅; on to the
    loop at 19385. -/
theorem seg_19373_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hn : 0 < n ∧ 336 * n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, sp + 16 ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 19373 ω μ x 19385 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat v ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (336 * n) := by
  have rv := rd8 hv v16
  have hn0 : ¬ n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hr, rv, hn0, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.mod_eq_of_lt hv]
    all_goals try (congr 1; omega)

/-- 19385 … 19403 (`Designate`, one key at a = ω₆, r = ω₇ octets left): r to sp + 8, a + 336 to sp, and
    the call appending the 32 octets at a + 128 (return 840 → 19410), the writer from ω₅. -/
theorem seg_19385 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a r : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (ha : a + 336 < 18446744073709551616) (hr64 : r < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat a)
    (h7 : ω[7] = UInt64.ofNat r)
    (hw : ∀ b, sp ≤ b → b < sp + 16 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 19385 ω μ x 58508 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 840 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (a + 128) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN sp 8 = Num.encodeLE 8 (a + 336) ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 r ∧
      (∀ b, b < 4294967296 → (b < sp ∨ sp + 16 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, h7, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hr64, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption

/-- 19410 … 19451 (`Designate`, the key at a = ω₆): the calls appending the 32 octets at a + 160
    (19410, return 842), the 144 at a + 192 (19426, return 844) and the 128 at a (19443, return 846),
    the writer from ω₅. -/
theorem seg_keyD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (e r off k v a : Nat)
    (he : (e = 19410 ∧ r = 842 ∧ off = 160 ∧ k = 32) ∨ (e = 19426 ∧ r = 844 ∧ off = 192 ∧ k = 144) ∨
      (e = 19443 ∧ r = 846 ∧ off = 0 ∧ k = 128))
    (hv : v < 18446744073709551616) (ha : a + 336 < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat a) :
    ∃ ω', FreeStepsH p R e ω μ x 58508 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (a + off) ∧ ω'[9] = UInt64.ofNat k := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, h6]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hv,
        Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega)]
      all_goals try (congr 1; omega)
      all_goals try simp only [Nat.add_zero]

/-- 19458 … 19467 (`Designate`, after a key, more left): the octets left r (sp + 8) less 336 is not 0;
    the next key b from sp in ω₆; back to 19385. -/
theorem seg_19458_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp r b : Nat) (hsp : sp + 32 ≤ 4294967296) (hr : 672 ≤ r ∧ r < 18446744073709551616)
    (hb : b < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 b) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r)
    (hrd : ∀ c, sp ≤ c → c < sp + 16 → μ.readable c = true) :
    ∃ ω', FreeStepsH p R 19458 ω μ x 19385 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat b ∧ ω'[7] = UInt64.ofNat (r - 336) := by
  have r8 := rd8 hr.2 s8
  have r0 := rd8 hb s0
  have hne : ¬ (r + 18446744073709551280) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hrd, r8, r0, hne, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
    all_goals try (congr 1; omega)

/-- 19458 … 19471 (`Designate`, after the last key): r = 336; on to the end at 20118. -/
theorem seg_19458_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp b : Nat) (hsp : sp + 32 ≤ 4294967296) (hb : b < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 b) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 336)
    (hrd : ∀ c, sp ≤ c → c < sp + 16 → μ.readable c = true) :
    ∃ ω', FreeStepsH p R 19458 ω μ x 20118 ω' μ x 6 ∧ ω'[1] = ω[1] := by
  have r8 := rd8 (by decide) s8
  have r0 := rd8 hb s0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hrd, r8, r0, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Encode.Enc
