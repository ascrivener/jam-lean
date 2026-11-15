import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `DeleteItems` (dispatch index 5)

`DeleteItems { items: Vec<Vec<u8>> }` (arm 19117 … 19253) has the same code as `Imported`
(19983 … 20131, `Encode.VecSegs2`) at other addresses: the tag octet, the items' count ℰ(m), then a
loop (19193 … 19250) over the 24-octet `Vec<u8>`s, appending ℰ(nⱼ) and the octets of each, and on to
the shared end 20118. The code traps (20397) on a length of 2^32 or more.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 19117 … 19133 (`DeleteItems`, tag 5): the tag octet at sp + 24 and the call for it (return 820 →
    19140), with S (ω₁₁) in ω₅ and the writer v (ω₁₀) in ω₆. -/
theorem seg_19117 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19117 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 820 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat 5] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 19140 … 19167 (`DeleteItems`): the `Vec`'s pointer q (S + 16) to sp + 8 and its length m < 2^32
    (S + 24) as a 32-bit word to sp + 24; the call of the length prefix with ω₇ = sp + 24, the writer
    (ω₆) in ω₈, m in ω₅ (return 822 → 19173). -/
theorem seg_19140 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v S q m : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (hS : S + 32 ≤ 4294967296) (hq : q < 18446744073709551616) (hm : m < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 m)
    (hrS : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 19140 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 822 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat m ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 q ∧ rdN μ' (sp + 24) 4 = m ∧
      (∀ a, a < 4294967296 → (a < sp + 8 ∨ sp + 16 ≤ a) → (a < sp + 24 ∨ sp + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hq s16
  have r24 := rd8 (by omega) s24
  have hsh : m >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hm
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hS, hw, hrS, r16, r24, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show m < 18446744073709551616 by omega)]
    post_simp
    all_goals try assumption
    all_goals try (show Num.decodeLE _ = _; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega),
      Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- 19173 (`DeleteItems`, no items): m = 0, on to the end at 20118. -/
theorem seg_19173_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (h5 : ω[5] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 19173 ω μ x 20118 ω' μ x 1 ∧ ω' = ω := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5]
  · rfl

/-- 19173 … 19192 (`DeleteItems`, m > 0 items): ω₉ = 24 m, the octets of the items left, and ω₅ =
    q + 16, the length word of the first item (q from sp + 8); on to the loop at 19193. -/
theorem seg_19173_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q m : Nat) (hsp : sp + 32 ≤ 4294967296) (hq : q + 16 < 18446744073709551616)
    (hm : 0 < m ∧ m < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat m)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 q)
    (hr : ∀ a, sp + 8 ≤ a → a < sp + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 19173 ω μ x 19193 ω' μ x 10 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (q + 16) ∧ ω'[6] = ω[6] ∧ ω'[9] = UInt64.ofNat (24 * m) := by
  have r8 := rd8 (by omega) s8
  have hm0 : ¬ m = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hr, r8, hm0, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    all_goals try (congr 1; omega)

/-- 19193 … 19221 (`DeleteItems`, one item): at ω₅ = a the item's length word, its length n < 2^32,
    and at a − 8 its pointer e; e to sp, n as a 32-bit word to sp + 24, the octets left (ω₉) to sp + 8;
    the call of the length prefix with ω₇ = sp + 24, the writer (from sp + 16) in ω₈ and n in ω₆ (return
    824 → 19227). -/
theorem seg_19193 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v a e n r : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (ha : 8 ≤ a ∧ a + 8 ≤ 4294967296) (he : e < 18446744073709551616) (hn : n < 4294967296)
    (hr64 : r < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a) (h9 : ω[9] = UInt64.ofNat r)
    (sa : μ.readN a 8 = Num.encodeLE 8 n) (se : μ.readN (a - 8) 8 = Num.encodeLE 8 e)
    (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hra : ∀ b, a - 8 ≤ b → b < a + 8 → μ.readable b = true)
    (haw : a + 8 ≤ sp ∨ sp + 32 ≤ a - 8)
    (hw : ∀ b, sp ≤ b → b < sp + 32 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 19193 ω μ x 30977 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 824 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat a ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (sp + 24) ∧ ω'[8] = UInt64.ofNat v ∧
      μ'.readN sp 8 = Num.encodeLE 8 e ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 r ∧ rdN μ' (sp + 24) 4 = n ∧
      (∀ b, b < 4294967296 → (b < sp ∨ sp + 16 ≤ b) → (b < sp + 24 ∨ sp + 28 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have ra := rd8 (by omega) sa
  have re := rd8 he se
  have rv := rd8 hv v16
  have hsh : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hr : ∀ b, sp ≤ b → b < sp + 32 → μ.readable b = true :=
    fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have hra' : ∀ b, (a + 18446744073709551608) % 18446744073709551616 ≤ b →
      b < (a + 18446744073709551608) % 18446744073709551616 + 8 → μ.readable b = true :=
    fun b h1 h2 => hra b (by omega) (by omega)
  have hae : (a + 18446744073709551608) % 18446744073709551616 = a - 8 := by omega
  have hm8 : μ.readN (a + 18446744073709551608) 8 = μ.readN (a - 8) 8 := by
    unfold Memory.readN; apply List.map_congr_left; intro k _
    unfold Memory.read
    rw [show (a + 18446744073709551608 + k) % two32 = (a - 8 + k) % two32 by unfold two32; omega]
  have re' : rdN μ (a + 18446744073709551608) 8 = e := by
    show Num.decodeLE (μ.readN _ 8) = _; rw [hm8]; exact re
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h9, hsp, ha, hw, hr, hra, hae, ra, re, re', rv, hsh, ↓rdN_fold, rdN_writeN_disjoint]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 hb2 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, h9, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)]
    all_goals try (
      rw [rdN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]
      show Num.decodeLE _ = _
      rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE]
      exact Nat.mod_eq_of_lt (by omega))
    post_simp
    all_goals try assumption

/-- 19227 … 19234 (`DeleteItems`, one item): the call appending the item's n octets at e (from sp), the
    writer from sp + 16 (return 826 → 19241). -/
theorem seg_19227 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v e n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (he : e < 18446744073709551616)
    (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat n)
    (s0 : μ.readN sp 8 = Num.encodeLE 8 e) (v16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 19227 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 826 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat e ∧ ω'[9] = UInt64.ofNat n := by
  have r0 := rd8 he s0
  have rv := rd8 hv v16
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hsp, hr, r0, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hn]
    all_goals try (congr 1; omega)

/-- 19241 … 19250 (`DeleteItems`, after an item): the octets left r (from sp + 8) less 24, and ω₅ on to
    the next item's length word; back to 19193 while items are left. -/
theorem seg_19241_more {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp a r : Nat) (hsp : sp + 32 ≤ 4294967296) (ha : a + 24 < 18446744073709551616)
    (hr : 48 ≤ r ∧ r < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat a)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r)
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 19241 ω μ x 19193 ω' μ x 4 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (a + 24) ∧ ω'[6] = ω[6] ∧ ω'[9] = UInt64.ofNat (r - 24) := by
  have r8 := rd8 hr.2 s8
  have hne : ¬ (r + 18446744073709551592) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hrd, r8, hne, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    all_goals try (congr 1; omega)

/-- 19241 … 19253 (`DeleteItems`, after the last item): r = 24, on to the end at 20118. -/
theorem seg_19241_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (hsp : sp + 32 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp)
    (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 24)
    (hrd : ∀ b, sp + 8 ≤ b → b < sp + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 19241 ω μ x 20118 ω' μ x 5 ∧ ω'[1] = ω[1] := by
  have r8 := rd8 (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hrd, r8, ↓rdN_fold]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Encode.Enc
