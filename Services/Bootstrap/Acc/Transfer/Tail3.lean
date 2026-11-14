import Services.Bootstrap.Acc.Transfer.LogS

/-!
# `on_transfer`'s log line (7454 … 7763), frame-only

After `from_utf8` (`Utf8Call`) has left its tag at sp + 744:
- 7454 (`lg_ok`, `lg_err`): the tag parked at sp + 248; `Ok` builds `String { 128, ptr, 128 }` (the
  memo's copy) at sp + 1576 and the size 3 at sp + 240, `Err` the pair (ptr, 128) at sp + 1576 and the
  size 128 at sp + 240; then `alloc(3, 1)` (return 258, to 7544);
- 7544: null traps at 15362 (`lg_null`); else (`lg_pick_ok`, `lg_pick_err`) a 3-octet `String` at
  sp + 744, the one shown (the memo for `Ok`, the 3 octets for `Err`) moved to sp + 512, and the other
  block freed (return 260, to 7631);
- 7631 (`lg_fmt_pre`): the three arguments (source, amount, the shown `String`) and `format_inner`
  of the template at 66221 into sp + 744 (return 262, to 7699);
- 7699 (`lg_sfree`): the shown `String` freed (return 264, to 7720); 7720 … 7741 (`lg_log_a`) and
  `log` (`FreeStepsH.logS`); 7743 (`lg_log_b`): the message freed (return 266, to 7763).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7454 … 40494**, `from_utf8` gave `Ok` (tag 0): the tag at sp + 248, 3 at sp + 240, the memo's
    `String { 128, ptr, 128 }` at sp + 1576 (ptr = ω₆), −1 at sp + 1568, and `alloc(3, 1)` (return 258). -/
theorem lg_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat ptr)
    (hp : ptr < 18446744073709551616)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (m : rdN μ (sp + 744) 8 = 0) :
    ∃ ω' μ', FreeStepsH p R 7454 ω μ x 40494 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 258 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat 3 ∧
      ω'[8] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat 128 ∧ ω'[6] = UInt64.ofNat ptr ∧
      rdN μ' (sp + 248) 8 = 0 ∧ rdN μ' (sp + 240) 8 = 3 ∧ rdN μ' (sp + 1576) 8 = 128 ∧
      rdN μ' (sp + 1584) 8 = ptr ∧ rdN μ' (sp + 1592) 8 = 128 ∧
      (∀ a, a < 4294967296 → (a < sp + 240 ∨ sp + 256 ≤ a) → (a < sp + 1568 ∨ sp + 1600 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, hwf, hr, m, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val,
      (by reg_val <;> exact h6), ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip

/-- **7454 … 40494**, `from_utf8` gave `Err` (tag 1): the tag at sp + 248, 128 at sp + 240, the pair
    (ptr, 128) at sp + 1576 (ptr = ω₆), ω₅ = ptr, and `alloc(3, 1)` (return 258). -/
theorem lg_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat ptr)
    (hp : ptr < 18446744073709551616)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (m : rdN μ (sp + 744) 8 = 1) :
    ∃ ω' μ', FreeStepsH p R 7454 ω μ x 40494 ω' μ' x 21 ∧
      ω'[0] = UInt64.ofNat 258 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat 3 ∧
      ω'[8] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat ptr ∧
      rdN μ' (sp + 248) 8 = 1 ∧ rdN μ' (sp + 240) 8 = 128 ∧
      (∀ a, a < 4294967296 → (a < sp + 240 ∨ sp + 256 ≤ a) → (a < sp + 1568 ∨ sp + 1608 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, hwf, hr, m, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, (by reg_val <;> exact h6),
      ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip

/-- `alloc`'s return (40611) to 7544 (ω₀ = 258). -/
theorem lg_j258 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 258) : FreeStepsH p R 40611 ω μ x 7544 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **7544 … 15362**, `alloc(3)` returned null: the allocation-failure trap. -/
theorem lg_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) : ∃ ω', FreeStepsH p R 7544 ω μ x 15362 ω' μ x 3 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

/-- **7544 … 40613**, `Ok` (tag 0 at sp + 248), the block p3 ≠ 0: 3 octets written at p3, the
    `String { 3, p3, 3 }` at sp + 744, the memo's `String` (from sp + 1576) moved to sp + 512, and
    `dealloc(p3, 3)` (return 260). -/
theorem lg_pick_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp p3 a b c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat p3)
    (hp0 : p3 ≠ 0) (hp : 65536 ≤ p3 ∧ p3 + 3 ≤ sp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (hw3 : ∀ a, p3 ≤ a → a < p3 + 3 → μ.writable a = true)
    (m248 : rdN μ (sp + 248) 8 = 0) (m240 : rdN μ (sp + 240) 8 = 3)
    (m1576 : rdN μ (sp + 1576) 8 = a) (m1584 : rdN μ (sp + 1584) 8 = b) (m1592 : rdN μ (sp + 1592) 8 = c) :
    ∃ ω' μ', FreeStepsH p R 7544 ω μ x 40613 ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat 260 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat p3 ∧
      ω'[8] = UInt64.ofNat 3 ∧
      rdN μ' (sp + 512) 8 = a ∧ rdN μ' (sp + 520) 8 = b ∧ rdN μ' (sp + 528) 8 = c ∧
      rdN μ' (sp + 744) 8 = 3 ∧ rdN μ' (sp + 752) 8 = p3 ∧ rdN μ' (sp + 760) 8 = 3 ∧
      (∀ a, a < 4294967296 → (a < p3 ∨ p3 + 3 ≤ a) → (a < sp + 512 ∨ sp + 536 ≤ a) →
        (a < sp + 744 ∨ sp + 768 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hr3 : ∀ a, p3 ≤ a → a < p3 + 3 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw3 a h1 h2)
  have hp0' : p3 % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  have la := m1576 ▸ rdN_lt64 μ (sp + 1576)
  have lb := m1584 ▸ rdN_lt64 μ (sp + 1584)
  have lc := m1592 ▸ rdN_lt64 μ (sp + 1592)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, hp0', hwf, hr, hw3, hr3, m248, m240, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip
    · rw [show Num.decodeLE (μ.readN (sp + 1576) 8) = a from m1576]; exact Nat.mod_eq_of_lt la
    · rw [show sp + 1576 + 8 = sp + 1584 by omega, show Num.decodeLE (μ.readN (sp + 1584) 8) = b from m1584,
        Nat.mod_eq_of_lt lb]; exact Nat.mod_eq_of_lt lb
    · rw [show sp + 1576 + 16 = sp + 1592 by omega, show Num.decodeLE (μ.readN (sp + 1592) 8) = c from m1592,
        Nat.mod_eq_of_lt lc]; exact Nat.mod_eq_of_lt lc

end Services.Bootstrap.Acc
