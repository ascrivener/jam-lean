import Services.Bootstrap.Fmt.Tac
import Services.Bootstrap.Fmt.DebugListSteps

/-!
# The field formatters of refine's 6159 `Debug` line: the steps

With plain options (the word 0x60000020 at F + 16: neither `{:x?}` nor `{:X?}`, no width or
precision):

- `f_u32`: `<u32 as Debug>::fmt` (28822) is jumped on to `<u32 as Display>::fmt` (68146), the
  value's address a (ω₇) and F (ω₈) kept;
- `f_u64`: `<u64 as Debug>::fmt` (28843), on to `<u64 as Display>::fmt` (68449);
- `rf_u32`: `<&u32 as Debug>::fmt` (37549): the slot at v is followed, on to 68146;
- `rf_bool`: `<&bool as Debug>::fmt` (37522): the slot at v is followed to the octet b at a;
  `<bool as Display>::fmt` (65017) picks `"false"` (72794, 5 octets) for b = 0, else `"true"`
  (72799, 4 octets), on to `Formatter::pad` (64029);
- `pad_str`: `Formatter::pad` with plain options goes straight to the sink's `write_str` (the word
  at 77040, 2596 → 59959) with the `String` W (the word at F).

ω₀, ω₁, ω₅, ω₆ are kept (64029 saves and restores ω₀, ω₅, ω₆ in sp − 24 … sp).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `<u32 as Debug>::fmt` (28822), plain options: on to `<u32 as Display>::fmt` (68146). -/
theorem f_u32 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : F + 24 < 4294967296) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28822 ω μ x 68146 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧
      ω'[8] = UInt64.ofNat F := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h8, hF, ro, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

/-- `<u64 as Debug>::fmt` (28843), plain options: on to `<u64 as Display>::fmt` (68449). -/
theorem f_u64 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : F + 24 < 4294967296) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28843 ω μ x 68449 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧
      ω'[8] = UInt64.ofNat F := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h8, hF, ro, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

/-- `<&u32 as Debug>::fmt` (37549), plain options: on to `<u32 as Display>::fmt` (68146) with the
    value's address a. -/
theorem rf_u32 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F a : Nat) (hv : v + 8 < 4294967296 ∧ F + 24 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (ra : rdN μ v 8 = a)
    (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 37549 ω μ x 68146 ω' μ x 7 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat a ∧
      ω'[8] = UInt64.ofNat F := by
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ v
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ro, ra, hrF, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

/-- `<&bool as Debug>::fmt` (37522 … 37524, then `<bool as Display>::fmt` 65017 … 65043), plain
    options: the octet b at a (the slot v's word) picks `"false"` (72794, 5 octets) or `"true"`
    (72799, 4 octets); on to `Formatter::pad` (64029) with F (ω₇), the name (ω₈) and its length
    (ω₉). Memory is not written. -/
theorem rf_bool {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F a b : Nat) (hv : v + 8 < 4294967296 ∧ a + 1 < 4294967296 ∧ F < 18446744073709551616)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ra : rdN μ v 8 = a) (rb : rdN μ a 1 = b)
    (hrv : ∀ c, v ≤ c → c < v + 8 → μ.readable c = true)
    (hra : ∀ c, a ≤ c → c < a + 1 → μ.readable c = true) :
    ∃ ω', FreeStepsH p R 37522 ω μ x 64029 ω' μ x 8 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat (if b = 0 then 72794 else 72799) ∧ ω'[9] = UInt64.ofNat (if b = 0 then 5 else 4) := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hb : b = 0
  · subst hb
    simp only [ite_true]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h7, h8, hv, ra, rb, hrv, hra, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hv.2.2]
  · have hbm : b % 18446744073709551616 = b := Nat.mod_eq_of_lt (by
      have := rdN_lt μ a 1; rw [rb] at this; simp at this; omega)
    simp only [hb, ite_false]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h7, h8, hv, ra, rb, hb, hbm, hrv, hra, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hv.2.2]

/-- `Formatter::pad` (64029 … 64054, 64404 … 64427) with plain options (no width or precision:
    the word 0x60000020 at F + 16): on to the sink's `write_str` (the word at 77040, 2596 → 59959)
    with the `String` W (the word at F), the text s (ω₈) and its length n (ω₉). Only sp − 24 … sp
    is written (ω₀, ω₅, ω₆ saved and restored). -/
theorem pad_str {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F W r0 v5 v6 src n : Nat) (hsp : 196608 + 24 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      F + 24 < 4294967296 ∧ src < 18446744073709551616 ∧ n < 18446744073709551616)
    (hF : F + 24 ≤ sp - 24 ∨ sp ≤ F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (ro : rdN μ (F + 16) 4 = 1610612768)
    (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ c, 65536 ≤ c → c < 77144 → μ.readable c = true)
    (hrF : ∀ c, F ≤ c → c < F + 24 → μ.readable c = true)
    (hw : ∀ c, sp - 24 ≤ c → c < sp → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 64029 ω μ x 59959 ω' μ' x 19 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat n ∧
      (∀ c, c < 4294967296 → (c < sp - 24 ∨ sp ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp - 24 ≤ c → c < sp → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hv, hF, rW, rvt, ro, rws, hro, hrF, hw, hr, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    · rw [rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt hv.1]
    · rw [rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt hv.2.1]
    · rw [rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt hv.2.2.1]
    · simp only [List.lookup_nil, Option.getD_none]; exact h9
    · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega),
        Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega),
        Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    · simp only [Memory.readable_writeN]
    · simp only [Memory.writable_writeN]

end Services.Bootstrap.Fmt
