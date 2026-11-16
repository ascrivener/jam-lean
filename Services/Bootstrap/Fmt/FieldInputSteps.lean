import Services.Bootstrap.Fmt.Tac

/-!
# `<&Input as Debug>::fmt` (36972): the steps

`in36_a` (36972 … 37047): with the slot v (ω₇) holding the struct's address a and the `Formatter` F
(ω₈), a 72-octet frame T = sp − 72 holds ω₀, ω₅, ω₆ at T + 64, T + 56, T + 48 and a + 8 (the
`nb_items` octet's address) at T + 40; `debug_struct_field2_finish` (62972) is called with the name
`"Input"` (68712, 5), field 1 `"seed"` (68729, 4) by its address a with the vtable 76008 (`u64`,
at T), field 2 `"nb_items"` (68741, 8) through the slot T + 40 with the vtable 75976 (`&u8`)
(T + 8 … T + 32), returning to 37053 (1752). `in36_r` (37053 … 37065): the return.

`f_u64b` (37857 … 37874): `<u64 as Debug>::fmt` at 37857, the same code as 28843 (`f_u64`).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem in36_a1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 72 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 9 < 4294967296)
    (ra : rdN μ v 8 = a) (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hdv : sp ≤ v)
    (hw : ∀ b, sp - 72 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 36972 ω μ x 36994 ω' μ' x 8 ∧
      ω'[1] = UInt64.ofNat (sp - 72) ∧ ω'[2] = UInt64.ofNat F ∧ ω'[12] = UInt64.ofNat a ∧
      rdN μ' (sp - 72 + 64) 8 = r0 ∧ rdN μ' (sp - 72 + 56) 8 = v5 ∧ rdN μ' (sp - 72 + 48) 8 = v6 ∧
      rdN μ' (sp - 72 + 40) 8 = a + 8 ∧
      (∀ b, b < 4294967296 → (b < sp - 72 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 72 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have ha : a < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdv, ra, hrv, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, h0, h1, h5, h6, h7, h8, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show a + 8 < 18446744073709551616 by omega)]

theorem in36_a2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T a F : Nat) (hT : 196608 ≤ T ∧ T + 72 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h2 : ω[2] = UInt64.ofNat F) (h12 : ω[12] = UInt64.ofNat a)
    (hv : F < 18446744073709551616 ∧ a < 18446744073709551616)
    (hw : ∀ b, T ≤ b → b < T + 40 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 36994 ω μ x 62972 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 1752 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat 68741 ∧
      ω'[6] = UInt64.ofNat 76008 ∧ ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68712 ∧
      ω'[9] = UInt64.ofNat 5 ∧ ω'[10] = UInt64.ofNat 68729 ∧ ω'[11] = UInt64.ofNat 4 ∧
      ω'[12] = UInt64.ofNat a ∧
      rdN μ' (T + 32) 8 = 75976 ∧ rdN μ' (T + 24) 8 = T + 40 ∧ rdN μ' (T + 16) 8 = 8 ∧
      rdN μ' (T + 8) 8 = 68741 ∧ rdN μ' T 8 = 76008 ∧
      (∀ b, b < 4294967296 → (b < T ∨ T + 40 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, T ≤ b → b < T + 40 → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h2, h12, hT, hv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_,
      fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, h1, h2, h12, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2,
      Nat.mod_eq_of_lt (show T < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show T + 40 < 18446744073709551616 by omega)]

theorem in36_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 v5 v6 t : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (r0' : rdN μ (T + 64) 8 = r0) (r5 : rdN μ (T + 56) 8 = v5)
    (r6 : rdN μ (T + 48) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 72 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 37053 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 72) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  have hv5 : v5 < 18446744073709551616 := r5 ▸ rdN_lt64 μ _
  have hv6 : v6 < 18446744073709551616 := r6 ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, r5, r6, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt hv5, Nat.mod_eq_of_lt hv6]

theorem f_u64b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : F + 24 < 4294967296) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 37857 ω μ x 68449 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧
      ω'[8] = UInt64.ofNat F := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h8, hF, ro, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

end Services.Bootstrap.Fmt
