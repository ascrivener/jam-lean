import Services.Bootstrap.Fmt.Tac

/-!
# `<Result<u64, HostCallError> as fmt::Debug>::fmt` (17779), and `<&HostCallError as Debug>` (37312):
the steps

`rd_ok` / `rd_err`: from the `Result` at v (ω₇; its tag octet at v) and the `Formatter` F (ω₈): the
frame T = sp − 16 holds ω₀ at T + 8 and the field's address at T + 0 (v + 8 for `Ok`, v + 1 for
`Err`); `debug_tuple_field1_finish` (62471) is called with F, the name (`"Ok"` at 67359 or `"Err"`
at 67361), T and the field's `Debug` vtable (74040: `&u64`; 74776: `&HostCallError`), returning to
17856 (696) or 17821 (694). `rd_r`: the return (also from 17507, `Option`'s `Debug`).

`he_a` (37312 … 37349): the error's name, from the tables at 68944 (lengths) and 69008 (offsets),
to `Formatter::write_str` (64485), whose jump through the sink's vtable reaches 59959 (`he_b`).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem rd_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 16 < 4294967296)
    (hdis : v + 1 ≤ sp - 16 ∨ sp ≤ v) (rt : rdN μ v 1 = 0)
    (hrv : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17779 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 696 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 67359 ∧ ω'[9] = UInt64.ofNat 2 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 74040 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = v + 8 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, rt, hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt (show v + 8 < 18446744073709551616 by omega)]

theorem rd_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 16 < 4294967296)
    (hdis : v + 1 ≤ sp - 16 ∨ sp ≤ v) (rt : rdN μ v 1 ≠ 0)
    (hrv : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17779 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 694 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 67361 ∧ ω'[9] = UInt64.ofNat 3 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 74776 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = v + 1 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rt' : rdN μ v 1 % 18446744073709551616 ≠ 0 := by
    have := rdN_lt μ v 1; rw [Nat.mod_eq_of_lt (by simp at this; omega)]; exact rt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, rt, rt', hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt (show v + 1 < 18446744073709551616 by omega)]

theorem rd_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t i : Nat) (hi : i = 17856 ∨ i = 17821 ∨ i = 17507) (hT : 65536 ≤ T ∧ T + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (r0' : rdN μ (T + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hT, r0', hret, hjt, hbt, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

/-- 37312 … 37349, then `Formatter::write_str` (64485 … 64493): `<&HostCallError as Debug>::fmt`
    with the slot v (ω₇) holding the error's address a and the `Formatter` F (ω₈): the error's tag t
    at a; its name's length L (the word at 68944 + 8t) and offset (the i32 u at 69008 + 4t, negative:
    the name at nm = 69008 + u − 2³²); on to the sink's `write_str` (the word at 77040, 2596 → 59959)
    with the `String` W (the word at F), nm and L. ω₀, ω₁, ω₅, ω₆ are kept. -/
theorem he_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F W a t L u nm : Nat) (hv : v + 8 < 4294967296 ∧ F + 16 < 4294967296 ∧ a + 1 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 1 = t) (ht : t < 8)
    (rL : rdN μ (68944 + 8 * t) 8 = L) (ru : rdN μ (69008 + 4 * t) 4 = u)
    (hu : 2147483648 ≤ u ∧ u + 69008 = nm + 4294967296)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hra : ∀ b, a ≤ b → b < a + 1 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 37312 ω μ x 59959 ω' μ x 18 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat nm ∧ ω'[9] = UInt64.ofNat L := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  have hL : L < 18446744073709551616 := rL ▸ rdN_lt64 μ _
  have hu4 : u < 4294967296 := by have := rdN_lt μ (69008 + 4 * t) 4; simp at this; omega
  have ru' : rdN μ (t * 4 + 69008) 4 = u := by rw [show t * 4 + 69008 = 69008 + 4 * t by omega]; exact ru
  have rL' : rdN μ (t * 8 + 68944) 8 = L := by rw [show t * 8 + 68944 = 68944 + 8 * t by omega]; exact rL
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ra, rt, ht, rL, ru, rL', ru', hu, hu4, rW, rvt, rws, hro, hrv, hra, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 5
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      exact congrArg UInt64.ofNat (by omega)
    all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hL, rW, rL,
      show 68944 + t * 8 = 68944 + 8 * t by omega]

end Services.Bootstrap.Fmt
