import Services.Bootstrap.Fmt.Tac

/-!
# `<Option<Vec<u8>> as fmt::Debug>::fmt` (17465): the steps

The `Option` at v (ω₇) is `None` when its first word (the `Vec`'s capacity, a niche) is 2⁶⁴ − 1.

`os_some`: from v and the `Formatter` F (ω₈), the frame T = sp − 16 holds ω₀ at T + 8 and v (the
`Vec`'s address) at T + 0; `debug_tuple_field1_finish` (62471) is called with F, the name `"Some"`
(66797, 4 octets), T and the field's `Debug` vtable 74648 (`&Vec<u8>`), returning to 17507 (670).
The return from there is `rd_r`.

`os_none` (17465 … 17523, then `Formatter::write_str`, 64485 … 64493): `"None"` (66801, 4 octets)
to the sink's `write_str` (the word at 77040, 2596 → 59959) with the `String` W (the word at F).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem os_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 16 < 4294967296)
    (hdis : v + 8 ≤ sp - 16 ∨ sp ≤ v) (rt : rdN μ v 8 ≠ 18446744073709551615)
    (hrv : ∀ a, v ≤ a → a < v + 8 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 17465 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 670 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 66797 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 74648 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = v ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rt' : rdN μ v 8 % 18446744073709551616 ≠ 18446744073709551615 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 μ v)]; exact rt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, rt, rt', hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega)]

theorem os_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F W : Nat) (hv : v + 8 < 4294967296 ∧ F + 16 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (rt : rdN μ v 8 = 18446744073709551615)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 17465 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 66801 ∧ ω'[9] = UInt64.ofNat 4 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, rt, rW, rvt, rws, hro, hrv, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hW, rW]

end Services.Bootstrap.Fmt
