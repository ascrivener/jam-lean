import Services.Bootstrap.Acc.Wrappers.Get

/-!
# The SDK's `remove` (48481): a write of nothing

`remove(key)` makes one Ω_W call (`write`, GP v0.8.0 Appendix B) with the key at ω₇ (ω₈ octets) and an
empty value (ω₉ = ω₁₀ = 0), then returns whether a value was removed:
- a reply below 2⁶⁴ − 9 (the old value's length): 1;
- NONE: 0;
- any other reply traps (48533). For this service that is FULL (the threshold after the removal still
  above the balance); `ASem.step .remove` does not panic there (reported, pending).
The frame is 16 octets (s = sp − 16): ω₅, ω₀ at s, + 8.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **48481 … 48493**: the frame s = sp − 16 (ω₀, ω₅ saved at s + 8, + 0), and Ω_W's registers with
    an empty value: the key at ω₇ (ω₈ octets) as at the call, ω₉ = ω₁₀ = 0. -/
theorem rm_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 48481 ω μ x 48493 ω' μ' x 6 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[9] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 0 ∧
      rdN μ' (sp - 16 + 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [1, 9, 10] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **48495 … 48514 / 48531**, Ω_W's reply r: below 2⁶⁴ − 9 (a value was removed) ω₇ = 1, at 48514;
    NONE (there was none) ω₇ = 0, at 48531; ω₀, ω₅ restored and the frame popped, at the return's
    `jumpInd`. -/
theorem rm_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp r r0 r5 : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat r)
    (hr : r < 18446744073709551607 ∨ r = 18446744073709551615)
    (hsp : 65536 ≤ sp ∧ sp + 16 < 4294967296)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 r5) (m8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) :
    ∃ e ω', FreeStepsH p R 48495 ω μ x e ω' μ x 12 ∧
      (r < 18446744073709551607 → e = 48514 ∧ ω'[7] = UInt64.ofNat 1) ∧
      (r = 18446744073709551615 → e = 48531 ∧ ω'[7] = UInt64.ofNat 0) ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 16) ∧ ω'[5] = UInt64.ofNat r5 := by
  have q0 : rdN μ sp 8 = r5 := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5
  have q8 : rdN μ (sp + 8) 8 = r0 := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr0
  rw [show ω = regsNF ω [] from rfl]
  rcases hr with hr | rfl
  · refine ⟨48514, ?ω', ?run, fun _ => ⟨rfl, ?a⟩, fun h => absurd h (by omega), ?b, ?c, ?d⟩
    case run => pvm_go [h1, h7, q0, q8, hrf, ↓rdN_fold, Nat.mod_eq_of_lt (show r < 18446744073709551616 by omega)]
    all_goals reg_val
  · refine ⟨48531, ?ω2, ?run2, fun h => absurd h (by omega), fun _ => ⟨rfl, ?a2⟩, ?b2, ?c2, ?d2⟩
    case run2 => pvm_go [h1, h7, q0, q8, hrf, ↓rdN_fold]
    all_goals reg_val

end Services.Bootstrap.Acc
