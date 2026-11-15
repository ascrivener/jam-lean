import Services.Bootstrap.Encode.EncMD

/-!
# `Instruction::encode_to`: the straight-line pieces of `CreateService` (dispatch index 0)

`CreateService` is the enum's dataful variant: its first word is its `Option<Vec<u8>>`'s capacity (the
`None` niche 2^64 − 1, or a `Vec`'s capacity below 2^63), not one of the niche words 2^63 … 2^63 + 23,
so the dispatch (30145) takes index 0 (`dispatch0`), the arm 17905, with ω₅ = 2^64 − 1 and ω₆ the first
word. The arm (17905 … 18135, 20218 … 20322) appends, in order (GP v0.8.0 Appendix C, field by field):
the tag 0; the 32-octet hash at S + 32; the four `u64`s at S + 64, 72, 80, 88 (each through the scratch
word sp + 24); the 128-octet array at S + 96; the `Option<Vec<u8>>` (ω₆ = ω₅: [0]; otherwise 1, the
length prefix ℰ(n) of the length n (S + 16; a trap at 20397 for n ≥ 2^32) and the n octets at the
pointer (S + 8)); the `u64` at S + 224; and the `Option<u32>` (its tag word at S + 24 as an `i32`: 0
gives [0], otherwise 1 and the 4 octets at S + 28), ending at 20329. S is kept at sp throughout.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- The signed comparison at 30184 fails for a first word D below 2^63 or equal to 2^64 − 1. -/
theorem signed_not_niche (D : Nat) (hD : D < 9223372036854775808 ∨ D = 18446744073709551615) :
    ¬ (Num.signed 8 D < Num.signed 8 9223372036854775832) := by
  have hc : Num.signed 8 9223372036854775832 = -9223372036854775784 := by decide
  rw [hc]
  rcases hD with hD | rfl
  · have : Num.signed 8 D = (D : Int) := by unfold Num.signed; simp [hD]
    rw [this]; omega
  · decide

/-- **The dispatch to index 0** (`CreateService`): from 30145 with the value at S (ω₇) whose first word
    D is below 2^63 or is 2^64 − 1, the function opens its frame at F − 56, saves ω₀, ω₅, ω₆ and v there
    and reaches the arm 17905, with ω₁ = F − 56, ω₅ = 2^64 − 1, ω₆ = D, ω₁₀ = v and ω₁₁ = S. -/
theorem dispatch0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F S v ret r5 r6 D : Nat) (hDn : D < 9223372036854775808 ∨ D = 18446744073709551615)
    (hF : 67476 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat S) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616)
    (hS : S + 8 ≤ 4294967296) (hSF : S + 8 ≤ F - 56 ∨ F ≤ S)
    (hD : μ.readN S 8 = Num.encodeLE 8 D)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (hrS : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x 17905 ω' μ' x 24 ∧
      ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[5] = UInt64.ofNat 18446744073709551615 ∧ ω'[6] = UInt64.ofNat D ∧
      ω'[10] = UInt64.ofNat v ∧ ω'[11] = UInt64.ofNat S ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧ μ'.readN (F - 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hD64 : D < 18446744073709551616 := by omega
  have rD := rd8 hD64 hD
  have hrt' : ∀ a, 67376 ≤ a → a < 67376 + 4 → μ.readable a = true :=
    fun a h1 h2 => hrt a (by omega) (by omega)
  have rt : rdN μ 67376 4 = 4294900622 := by
    show Num.decodeLE (μ.readN _ 4) = _
    rw [show (67376 : Nat) = 67376 + 4 * 0 from rfl, table_entry tab 0 (by omega)]
    exact table_val 0 (by omega)
  have hsx : sxw 4 4294900622 = 18446744073709484942 := sxw_table 0 (by decide)
  have hlt := signed_not_niche D hDn
  have hlt' : (decide (Num.signed 8 D < Num.signed 8 9223372036854775832)) = false := by simp [hlt]
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hF, hS, hSF, hw, hr, hrS, rD, rt, hrt', hsx, hlt, hlt', rdN_writeN_disjoint,
      ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
      show F - 56 + 32 = F - 24 by omega, show F - 56 + 16 = F - 40 by omega]
    post_simp
    all_goals try assumption

end Services.Bootstrap.Encode.Enc
