import Services.Bootstrap.Acc.HostSteps
import Services.Bootstrap.Fmt.Tac
import Services.Bootstrap.CodeAAll

/-!
# Accumulate's first log line after `format!`: the `log` call (6608) and the `String`'s dealloc

- `FreeStepsH.logAcc`: the `log` (100) host call under `accContractK cap` (cap ≥ 𝖬_∅ = 1000). The
  accumulate dispatcher does not know id 100, so it charges 𝖬_∅ and returns WHAT in ω₇; memory and
  the context are kept (GP v0.8.0 eq. `accinvocation`). The message is not looked at.
- `ls_a`: 6587 … 6606, the `log` arguments from the `String` at sp + 744;
- `ls_b`: 6610 … 6623, a nonzero capacity: the call of `dealloc` (40613), returning to 6630 (224);
- `ls_b0`: 6610 … 6615, capacity 0: no dealloc, on to 6630;
- `ls_ret`: `dealloc`'s return (40697) to 6630.
-/

namespace Services.Bootstrap.Fmt

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Acc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A `log` (100) step** under `accContractK cap` (1000 ≤ cap): ω₇ := WHAT, memory and context kept. -/
theorem FreeStepsH.logAcc (cap : Nat) (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 100) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractK cap env) n (setR7 ω Result.WHAT) μ x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  have hc : ¬ ((cap : Int) - ((1000 : Nat) : Int) < 0) := by omega
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow,
    Constants.Cgasunknown, Nat.mod_eq_of_lt hcap.2, hc, ↓reduceIte]

variable {X : Type} {R : HostRel X}

/-- 6587 … 6606: `log`'s arguments: level 2 (ω₇), the target at 66793 (ω₈, 4 octets, ω₉), the
    message at the `String`'s buffer (ω₁₀ = ω₅ = the word at sp + 752) and length (ω₁₁, at
    sp + 760). -/
theorem ls_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hr : ∀ a, sp + 744 ≤ a → a < sp + 768 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6587 ω μ x 6608 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 752) 8) ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 752))]

/-- 6610 … 6623, the `String`'s capacity (at sp + 744) nonzero: `dealloc(ω₅, 1)` (40613), returning
    to 6630 (224). -/
theorem ls_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q : Nat) (hsp : sp + 768 < 4294967296) (hq : q < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat sp)
    (h5 : ω[5] = UInt64.ofNat q)
    (hcap : rdN μ (sp + 744) 8 ≠ 0) (hr : ∀ a, sp + 744 ≤ a → a < sp + 752 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6610 ω μ x 40613 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 224 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 744)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]

/-- 6610 … 6615, capacity 0: on to 6630. -/
theorem ls_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hcap : rdN μ (sp + 744) 8 = 0) (hr : ∀ a, sp + 744 ≤ a → a < sp + 752 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6610 ω μ x 6630 ω' μ x 3 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 744)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

/-- `dealloc`'s return (40697) to 6630 (224). -/
theorem ls_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 224) : FreeStepsH p R 40697 ω μ x 6630 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Fmt
