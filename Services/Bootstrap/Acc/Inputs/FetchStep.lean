import Services.Bootstrap.Acc.Contract

/-!
# `fetch` of the accumulate inputs (kind 14) under the accumulate contract

Ω_Y (GP v0.8.0 Appendix B, `fetch` = 2) with ω₁₀ = 14 returns the inputs ℰ(↕**i**) (eq. `fetch`,
`accInputs`): it charges 287 + 𝔊(400, ω₉) (`Constants.CgasY`), writes the slice
v[f … f + l] at ω₇ (f = min(ω₈, |v|), l = min(ω₉, |v| − f)) if those octets are writable, and sets
ω₇ = |v|. `fetch14_step` is that step under `accContractK cap env` for a cost within `cap`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- ℰ(↕**i**): the inputs as Ψ_A's `fetch` returns them for kind 14. -/
def inputsEnc (env : AccEnv) : List UInt8 := Codec.varSeq AccumulateInput.encode env.inputs

/-- **One `fetch` of kind 14** under `accContractK cap env`: with ω₇ = o, ω₈ = f, ω₉ = z and
    ω₁₀ = 14, a cost 287 + 𝔊(400, z) within `cap` and the target octets writable, the call continues
    with ω₇ = |ℰ(↕**i**)| and the slice written at o. -/
theorem fetch14_step (cap : Nat) (hcap : cap < 2 ^ 64) (env : AccEnv) (ω : Regs) (μ : Memory)
    (x : AccCtx) (o f z : Nat) (h7 : reg ω 7 = o) (h8 : reg ω 8 = f) (h9 : reg ω 9 = z)
    (h10 : reg ω 10 = 14) (hcost : 287 + memGas 400 z ≤ cap)
    (hw : μ.rangeWritable o (min z ((inputsEnc env).length - min f (inputsEnc env).length)) = true) :
    accContractK cap env 2 ω μ x .cont (setR7 ω (inputsEnc env).length)
      (μ.writeN o (((inputsEnc env).drop (min f (inputsEnc env).length)).take
        (min z ((inputsEnc env).length - min f (inputsEnc env).length)))) x := by
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  have hc : (UInt64.ofNat cap).toNat = cap := UInt64.toNat_ofNat_of_lt' hcap
  simp only [accHostFn, AccHost.dispatch, hostFetch, charged, h9, h10, hc]
  simp only [show (14 < 16) = True from by decide, ite_true, Constants.CgasY]
  rw [if_neg (by omega)]
  simp only [writeValue, fetchValue, h7, h8, Option.map_some]
  simp only [inputsEnc] at hw ⊢
  simp [hw]

/-- `rangeWritable` from writability octet by octet (writability is per page). -/
theorem rangeWritable_of {μ : Memory} {o l : Nat} (hol : o + l ≤ 2 ^ 32)
    (h : ∀ a, o ≤ a → a < o + l → μ.writable a = true) : μ.rangeWritable o l = true := by
  unfold Memory.rangeWritable
  by_cases hl : l = 0
  · simp [hl]
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  right
  refine ⟨hol, fun k hk => ?_⟩
  have hps : pageSize = 4096 := rfl
  rw [hps] at hk ⊢
  -- the page (o / 4096 + k) holds an octet of the range: its start, or o itself
  have ha := h (max o ((o / 4096 + k) * 4096)) (by omega) (by
    have := Nat.div_mul_le_self o 4096
    have := Nat.lt_div_mul_add (a := o + l - 1) (b := 4096) (by decide)
    have : (o + l - 1) / 4096 * 4096 ≤ o + l - 1 := Nat.div_mul_le_self _ _
    omega)
  unfold Memory.writable at ha ⊢
  rw [hps] at ha
  have e : max o ((o / 4096 + k) * 4096) / 4096 = (o / 4096 + k) * 4096 / 4096 := by
    rw [Nat.mul_div_cancel _ (by decide)]
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.add_zero]
      rw [Nat.max_def]; split
      · rw [Nat.mul_div_cancel _ (by decide)]
      · rfl
    · rw [Nat.max_eq_right (by have := Nat.lt_div_mul_add (a := o) (b := 4096) (by decide); omega),
        Nat.mul_div_cancel _ (by decide)]
  rw [e] at ha
  exact ha

end Services.Bootstrap.Acc
