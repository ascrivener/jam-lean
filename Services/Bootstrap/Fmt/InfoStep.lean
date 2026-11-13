import Services.Bootstrap.Acc.HostSteps

/-!
# The `info` (6) host call on the accumulating service, under the accumulate contract

`FreeStepsH.infoSelf`: an `info` call with ω₇ = 2⁶⁴ − 1 (the service itself), offset 0 and length
z, into a writable buffer o, computes Ψ_A's handler (`JAM.accHostFn`, Ω_I of GP v0.8.0) when the
accumulating service's own account a is in the context's accounts: ω'₇ = |infoValue a| and the
first min(z, |infoValue a|) octets of infoValue a at o. The context is kept.
-/

namespace Services.Bootstrap.Fmt

open PVM JAM Services.Bootstrap.Acc

/-- A range of writable octets passes `rangeWritable`'s page check. -/
theorem rangeWritable_of {μ : Memory} {o n : Nat} (hn : o + n ≤ 2 ^ 32)
    (hw : ∀ a, o ≤ a → a < o + n → μ.writable a = true) : μ.rangeWritable o n = true := by
  unfold Memory.rangeWritable
  by_cases h0 : n = 0
  · simp [h0]
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true, decide_eq_true_eq, hn, true_and,
    List.all_eq_true, List.mem_range]
  intro k hk
  have hps : pageSize = 4096 := rfl
  have e : ((o / pageSize + k) * pageSize) / pageSize = (max o ((o / pageSize + k) * pageSize)) / pageSize := by
    rw [hps] at hk ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [Nat.add_zero]
      rw [Nat.max_def]; split <;> omega
    · rw [Nat.max_def]; split <;> omega
  have hw' := hw (max o ((o / pageSize + k) * pageSize)) (Nat.le_max_left _ _) (by
    rw [hps] at hk ⊢; rw [Nat.max_def]; split <;> omega)
  unfold Memory.writable at hw' ⊢
  rw [e]; exact hw'

/-- **An `info` step on the service itself** under `accContractK cap` (cap ≥ 𝖬_I = 703): with the
    accumulating service's account a in the context's accounts, ω₇ = 2⁶⁴ − 1, ω₈ = o, ω₉ = 0,
    ω₁₀ = z and o … o + min(z, |infoValue a|) writable, the call continues with
    ω'₇ = |infoValue a|, the first min(z, |infoValue a|) octets of infoValue a at o, and the
    context unchanged. -/
theorem FreeStepsH.infoSelf (cap : Nat) (hcap : 703 ≤ cap ∧ cap < 2 ^ 64) (env : AccEnv)
    {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {a : ServiceAccount}
    {o z : Nat} {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtx} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 6) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (ha : x.1.state.accounts.get? x.1.id = some a)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) (h8 : ω[8] = UInt64.ofNat o)
    (h9 : ω[9] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat z) (ho : o + z ≤ 2 ^ 32)
    (hw : ∀ b, o ≤ b → b < o + z → μ.writable b = true)
    (rest : FreeStepsH p (accContractK cap env) n (setR7 ω (infoValue a).length)
      (μ.writeN o ((infoValue a).take (min z (infoValue a).length))) x i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractK cap env) i ω μ x i'' ω'' μ'' x'' (k + 1) := by
  apply FreeStepsH.host_decode hd _ rest
  have hrw : μ.rangeWritable o (min z (infoValue a).length) = true :=
    rangeWritable_of (by omega) (fun b h1 h2 => hw b h1 (by omega))
  have r7 : reg ω 7 = 2 ^ 64 - 1 := by simp [reg, Regs.get, Fin.getElem_fin, h7]
  have r8 : reg ω 8 = o := by simp [reg, Regs.get, Fin.getElem_fin, h8]; omega
  have r9 : reg ω 9 = 0 := by simp [reg, Regs.get, Fin.getElem_fin, h9]
  have r10 : reg ω 10 = z := by simp [reg, Regs.get, Fin.getElem_fin, h10]; omega
  have hc : ¬ (cap % 18446744073709551616 < 703) := by rw [Nat.mod_eq_of_lt hcap.2]; omega
  refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
  simp only [accHostFn, AccHost.dispatch, hostInfo, charged, writeValue, UInt64.toNat_ofNat', Constants.CgasI,
    UInt64.reduceToNat, Nat.reducePow, hc, ↓reduceIte, r7, r8, r9, r10, ha, Option.map_some, Nat.zero_min,
    Nat.sub_zero, List.drop_zero, hrw, Bool.not_true, Bool.false_eq_true]

end Services.Bootstrap.Fmt
