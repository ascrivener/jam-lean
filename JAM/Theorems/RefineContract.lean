import JAM.Refine
import JAM.Theorems.HostGas
import PVM.Logic.Det
import PVM.Logic.StepsH
import PVM.Logic.GasBound

/-!
# A contract for the refine dispatcher that pins down its outcomes

`FreeRunH` and `FreeStepsH` abstract gas away, so the handler a proof steps through is a contract:
which outcomes a host call may have. For the lift to Ψ_M (`PVM.psiM_of_freeRunH`) the contract
must *pin down* the real handler: whatever non-∞ outcome the handler produces, for whatever gas,
must be the one the contract allows.

That holds for host calls whose non-∞ outcome does not depend on the gas left: `grow_heap`,
`fetch` and any id the dispatcher does not know (`log`, for instance). It fails for `gas`, which
reports the gas left. `refineContract` is the dispatcher's graph restricted to those ids, and
`refineContract_pins` proves it pins down the dispatcher.
-/

namespace JAM

open PVM

/-- Two host outcomes that agree except for the gas left. -/
def SameButGas {X : Type} (o₁ o₂ : HostOut X) : Prop :=
  o₁.status = o₂.status ∧ o₁.regs = o₂.regs ∧ o₁.mem = o₂.mem ∧ o₁.ctx = o₂.ctx

/-- The common rules: if the body's outcome does not depend on the gas it is handed and is never
    ∞, the charged function's non-∞ outcomes do not depend on the gas. -/
theorem charged_sameButGas {X : Type} (g : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X)
    (hb : ∀ a b, SameButGas (body ⟨.cont, a, ω, μ, x⟩) (body ⟨.cont, b, ω, μ, x⟩))
    {gas₁ gas₂ : Nat} (h₁ : (charged g gas₁ ω μ x body).status ≠ .oog)
    (h₂ : (charged g gas₂ ω μ x body).status ≠ .oog) :
    SameButGas (charged g gas₁ ω μ x body) (charged g gas₂ ω μ x body) := by
  unfold charged at *
  split at h₁
  · exact absurd rfl h₁
  · split at h₂
    · exact absurd rfl h₂
    · simp only [*]
      exact hb _ _

theorem writeValue_sameButGas {X : Type} (s : HostStatus) (a b : Int) (ω : Regs) (μ : Memory)
    (x : X) (v : Except Unit (Option (List UInt8))) (o f z : Nat) :
    SameButGas (writeValue ⟨s, a, ω, μ, x⟩ v o f z) (writeValue ⟨s, b, ω, μ, x⟩ v o f z) := by
  unfold writeValue SameButGas
  dsimp only
  repeat' split
  all_goals simp

/-- The host-call ids whose non-∞ outcome does not depend on the gas: `grow_heap` (1), `fetch` (2),
    `historical_lookup` (7, Ω_H), `export` (8, Ω_E), and the ids the refine dispatcher does not know
    (3 … 6 and above 14). -/
def GasFreeId (h : Nat) : Prop := h = 1 ∨ h = 2 ∨ (3 ≤ h ∧ h ≤ 8) ∨ 14 < h


/-- The protocol parameters always encode to 122 octets (`fetch` case 0). -/
@[simp] theorem Params.encode_length (c : Params) : c.encode.length = 122 := by
  unfold Params.encode
  simp only [Codec.fixed, List.length_append, PVM.Num.length_encodeLE]

/-- ℰ of the Gray Paper's full-chain parameters, as `fetch` case 0 returns them (GP Appendix B,
    Ω_Y; the constants of `JAM.Constants`). -/
theorem Params.full_encode : Params.full.encode = [10, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 85, 1, 0, 75, 0, 0, 88, 2, 0, 0, 128, 150, 152, 0, 0, 0, 0, 0, 128, 240, 250, 2, 0, 0, 0, 0, 0, 242, 5, 42, 1, 0, 0, 0, 0, 195, 157, 208, 0, 0, 0, 0, 8, 0, 16, 0, 8, 0, 16, 0, 64, 56, 0, 0, 8, 0, 6, 0, 80, 0, 10, 0, 128, 0, 5, 0, 0, 250, 0, 0, 128, 112, 210, 0, 0, 9, 61, 0, 0, 12, 0, 0, 0, 192, 0, 0, 128, 0, 0, 0, 0, 12, 0, 0, 244, 1, 0, 0] := by
  decide

namespace RefineHost

theorem dispatch_sameButGas (env : Env) {h : Nat} (hh : GasFreeId h) (ω : Regs) (μ : Memory)
    (c : RefineCtx) {gas₁ gas₂ : Nat} (h₁ : (dispatch env h gas₁ ω μ c).status ≠ .oog)
    (h₂ : (dispatch env h gas₂ ω μ c).status ≠ .oog) :
    SameButGas (dispatch env h gas₁ ω μ c) (dispatch env h gas₂ ω μ c) := by
  rcases hh with rfl | rfl | ⟨h3, h8⟩ | hlt
  · -- grow_heap
    simp only [dispatch] at *
    unfold hostGrowHeap SameButGas at *
    generalize growHeapCore ω μ env.code = q at *
    obtain ⟨a, b, hp, w⟩ := q
    dsimp only at *
    by_cases hc : w ≤ hp ∨ w > b
    · simp [hc]
    · simp only [hc, ↓reduceIte] at h₁ h₂ ⊢
      by_cases g₁ : gas₁ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear <;>
        by_cases g₂ : gas₂ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear <;>
        simp only [g₁, g₂, ↓reduceIte] at h₁ h₂ ⊢ <;> simp_all
  · -- fetch
    simp only [dispatch] at *
    exact charged_sameButGas _ _ _ _ _ (fun a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
  · rcases (show h = 7 ∨ h = 8 ∨ (3 ≤ h ∧ h ≤ 6) by omega) with rfl | rfl | h36
    · -- historical_lookup
      simp only [dispatch] at *
      exact charged_sameButGas _ _ _ _ _
        (fun a b => by dsimp only; exact writeValue_sameButGas _ _ _ _ _ _ _ _ _ _) h₁ h₂
    · -- export
      simp only [dispatch] at *
      refine charged_sameButGas _ _ _ _ _ (fun a b => ?_) h₁ h₂
      dsimp only
      unfold SameButGas
      split
      · simp [panic]
      · split <;> simp [r7]
    · -- an id the dispatcher does not know
      have hu : ∀ g, dispatch env h g ω μ c = unknown g ω μ c := by
        intro g; unfold dispatch; split <;> first | omega | rfl
      simp only [hu] at h₁ h₂ ⊢
      unfold unknown at h₁ h₂ ⊢
      unfold SameButGas
      dsimp only at h₁ h₂ ⊢
      split at h₁ <;> split at h₂ <;> simp_all
      simp only [show ¬((gas₁ : Int) - Constants.Cgasunknown < 0) by omega,
        show ¬((gas₂ : Int) - Constants.Cgasunknown < 0) by omega, ↓reduceIte]
  · -- an unknown id
    have hu : ∀ g, dispatch env h g ω μ c = unknown g ω μ c := by
      intro g; unfold dispatch; split <;> first | omega | rfl
    simp only [hu] at h₁ h₂ ⊢
    unfold unknown at h₁ h₂ ⊢
    unfold SameButGas
    dsimp only at h₁ h₂ ⊢
    split at h₁ <;> split at h₂ <;> simp_all
    simp only [show ¬((gas₁ : Int) - Constants.Cgasunknown < 0) by omega,
      show ¬((gas₂ : Int) - Constants.Cgasunknown < 0) by omega, ↓reduceIte]

end RefineHost

/-- The most gas a host call on the paths proved here may charge: `refineContract` allows only
    calls that do not run out with this much, so a run's host calls each cost at most this
    (`refineContract_cost`). (`fetch` of the parameters costs 390, an unknown id such as `log`
    1000, `grow_heap` 275 plus 121 a page.) -/
def hostCostMax : Nat := 2000

/-- The refine dispatcher's outcomes for the gas-independent ids, for calls that do not run out of
    gas with `cap`: the outcome with that much gas. `cap` is the most gas a host call may charge;
    a caller picks it from the gas it actually hands the call (it must fit in a `UInt64`, as gas
    does). -/
def refineContractK (cap : Nat) (env : RefineHost.Env) : HostRel RefineCtx :=
  fun h ω μ x s ω' μ' x' =>
    GasFreeId h ∧ s ≠ .oog ∧
      toHostFn (RefineHost.dispatch env) h (UInt64.ofNat cap) ω μ x =
        ⟨s, (toHostFn (RefineHost.dispatch env) h (UInt64.ofNat cap) ω μ x).gas, ω', μ', x'⟩

/-- `refineContractK` at `hostCostMax`: the contract the gas-free proofs use by default. -/
def refineContract (env : RefineHost.Env) : HostRel RefineCtx := refineContractK hostCostMax env

/-- **The contract pins down the dispatcher**, for any cap: a step allowed by `refineContractK cap`
    is the only non-∞ outcome the real handler has, for any gas. -/
theorem refineContractK_pins (cap : Nat) (env : RefineHost.Env) :
    (refineContractK cap env).Pins (toHostFn (RefineHost.dispatch env)).graph := by
  intro h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ ⟨hh, hs₁, he₁⟩ ⟨hs₂, g₂, he₂⟩
  simp only [toHostFn, HostResult.mk.injEq] at he₁ he₂
  obtain ⟨e1s, -, e1r, e1m, e1c⟩ := he₁
  obtain ⟨e2s, -, e2r, e2m, e2c⟩ := he₂
  have n₁ : (RefineHost.dispatch env h (UInt64.ofNat cap).toNat ω μ x).status ≠ .oog := by
    rw [e1s]; exact hs₁
  have n₂ : (RefineHost.dispatch env h g₂.toNat ω μ x).status ≠ .oog := by rw [e2s]; exact hs₂
  obtain ⟨a, b, c, d⟩ := RefineHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  exact ⟨e1s ▸ e2s ▸ a, e1r ▸ e2r ▸ b, e1m ▸ e2m ▸ c, e1c ▸ e2c ▸ d⟩

/-- **The contract pins down the dispatcher**: a step allowed by `refineContract` is the only
    non-∞ outcome the real handler has, for any gas. -/
theorem refineContract_pins (env : RefineHost.Env) :
    (refineContract env).Pins (toHostFn (RefineHost.dispatch env)).graph :=
  refineContractK_pins hostCostMax env

namespace RefineHost

theorem writeValue_gas {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) : (writeValue out v o f z).gas = out.gas := by
  unfold writeValue; dsimp only; repeat' split
  all_goals rfl

theorem writeValue_status {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) (h : out.status = .cont) : (writeValue out v o f z).status ≠ .oog := by
  unfold writeValue; dsimp only; repeat' split
  all_goals simp [h]

/-- `charged k`: with a body that keeps the gas and never reports ∞, the call charges exactly k. -/
theorem charged_cost {X : Type} (k g : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X)
    (hb : ∀ a : Int, (body ⟨.cont, a, ω, μ, x⟩).gas = a ∧ (body ⟨.cont, a, ω, μ, x⟩).status ≠ .oog) :
    ((charged k g ω μ x body).status ≠ .oog → (charged k g ω μ x body).gas = (g : Int) - k) ∧
      (k ≤ g → (charged k g ω μ x body).status ≠ .oog) ∧
      ((charged k g ω μ x body).status ≠ .oog → k ≤ g) := by
  unfold charged
  by_cases hg : g < k
  · simp [hg]
  · simp only [hg, ↓reduceIte]
    exact ⟨fun _ => (hb _).1, fun _ => (hb _).2, fun _ => by omega⟩

/-- **Each gas-independent call charges a fixed cost k** (at most 275 more than the gas it was
    given, for `grow_heap`'s no-growth case): the gas left is g − k whenever it does not run out,
    and it does not run out once g ≥ k. -/
theorem dispatch_cost (env : Env) {h : Nat} (hh : GasFreeId h) (ω : Regs) (μ : Memory)
    (c : RefineCtx) : ∃ k : Nat, ∀ g : Nat,
      ((dispatch env h g ω μ c).status ≠ .oog → (dispatch env h g ω μ c).gas = (g : Int) - k) ∧
      (k ≤ g → (dispatch env h g ω μ c).status ≠ .oog) ∧
      ((dispatch env h g ω μ c).status ≠ .oog → k ≤ max g 275) := by
  rcases hh with rfl | rfl | ⟨h3, h8⟩ | hlt
  · -- grow_heap
    simp only [dispatch]
    unfold hostGrowHeap
    generalize growHeapCore ω μ env.code = q
    obtain ⟨a, b, hp, w⟩ := q
    dsimp only
    by_cases hc : w ≤ hp ∨ w > b
    · refine ⟨Constants.CgasGeminiconst, fun g => ?_⟩
      simp only [hc, ↓reduceIte]
      exact ⟨fun _ => trivial, fun _ => by simp, fun _ => by simp [Constants.CgasGeminiconst]; omega⟩
    · refine ⟨Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear, fun g => ?_⟩
      simp only [hc, ↓reduceIte]
      by_cases hg : g < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear
      · simp [hg]
      · simp only [hg, ↓reduceIte]
        refine ⟨fun _ => ?_, fun _ => by simp, fun _ => by omega⟩
        simp
  · -- fetch
    simp only [dispatch, hostFetch]
    refine ⟨(Constants.CgasY (if reg ω 10 < 16 then some (reg ω 10) else none)).fst +
      memGas (Constants.CgasY (if reg ω 10 < 16 then some (reg ω 10) else none)).snd (reg ω 9), fun g => ?_⟩
    have := charged_cost ((Constants.CgasY (if reg ω 10 < 16 then some (reg ω 10) else none)).fst +
      memGas (Constants.CgasY (if reg ω 10 < 16 then some (reg ω 10) else none)).snd (reg ω 9)) g ω μ c
      (fun out => writeValue out (Except.ok (fetchValue env.fetch (reg ω 10) (reg ω 11) (reg ω 12)))
        (reg ω 7) (reg ω 8) (reg ω 9)) fun a =>
      ⟨writeValue_gas _ _ _ _ _, writeValue_status _ _ _ _ _ rfl⟩
    exact ⟨this.1, this.2.1, fun h => Nat.le_trans (this.2.2 h) (Nat.le_max_left _ _)⟩
  · rcases (show h = 7 ∨ h = 8 ∨ (3 ≤ h ∧ h ≤ 6) by omega) with rfl | rfl | h36
    · -- historical_lookup
      simp only [dispatch, historicalLookup]
      refine ⟨Constants.CgasHconst + memGas Constants.CgasHlinear (reg ω 11), fun g => ?_⟩
      have := @charged_cost RefineCtx (Constants.CgasHconst + memGas Constants.CgasHlinear (reg ω 11)) g ω μ c
      refine (fun H => ⟨H.1, H.2.1, fun h => Nat.le_trans (H.2.2 h) (Nat.le_max_left _ _)⟩) (this _ ?_)
      intro a
      exact ⟨writeValue_gas _ _ _ _ _, writeValue_status _ _ _ _ _ rfl⟩
    · -- export
      simp only [dispatch, exportSeg]
      refine ⟨Constants.CgasE, fun g => ?_⟩
      have := @charged_cost RefineCtx Constants.CgasE g ω μ c
      refine (fun H => ⟨H.1, H.2.1, fun h => Nat.le_trans (H.2.2 h) (Nat.le_max_left _ _)⟩) (this _ ?_)
      intro a
      split
      · simp [panic]
      · split <;> simp [r7]
    · -- an id the dispatcher does not know
      have hu : ∀ g, dispatch env h g ω μ c = unknown g ω μ c := by
        intro g; unfold dispatch; split <;> first | omega | rfl
      refine ⟨Constants.Cgasunknown, fun g => ?_⟩
      simp only [hu, unknown]
      by_cases hg : (g : Int) - Constants.Cgasunknown < 0
      · simp only [hg, ↓reduceIte]
        refine ⟨fun h => absurd rfl h, fun h => ?_, fun h => absurd rfl h⟩
        simp only [Constants.Cgasunknown] at hg h; omega
      · simp only [hg, ↓reduceIte]
        refine ⟨fun _ => trivial, fun _ => by simp, fun _ => ?_⟩
        simp only [Constants.Cgasunknown] at hg ⊢; omega
  · -- an unknown id
    have hu : ∀ g, dispatch env h g ω μ c = unknown g ω μ c := by
      intro g; unfold dispatch; split <;> first | omega | rfl
    refine ⟨Constants.Cgasunknown, fun g => ?_⟩
    simp only [hu, unknown]
    by_cases hg : (g : Int) - Constants.Cgasunknown < 0
    · simp only [hg, ↓reduceIte]
      refine ⟨fun h => absurd rfl h, fun h => ?_, fun h => absurd rfl h⟩
      simp only [Constants.Cgasunknown] at hg h; omega
    · simp only [hg, ↓reduceIte]
      refine ⟨fun _ => trivial, fun _ => by simp, fun _ => ?_⟩
      simp only [Constants.Cgasunknown] at hg ⊢; omega

end RefineHost

/-- **The host calls `refineContractK cap` allows each cost at most `cap`**, and do what the
    contract says with any gas of at least that. (`cap` must cover `grow_heap`'s base cost 275,
    which a call that does not grow charges whatever the gas.) -/
theorem refineContractK_cost (cap : Nat) (h275 : 275 ≤ cap) (hcap : cap < 2 ^ 64)
    (env : RefineHost.Env) :
    HostCostLe (toHostFn (RefineHost.dispatch env)) (refineContractK cap env) cap := by
  intro h ω μ x ω' μ' x' ⟨hh, hs, he⟩ g hg
  have hmax : (UInt64.ofNat cap).toNat = cap := UInt64.toNat_ofNat_of_lt' hcap
  simp only [toHostFn, HostResult.mk.injEq] at he
  obtain ⟨es, -, er, em, ec⟩ := he
  rw [hmax] at es er em ec
  have n₁ : (RefineHost.dispatch env h cap ω μ x).status ≠ .oog := by rw [es]; exact hs
  obtain ⟨k, hk⟩ := RefineHost.dispatch_cost env hh ω μ x
  have hkle : k ≤ cap := by
    have := (hk cap).2.2 n₁; omega
  have n₂ : (RefineHost.dispatch env h g.toNat ω μ x).status ≠ .oog := (hk g.toNat).2.1 (by omega)
  have hgas := (hk g.toNat).1 n₂
  obtain ⟨a, b, c, d⟩ := RefineHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  simp only [toHostFn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← a, es]
  · rw [← b, er]
  · rw [← c, em]
  · rw [← d, ec]
  · have hg64 := g.toNat_lt
    have hsz : UInt64.size = 2 ^ 64 := rfl
    rw [hgas, UInt64.toNat_ofNat_of_lt' (by omega)]
    omega

/-- **The host calls `refineContract` allows each cost at most `hostCostMax`**, and do what the
    contract says with any gas of at least that. -/
theorem refineContract_cost (env : RefineHost.Env) :
    HostCostLe (toHostFn (RefineHost.dispatch env)) (refineContract env) hostCostMax :=
  refineContractK_cost hostCostMax (by decide) (by decide) env

/-- **A larger cap allows more**: a call that does not run out of gas with c₁ does not with
    c₂ ≥ c₁ either, and does the same. So a proof under `refineContract` lifts to
    `refineContractK cap` for any `cap ≥ hostCostMax` (`FreeStepsH.weaken`). -/
theorem refineContractK_mono {c₁ c₂ : Nat} (h275 : 275 ≤ c₁) (h12 : c₁ ≤ c₂) (hc₂ : c₂ < 2 ^ 64)
    (env : RefineHost.Env)
    {h : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx} {ω' : Regs} {μ' : Memory} {x' : RefineCtx}
    (hr : refineContractK c₁ env h ω μ x .cont ω' μ' x') :
    refineContractK c₂ env h ω μ x .cont ω' μ' x' := by
  obtain ⟨hh, hs, he⟩ := hr
  have hc₁ : c₁ < 2 ^ 64 := by omega
  obtain ⟨e1, e2, e3, e4, -⟩ := refineContractK_cost c₁ h275 hc₁ env h ω μ x ω' μ' x' ⟨hh, hs, he⟩
    (UInt64.ofNat c₂) (by rw [UInt64.toNat_ofNat_of_lt' hc₂]; exact h12)
  refine ⟨hh, hs, ?_⟩
  simp only [toHostFn] at e1 e2 e3 e4 ⊢
  simp only [HostResult.mk.injEq, e1, e2, e3, e4, and_self]

/-- `refineContract` lifts to any larger cap. -/
theorem refineContract_le {cap : Nat} (hc : hostCostMax ≤ cap) (hcap : cap < 2 ^ 64)
    (env : RefineHost.Env) {h : Nat} {ω : Regs} {μ : Memory} {x : RefineCtx} {ω' : Regs}
    {μ' : Memory} {x' : RefineCtx} (hr : refineContract env h ω μ x .cont ω' μ' x') :
    refineContractK cap env h ω μ x .cont ω' μ' x' :=
  refineContractK_mono (by decide) hc hcap env hr

/-! ## The host-step tactic -/

/-- Prove that a host call's outcome is allowed by `refineContract`: check the id is gas-free,
    then compute the dispatcher at the largest gas and fix the outcome by `rfl` (cf. `pvm_simp`
    for ordinary steps). The extra terms are facts for `simp`. -/
syntax "pvm_host" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_host [$hs,*]) => `(tactic| (
    refine ⟨by unfold JAM.GasFreeId; decide, by decide, ?_⟩
    simp only [JAM.hostCostMax, JAM.toHostFn, JAM.RefineHost.dispatch, JAM.hostFetch, JAM.hostGrowHeap, JAM.charged,
      JAM.fetchValue, JAM.writeValue, JAM.RefineHost.unknown, JAM.memGas, JAM.reg, JAM.setR7,
      JAM.Params.encode_length, PVM.Memory.rangeWritable, PVM.Regs.get, Fin.getElem_fin,
      PVM.regIdx_val_0, PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4,
      PVM.regIdx_val_5, PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9,
      PVM.regIdx_val_10, PVM.regIdx_val_11, PVM.regIdx_val_12, Vector.getElem_ofFn,
      Vector.getElem_set, UInt64.toNat_ofNat', UInt64.toNat_ofNat, UInt64.reduceToNat,
      PVM.getD_some', List.getD_cons_zero, List.getD_cons_succ, Fin.isValue, ↓reduceIte,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.reduceDiv,
      Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceLeDiff, Int.reduceLT, Int.reduceSub, Int.reduceNeg,
      Nat.min_def, List.take_zero, List.drop_zero, PVM.Memory.writeN_nil, beq_self_eq_true,
      List.take_of_length_le, Nat.le_refl, Nat.reduceBEq, Nat.reduceBNe, decide_eq_true_eq,
      Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ite_true, ite_false, Nat.lt_irrefl, Nat.zero_le, Nat.sub_self,
      PVM.two32, PVM.two64, PVM.pageSize, JAM.Constants.CgasY, id_eq, PVM.getElem_regsNF,
      PVM.lookup_cons_nat, List.lookup_nil, Option.getD_none, PVM.set_regsNF, PVM.insertReg, $hs,*]
    rfl))

end JAM
