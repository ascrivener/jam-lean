import Services.Bootstrap.Acc.Impl.Impl
import Services.Bootstrap.Acc.Contract
import PVM.Logic.Host

/-!
# The accumulate contract with an answer stream for `gas` and `checkpoint`

Ω_G (`gas`, 0) and Ω_C (`checkpoint`, 18) put the gas left in ω₇ (GP v0.8.0 eq. `accinvocation`),
which a gas-free run does not know. As in Handlers A's `accContractQ` (an answer list), the context
carries the answers, here as an infinite stream `Nat → Nat` (so a run never runs out of them):
- at a gas-independent id (`AccGasFreeId`), the model's outcome at some gas, not ∞, the stream kept;
- at 0 or 18, the call continues with ω₇ := the stream's head, which it drops, the memory kept, and
  y := x at 18.

`accContractS_pins`: it pins itself. `FreeRunH.toS`: a non-∞ run of the handler's outcomes is a run
under it, for some stream (the values left at its `gas` and `checkpoint` calls, then 0s).
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- An answer stream. -/
abbrev Stream := Nat → Nat

/-- The stream without its head. -/
def Stream.tail (f : Stream) : Stream := fun n => f (n + 1)

/-- v, then f. -/
def Stream.cons (v : Nat) (f : Stream) : Stream := fun n => if n = 0 then v else f (n - 1)

theorem Stream.tail_cons (v : Nat) (f : Stream) : (Stream.cons v f).tail = f := by
  funext n; simp [Stream.tail, Stream.cons]

/-- **The accumulate contract with an answer stream** (see the module docstring). -/
def accContractS (env : AccEnv) : HostRel (AccCtx × Stream) :=
  fun h ω μ xq s ω' μ' xq' =>
    (AccGasFreeId h ∧ s ≠ .oog ∧ xq'.2 = xq.2 ∧
      ∃ g, accHostFn env h g ω μ xq.1 = ⟨s, (accHostFn env h g ω μ xq.1).gas, ω', μ', xq'.1⟩) ∨
    ((h = 0 ∨ h = 18) ∧ s = .cont ∧ μ' = μ ∧
      xq'.1 = (if h = 18 then (xq.1.1, xq.1.1) else xq.1) ∧
      xq'.2 = xq.2.tail ∧ ω' = setR7 ω (xq.2 0))

/-- **`accContractS` is deterministic.** -/
theorem accContractS_pins (env : AccEnv) : (accContractS env).Pins (accContractS env) := by
  intro h ω μ xq s₁ ω₁ μ₁ xq₁ s₂ ω₂ μ₂ xq₂ h₁ h₂
  rcases h₁ with ⟨hh, hs₁, hq₁, g₁, he₁⟩ | ⟨h018, rfl, rfl, hx₁, hq₁, rfl⟩ <;>
    rcases h₂ with ⟨hh', hs₂, hq₂, g₂, he₂⟩ | ⟨h018', rfl, rfl, hx₂, hq₂, rfl⟩
  · simp only [accHostFn, HostResult.mk.injEq] at he₁ he₂
    obtain ⟨e1s, -, e1r, e1m, e1c⟩ := he₁
    obtain ⟨e2s, -, e2r, e2m, e2c⟩ := he₂
    have n₁ : (AccHost.dispatch env h g₁.toNat ω μ xq.1).status ≠ .oog := by
      intro hc; apply hs₁; rw [← e1s, hc]
    have n₂ : (AccHost.dispatch env h g₂.toNat ω μ xq.1).status ≠ .oog := by
      intro hc; apply hs₂; rw [← e2s, hc]
    obtain ⟨a, b, c, d⟩ := AccHost.dispatch_sameButGas env hh ω μ xq.1 n₁ n₂
    exact ⟨e1s ▸ e2s ▸ a, e1r ▸ e2r ▸ b, e1m ▸ e2m ▸ c, Prod.ext (e1c ▸ e2c ▸ d) (hq₁.trans hq₂.symm)⟩
  · exfalso; unfold AccGasFreeId at hh; omega
  · exfalso; unfold AccGasFreeId at hh'; omega
  · exact ⟨rfl, rfl, rfl, Prod.ext (hx₁.trans hx₂.symm) (hq₁.trans hq₂.symm)⟩

/-- The handler's outcomes, at any gas. -/
def accGraphS (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' => ∃ g, accHostFn env h g ω μ x = ⟨s, (accHostFn env h g ω μ x).gas, ω', μ', x'⟩

/-- Ω_G and Ω_C continue only with ω₇ := the gas left, memory kept, and the context kept (Ω_G) or
    y := x (Ω_C); otherwise they end in ∞. -/
theorem gasCk_outcomeS (env : AccEnv) {h : Nat} (hh : h = 0 ∨ h = 18) (g : UInt64) (ω : Regs) (μ : Memory)
    (x : AccCtx) :
    (accHostFn env h g ω μ x).status = .oog ∨
      ((accHostFn env h g ω μ x).status = .cont ∧ (accHostFn env h g ω μ x).mem = μ ∧
        (accHostFn env h g ω μ x).ctx = (if h = 18 then (x.1, x.1) else x) ∧
        ∃ v, (accHostFn env h g ω μ x).regs = setR7 ω v) := by
  rcases hh with rfl | rfl
  · simp only [accHostFn, AccHost.dispatch, hostGas, charged]
    split <;> simp; exact ⟨_, rfl⟩
  · simp only [accHostFn, AccHost.dispatch, AccHost.checkpoint, AccHost.charge, charged]
    split <;> simp; exact ⟨_, rfl⟩

theorem toStatus_ne_oogS {s : PVM.HostStatus} (h : s.toStatus ≠ Status.oog) : s ≠ PVM.HostStatus.oog := by
  rintro rfl; exact h rfl

/-- **A non-∞ run of the handler's outcomes is a run under `accContractS`**, for the stream of the
    values its `gas` and `checkpoint` calls put in ω₇ (then anything, `tl`). -/
theorem FreeRunH.toS (env : AccEnv) {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hrun : FreeRunH p (accGraphS env) i ω μ x ε ω' μ' x') (hε : ε ≠ .oog) (tl : Stream) :
    ∃ f tl', FreeRunH p (accContractS env) i ω μ (x, f) ε ω' μ' (x', tl') := by
  induction hrun with
  | exit hr hh => exact ⟨tl, tl, .exit hr hh⟩
  | @host i ω μ x h e ω₁ μ₁ ω₂ μ₂ x₂ ε ω₃ μ₃ x₃ hr hR _ ih =>
    obtain ⟨f, tl', hq⟩ := ih hε
    obtain ⟨g, hg⟩ := hR
    by_cases hgf : AccGasFreeId h.toNat
    · exact ⟨f, tl', .host (x'' := (x₂, f)) hr (.inl ⟨hgf, by simp, rfl, g, by simpa using hg⟩) hq⟩
    · have h018 : h.toNat = 0 ∨ h.toNat = 18 := by unfold AccGasFreeId at hgf; omega
      rcases gasCk_outcomeS env h018 g ω₁ μ₁ x with ho | ⟨hs, hm, hx, v, hv⟩
      · rw [hg] at ho; simp at ho
      · rw [hg] at hs hm hx hv
        simp only at hs hm hx hv
        refine ⟨Stream.cons v f, tl', .host (x'' := (x₂, f)) hr
          (.inr ⟨h018, rfl, hm, hx, (Stream.tail_cons v f).symm, ?_⟩) hq⟩
        rw [hv]; simp [Stream.cons]
  | @hostStop i ω μ x h e ω₁ μ₁ s ω₂ μ₂ x₂ hr hR hs =>
    obtain ⟨g, hg⟩ := hR
    by_cases hgf : AccGasFreeId h.toNat
    · exact ⟨tl, tl, .hostStop (x'' := (x₂, tl)) hr
        (.inl ⟨hgf, toStatus_ne_oogS hε, rfl, g, by simpa using hg⟩) hs⟩
    · have h018 : h.toNat = 0 ∨ h.toNat = 18 := by unfold AccGasFreeId at hgf; omega
      rcases gasCk_outcomeS env h018 g ω₁ μ₁ x with ho | ⟨hs', -⟩
      · rw [hg] at ho; simp only at ho; subst ho; exact absurd rfl hε
      · rw [hg] at hs'; exact absurd hs' hs

end Services.Bootstrap.Acc
