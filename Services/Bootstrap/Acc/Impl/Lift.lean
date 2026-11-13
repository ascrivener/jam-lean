import Services.Bootstrap.Acc.Impl.OogPrefix

/-!
# The lift: from `Impl` to what Ψ_M reports

If, for every answer stream, a run from Y's initial state implements `prog` and then halts, then
what Ψ_M (with Ψ_A's handler) leaves is what `ASem.run n prog` reports for some n (`impl_psiM`):
- x after a halt;
- y after ☇ or ∞ (GP eq. `accinvocation`).
This holds from a start (x₀, x₀).
- **No ∞:** the real run is a run under `accContractS` for some stream (`FreeRunH.toS`), and
  `Impl.run` gives one. They are the same run (`accContractS_pins`, `FreeRunH.det`). An early ☇
  keeps x₀'s y, which `ASem.run 0` reports.
- **∞:** the context Ψ_M returns has the y of a prefix of such a run (`psiM_oog_pre`), and
  `Impl.prefix` says what that y is.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Spec

/-- What Ψ_A takes from Ψ_M's output and final context (GP eq. `accinvocation`), without the gas and
    without a returned hash: x after an output, y after ☇ or ∞. -/
def psiMOutcome (r : Nat × InvOutput × AccCtx) :
    PartialState × List DeferredTransfer × Option (List UInt8) × Provisions :=
  match r.2.1 with
  | .ok _ => (r.2.2.1.state, r.2.2.1.xfers, r.2.2.1.yield, r.2.2.1.provisions)
  | _ => (r.2.2.2.state, r.2.2.2.xfers, r.2.2.2.yield, r.2.2.2.provisions)

/-- From (x, x), any `ASem.run 0` reports y. -/
theorem run0_y (env : AccEnv) (prog : Prog AOp Unit) (c : AccCtx) (hc : c.1 = c.2) :
    ASem.outcome (ASem.run 0 prog env c) = yOutcome c.2 := by
  obtain ⟨x, y⟩ := c
  dsimp only at hc; subst hc
  cases prog <;> rfl

/-- **The lift.** If for every stream f a run from Y's initial state with context (x₀, x₀) and
    answers f implements `prog` and halts (early ☇ only for a reason in `Ab`), then Ψ_M's outcome is
    `ASem.run n prog`'s for some n, and that run finished, or Ψ_M ran out of gas, or a run reached a
    state where a reason in `Ab` holds. -/
theorem impl_psiM (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (env : AccEnv)
    (x₀ : AccCtx) (hx : x₀.1 = x₀.2) {p : ByteArray} {ω : Regs} {μ : Memory}
    (hY : standardInit b a = some (p, ω, μ)) (prog : Prog AOp Unit) (Ab : St Stream → Prop)
    (himpl : ∀ f : Stream, Impl p (accContractS env) env Ab prog (Halts p (accContractS env)) ⟨i, ω, μ, x₀, f⟩) :
    (∃ n, psiMOutcome (psiM b i gas a (accHostFn env) x₀) = ASem.outcome (ASem.run n prog env x₀) ∧
      ((ASem.run n prog env x₀).1 ≠ .stopped ∨ (psiM b i gas a (accHostFn env) x₀).2.1 = .oog ∨
        ∃ (f : Stream) (s' : St Stream), Reaches p (accContractS env) ⟨i, ω, μ, x₀, f⟩ s' ∧ Ab s')) ∧
      ∀ out, (psiM b i gas a (accHostFn env) x₀).2.1 = .ok out → out.size = 0 := by
  have hpin := accContractS_pins env
  cases hoog : (psiM b i gas a (accHostFn env) x₀).2.1 with
  | oog =>
    obtain ⟨p', ω', μ', hY', f, c₀, hpre, hc⟩ := psiM_oog_pre b i gas a x₀ env hoog
    rw [hY] at hY'; cases hY'
    have hout : psiMOutcome (psiM b i gas a (accHostFn env) x₀) = yOutcome c₀.2 := by
      simp only [psiMOutcome, hoog, hc]; rfl
    rw [hout]
    refine ⟨?_, fun out h => by cases h⟩
    rcases Impl.prefix hpin prog _ (himpl f) c₀ hpre with h | ⟨n, hn⟩
    · exact ⟨0, by rw [run0_y env prog x₀ hx]; dsimp only at h; rw [h], .inr (.inl hoog)⟩
    · exact ⟨n, hn.symm, .inr (.inl hoog)⟩
  | _ =>
    all_goals
      have hno : (psiM b i gas a (accHostFn env) x₀).2.1.isOog = false := by rw [hoog]; rfl
      have hresp : (accHostFn env).Respects (accGraphS env) := fun h g ω μ x => ⟨g, rfl⟩
      rcases psiM_free b i gas a x₀ (accGraphS env) (accHostFn env) (accHostFn_gasNonIncreasing env)
          hresp hno with ⟨hY', _⟩ | ⟨p', ω₀, μ₀, ε, ω', μ', x', hY', hrun, hres⟩
      · rw [hY] at hY'; cases hY'
      · rw [hY] at hY'; cases hY'
        have hε : ε ≠ .oog := by
          intro he; rw [hres] at hoog; simp [freeOutput, he] at hoog
        obtain ⟨f, tl', hrunS⟩ := FreeRunH.toS env hrun hε (fun _ => 0)
        obtain ⟨ε₂, c₂, ω₂, μ₂, q₂, he₂, h8, hr⟩ := Impl.run prog _ (himpl f)
        obtain ⟨n, hn, hcase⟩ : ∃ n, ASem.outcome (ASem.run n prog env x₀) = runOutcome ε₂ c₂ ∧
            ((ASem.run n prog env x₀).1 ≠ .stopped ∨
              ∃ (f : Stream) (s' : St Stream), Reaches p (accContractS env) ⟨i, ω, μ, x₀, f⟩ s' ∧ Ab s') := by
          rcases hr with ⟨n, hn, hf⟩ | ⟨hab, hr⟩
          · exact ⟨n, hn, .inl hf⟩
          rcases hr with ⟨n, hn⟩ | ⟨hne, hy⟩
          · exact ⟨n, hn, .inr ⟨f, hab⟩⟩
          · refine ⟨0, ?_, .inr ⟨f, hab⟩⟩
            rw [run0_y env prog x₀ hx]
            dsimp only at hy
            simp only [runOutcome, if_neg hne, yOutcome, hy]
        obtain ⟨rfl, rfl, rfl, hxq⟩ := FreeRunH.det hpin he₂ hrunS
        have hc₂ : c₂ = x' := congrArg Prod.fst hxq
        subst hc₂
        refine ⟨⟨n, ?_, hcase.elim .inl (fun h => .inr (.inr h))⟩, fun out hout => ?_⟩
        rotate_left
        · have hf : freeOutput ε₂ ω₂ μ₂ = .ok out := by
            have := hoog; rw [hres] at this; exact this.trans hout
          by_cases hh : ε₂ = .halt
          · subst hh
            have h8' := h8 rfl
            by_cases hrd : μ₂.rangeReadable (ω₂.get 7).toNat (ω₂.get 8).toNat <;>
              simp [freeOutput, hrd] at hf <;> subst hf
            · show (List.toArray _).size = 0
              simp [h8', Memory.readN]
            · rfl
          · cases ε₂ <;> simp [freeOutput] at hf hh
        rw [hn]
        unfold psiMOutcome
        rw [hres]
        simp only [runOutcome]
        by_cases hh : ε₂ = .halt
        · subst hh
          by_cases hrd : μ₂.rangeReadable (ω₂.get 7).toNat (ω₂.get 8).toNat <;> simp [freeOutput, hrd]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hh)]
          cases ε₂ <;> first | exact absurd rfl hh | rfl | (exfalso; exact hε rfl)

/-- **T2's shape, from `Impl`** (`docs/bootstrap-target.md`, `accumulate_spec`). Suppose service s's
    code, in the state **e**′ with the incoming transfers credited, is `code` within 𝖶_C, and Y
    succeeds on it. Suppose also that for every answer stream a run from instruction 5 with context
    (x₀, x₀), x₀ = I(**e**′, s), implements `prog` and halts, with early ☇ only for the reasons `Ab`.
    Then Ψ_A's state, transfers, yield and provisions are `ASem.run n prog`'s outcome for some n, and
    one of these holds:
    - that run of the spec finished (`done` or `panicked`);
    - Ψ_M ran out of gas (∞);
    - a run from instruction 5 (under `accContractS`, for some answer stream) reaches a state where
      a reason in `Ab` holds. -/
theorem psiA_of_impl (η : List UInt8) (e : PartialState) (t s g : Nat) (inputs : List AccumulateInput)
    (code : ByteArray) (hcode : ASem.codeOf (ASem.credit e s inputs) s = some code)
    (hsize : ¬ code.size > Constants.Cmaxservicecodesize) {p : ByteArray} {ω : Regs} {μ : Memory}
    (hY : standardInit code ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩ = some (p, ω, μ))
    (prog : Prog AOp Unit) (Ab : St Stream → Prop)
    (himpl : ∀ f : Stream, Impl p (accContractS (ASem.accEnv η t inputs code)) (ASem.accEnv η t inputs code) Ab prog
      (Halts p (accContractS (ASem.accEnv η t inputs code)))
      ⟨5, ω, μ, (initImplications (ASem.credit e s inputs) s t η, initImplications (ASem.credit e s inputs) s t η), f⟩) :
    let o := psiA Params.full η e t s g inputs
    let x₀ := initImplications (ASem.credit e s inputs) s t η
    ∃ n, (o.state, o.xfers, o.yield, o.provisions) = ASem.outcome (ASem.run n prog (ASem.accEnv η t inputs code) (x₀, x₀)) ∧
      ((ASem.run n prog (ASem.accEnv η t inputs code) (x₀, x₀)).1 ≠ .stopped ∨
        (psiM code 5 (UInt64.ofNat g) ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
          (accHostFn (ASem.accEnv η t inputs code)) (x₀, x₀)).2.1 = .oog ∨
        ∃ (f : Stream) (s' : St Stream), Reaches p (accContractS (ASem.accEnv η t inputs code)) ⟨5, ω, μ, (x₀, x₀), f⟩ s' ∧ Ab s') := by
  intro o x₀
  have hA : o = psiARun Params.full η (ASem.credit e s inputs) t s g inputs := ASem.psiA_eq _ _ _ _ _ _ _
  obtain ⟨⟨n, hn, hc⟩, hsz⟩ := impl_psiM code 5 (UInt64.ofNat g) _ (ASem.accEnv η t inputs code) _ rfl hY prog Ab
    himpl
  refine ⟨n, ?_, hc⟩
  rw [← hn, hA, psiARun_eq Params.full η (ASem.credit e s inputs) t s g inputs code hcode hsize]
  simp only [ASem.accEnv] at hsz ⊢
  generalize psiM _ _ _ _ _ _ = r at hsz ⊢
  obtain ⟨u, out, c⟩ := r
  cases out with
  | ok b =>
    have hb := hsz b rfl
    simp only [psiMOutcome, hb]
    rfl
  | _ => rfl

end Services.Bootstrap.Acc
