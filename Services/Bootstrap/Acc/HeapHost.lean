import Services.Bootstrap.Acc.Contract
import Services.Bootstrap.Alloc.HeapContract

/-!
# The accumulate contract is a host fit for the allocator

`accHeapHost env`: the accumulate contract `accContractK · env` (Ψ_A's handler F, GP v0.8.0 eq.
`accinvocation`) as a `HeapHost`, so the allocator's and the heap decoders' host-generic theorems
(`…G`) hold under it. Its three facts:
- `grow`: a `grow_heap` call whose cost fits in the cap has Ω_♊'s outcome;
- `keep`: every continuing call of an `AccGasFreeId` id keeps the page table outside the heap and
  every octet that is not writable. `grow_heap` sets heap pages only; `fetch`, `lookup`, `read` and
  `info` write octets through `writeValue`, which checks that they are writable; `write` and the
  unknown ids leave memory alone;
- `le`: a call that does not run out of gas with `hostCostMax` does not with any larger cap either,
  and does the same (`AccHost.dispatch_noOog_mono`, then `AccHost.dispatch_sameButGas`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap.Alloc

/-- A charged call whose body's outcome does not depend on the gas: if it does not run out of gas
    with g₁, it does not with any g₂ ≥ g₁. -/
theorem charged_noOog_mono {X : Type} (g : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X)
    (hb : ∀ a b, SameButGas (body ⟨.cont, a, ω, μ, x⟩) (body ⟨.cont, b, ω, μ, x⟩))
    {g₁ g₂ : Nat} (h12 : g₁ ≤ g₂) (h₁ : (charged g g₁ ω μ x body).status ≠ .oog) :
    (charged g g₂ ω μ x body).status ≠ .oog := by
  unfold charged at *
  by_cases c1 : g₁ < g
  · rw [if_pos c1] at h₁; exact absurd rfl h₁
  · rw [if_neg c1] at h₁
    rw [if_neg (by omega), ← (hb _ _).1]
    exact h₁

namespace AccHost

/-- **More gas does not run out where less did not**, for the gas-independent ids. -/
theorem dispatch_noOog_mono (env : AccEnv) {h : Nat} (hh : AccGasFreeId h) (ω : Regs) (μ : Memory)
    (c : AccCtx) {g₁ g₂ : Nat} (h12 : g₁ ≤ g₂) (h₁ : (AccHost.dispatch env h g₁ ω μ c).status ≠ .oog) :
    (AccHost.dispatch env h g₂ ω μ c).status ≠ .oog := by
  have unk : ∀ (g : Nat), h ≠ 0 → h ≠ 1 → h ≠ 2 → h ≠ 3 → h ≠ 4 → h ≠ 5 → h ≠ 6 →
      (h < 15 ∨ 27 < h) →
      AccHost.dispatch env h g ω μ c =
        let g' : Int := (g : Int) - Constants.Cgasunknown
        ⟨if g' < 0 then .oog else .cont, g', setR7 ω Result.WHAT, μ, c⟩ := by
    intro g n0 n1 n2 n3 n4 n5 n6 hr
    unfold AccHost.dispatch
    split <;> first | omega | rfl
  have wv : ∀ (v : Except Unit (Option (List UInt8))) (o f z : Nat) (X : Type) (ω : Regs)
      (μ : Memory) (x : X) (a b : Int),
      SameButGas (writeValue ⟨.cont, a, ω, μ, x⟩ v o f z) (writeValue ⟨.cont, b, ω, μ, x⟩ v o f z) :=
    fun v o f z _ ω μ x a b => writeValue_sameButGas _ _ _ _ _ _ _ _ _ _
  by_cases e1 : h = 1
  · subst e1
    simp only [AccHost.dispatch] at *
    unfold hostGrowHeap at *
    generalize growHeapCore ω μ env.code = q at *
    obtain ⟨a, b, hp, w⟩ := q
    dsimp only at *
    by_cases hc : w ≤ hp ∨ w > b
    · simp [hc]
    · simp only [hc, ↓reduceIte] at h₁ ⊢
      by_cases c1 : g₁ < Constants.CgasGeminiconst + (w - hp) * Constants.CgasGeminilinear
      · simp [c1] at h₁
      · rw [if_neg (by omega)]; simp
  by_cases e2 : h = 2
  · subst e2
    simp only [AccHost.dispatch, hostFetch] at *
    exact charged_noOog_mono _ _ _ _ _ (fun a b => wv _ _ _ _ _ _ _ _ a b) h12 h₁
  by_cases e3 : h = 3
  · subst e3
    simp only [AccHost.dispatch, hostLookup] at *
    exact charged_noOog_mono _ _ _ _ _ (fun a b => wv _ _ _ _ _ _ _ _ a b) h12 h₁
  by_cases e4 : h = 4
  · subst e4
    simp only [AccHost.dispatch, hostRead] at *
    exact charged_noOog_mono _ _ _ _ _ (fun a b => wv _ _ _ _ _ _ _ _ a b) h12 h₁
  by_cases e5 : h = 5
  · subst e5
    simp only [AccHost.dispatch, AccHost.onSelf] at *
    unfold hostWrite at *
    refine charged_noOog_mono _ _ _ _ _ (fun a b => ?_) h12 h₁
    unfold SameButGas
    dsimp only
    repeat' split
    all_goals simp
  by_cases e6 : h = 6
  · subst e6
    simp only [AccHost.dispatch, hostInfo] at *
    exact charged_noOog_mono _ _ _ _ _ (fun a b => wv _ _ _ _ _ _ _ _ a b) h12 h₁
  have hr : h < 15 ∨ 27 < h := by unfold AccGasFreeId at hh; omega
  have h0 : h ≠ 0 := by unfold AccGasFreeId at hh; omega
  rw [unk g₁ h0 e1 e2 e3 e4 e5 e6 hr] at h₁
  rw [unk g₂ h0 e1 e2 e3 e4 e5 e6 hr]
  dsimp only at h₁ ⊢
  split at h₁
  · exact absurd rfl h₁
  · rw [if_neg (by omega)]; simp

end AccHost

/-- **A larger cap allows more**: a call `accContract` allows, `accContractK cap` allows too, for
    any cap ≥ `hostCostMax`. -/
theorem accContract_le {cap : Nat} (hc : hostCostMax ≤ cap) (hcap : cap < 2 ^ 64) (env : AccEnv)
    {h : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hr : accContract env h ω μ x .cont ω' μ' x') : accContractK cap env h ω μ x .cont ω' μ' x' := by
  obtain ⟨hh, hs, he⟩ := hr
  refine ⟨hh, hs, ?_⟩
  simp only [accHostFn, HostResult.mk.injEq] at he ⊢
  obtain ⟨e1, -, e3, e4, e5⟩ := he
  have hm : (UInt64.ofNat hostCostMax).toNat = hostCostMax := by decide
  have hm2 : (UInt64.ofNat cap).toNat = cap := UInt64.toNat_ofNat_of_lt' hcap
  rw [hm] at e1 e3 e4 e5
  rw [hm2]
  have n₁ : (AccHost.dispatch env h hostCostMax ω μ x).status ≠ .oog := by rw [e1]; exact hs
  have n₂ := AccHost.dispatch_noOog_mono env hh ω μ x hc n₁
  obtain ⟨a, b, c, d⟩ := AccHost.dispatch_sameButGas env hh ω μ x n₁ n₂
  exact ⟨by rw [← a, e1], trivial, by rw [← b, e3], by rw [← c, e4], by rw [← d, e5]⟩

/-- `writeValue` that continues keeps the pages and every octet that is not writable, for any value. -/
theorem writeValue_keep' {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) (hs : (writeValue out v o f z).status = .cont) :
    (writeValue out v o f z).mem.pages = out.mem.pages ∧
      ∀ b, b < two32 → out.mem.writable b = false → (writeValue out v o f z).mem.read b = out.mem.read b := by
  rcases v with _ | v
  · unfold writeValue at hs; simp at hs
  · exact writeValue_keep out v o f z hs

/-- A charged call whose body keeps memory as `writeValue` does: so does the call. -/
theorem charged_keep {X : Type} (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X)
    (hb : ∀ a, (body ⟨.cont, a, ω, μ, x⟩).status = .cont →
      (body ⟨.cont, a, ω, μ, x⟩).mem.pages = μ.pages ∧
        ∀ b, b < two32 → μ.writable b = false → (body ⟨.cont, a, ω, μ, x⟩).mem.read b = μ.read b)
    (hs : (charged g gas ω μ x body).status = .cont) :
    (charged g gas ω μ x body).mem.pages = μ.pages ∧
      ∀ b, b < two32 → μ.writable b = false → (charged g gas ω μ x body).mem.read b = μ.read b := by
  unfold charged at *
  split at hs
  · simp at hs
  · rw [if_neg (by assumption)]
    exact hb _ hs

/-- **A continuing accumulate call keeps what is not writable**: under `accContractK`, a continuing
    call changes no page outside the heap's 48 … pb and no octet that is not writable. -/
theorem accContractK_keep {cap : Nat} {env : AccEnv} {pb : Nat}
    (hbd : heapBounds env.code = (48, pb)) {h : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : AccCtx}
    (hr : accContractK cap env h ω μ x .cont ω' μ' x') :
    PagesOut 48 pb μ μ' ∧ ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b := by
  obtain ⟨hg, -, he⟩ := hr
  simp only [accHostFn, HostResult.mk.injEq] at he
  obtain ⟨hs, -, -, hm, -⟩ := he
  subst hm
  generalize (UInt64.ofNat cap).toNat = g at hs ⊢
  -- the octet-writing calls: pages kept, so outside the heap too
  have ofPages : ∀ μ'' : Memory, μ''.pages = μ.pages →
      (∀ b, b < two32 → μ.writable b = false → μ''.read b = μ.read b) →
      PagesOut 48 pb μ μ'' ∧ ∀ b, b < two32 → μ.writable b = false → μ''.read b = μ.read b :=
    fun μ'' hp hk => ⟨PagesOut.of_eq hp, hk⟩
  have wvk : ∀ (v : Except Unit (Option (List UInt8))) (o f z : Nat) (a : Int),
      (writeValue (⟨.cont, a, ω, μ, x⟩ : HostOut AccCtx) v o f z).status = .cont →
      (writeValue (⟨.cont, a, ω, μ, x⟩ : HostOut AccCtx) v o f z).mem.pages = μ.pages ∧
        ∀ b, b < two32 → μ.writable b = false →
          (writeValue (⟨.cont, a, ω, μ, x⟩ : HostOut AccCtx) v o f z).mem.read b = μ.read b :=
    fun v o f z a hs => writeValue_keep' _ v o f z hs
  have wvk' : ∀ (v : Except Unit (Option (List UInt8))) (o f z : Nat) (a : Int),
      (writeValue (⟨.cont, a, ω, μ, ()⟩ : HostOut Unit) v o f z).status = .cont →
      (writeValue (⟨.cont, a, ω, μ, ()⟩ : HostOut Unit) v o f z).mem.pages = μ.pages ∧
        ∀ b, b < two32 → μ.writable b = false →
          (writeValue (⟨.cont, a, ω, μ, ()⟩ : HostOut Unit) v o f z).mem.read b = μ.read b :=
    fun v o f z a hs => writeValue_keep' _ v o f z hs
  by_cases e1 : h = 1
  · subst e1
    simp only [AccHost.dispatch, hostGrowHeap, growHeapCore, hbd] at hs ⊢
    generalize hC : List.countP (fun k => μ.pages.get? (48 + k) == some Access.write) (List.range (pb - 48)) = C
      at hs ⊢
    have hCle : C ≤ pb - 48 := by
      rw [← hC]; exact Nat.le_trans List.countP_le_length (by simp)
    by_cases c1 : reg ω 7 ≤ 48 + C ∨ reg ω 7 > pb
    · rw [if_pos c1] at hs ⊢
      exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
    · rw [if_neg c1] at hs ⊢
      by_cases c2 : g < Constants.CgasGeminiconst + (reg ω 7 - (48 + C)) * Constants.CgasGeminilinear
      · rw [if_pos c2] at hs; simp at hs
      · rw [if_neg c2]
        exact ⟨fun q hq => Memory.setPages_get_off _ _ _ _ _ (by dsimp only; omega), fun b _ _ => rfl⟩
  by_cases e2 : h = 2
  · subst e2
    simp only [AccHost.dispatch, hostFetch] at hs ⊢
    obtain ⟨hp, hk⟩ := charged_keep _ _ _ _ _ _ (fun a hs => wvk _ _ _ _ a hs) hs
    exact ofPages _ hp hk
  by_cases e3 : h = 3
  · subst e3
    simp only [AccHost.dispatch, hostLookup] at hs ⊢
    obtain ⟨hp, hk⟩ := charged_keep _ _ _ _ _ _ (fun a hs => wvk' _ _ _ _ a hs) hs
    exact ofPages _ hp hk
  by_cases e4 : h = 4
  · subst e4
    simp only [AccHost.dispatch, hostRead] at hs ⊢
    obtain ⟨hp, hk⟩ := charged_keep _ _ _ _ _ _ (fun a hs => wvk' _ _ _ _ a hs) hs
    exact ofPages _ hp hk
  by_cases e5 : h = 5
  · subst e5
    simp only [AccHost.dispatch, AccHost.onSelf] at hs ⊢
    have : (hostWrite g ω μ x.1.self).mem = μ := by
      unfold hostWrite charged
      dsimp only
      repeat' split
      all_goals rfl
    rw [this]
    exact ofPages _ rfl fun _ _ _ => rfl
  by_cases e6 : h = 6
  · subst e6
    simp only [AccHost.dispatch, hostInfo] at hs ⊢
    obtain ⟨hp, hk⟩ := charged_keep _ _ _ _ _ _ (fun a hs => wvk' _ _ _ _ a hs) hs
    exact ofPages _ hp hk
  have hr : h < 15 ∨ 27 < h := by unfold AccGasFreeId at hg; omega
  have h0 : h ≠ 0 := by unfold AccGasFreeId at hg; omega
  have hu : (AccHost.dispatch env h g ω μ x).mem = μ := by
    unfold AccHost.dispatch
    split <;> first | omega | rfl
  rw [hu]
  exact ofPages _ rfl fun _ _ _ => rfl

/-- **The accumulate contract is a host fit for the allocator**: `accContractK cap env` for each
    cap. -/
def accHeapHost (env : AccEnv) : HeapHost AccCtx where
  code := env.code
  rel cap := accContractK cap env
  grow cap hcap a pb hbd ω μ x h hp hah hhb hcost := by
    refine ⟨by unfold AccGasFreeId; decide, by decide, ?_⟩
    simp only [accHostFn, AccHost.dispatch, hostGrowHeap, growHeapCore_eq ω μ env.code hbd hp hah hhb,
      growTop] at hcost ⊢
    have hw := (ω.get 7).toNat_lt
    simp only [reg] at hw hcost ⊢
    by_cases hc : (ω.get 7).toNat ≤ h ∨ (ω.get 7).toNat > pb
    · simp [hc]
    · simp only [hc, ↓reduceIte] at hcost
      have : ¬ cap % 18446744073709551616 <
          Constants.CgasGeminiconst + ((ω.get 7).toNat - h) * Constants.CgasGeminilinear := by
        rw [Nat.mod_eq_of_lt hcap]
        omega
      simp [hc, this]
  keep cap pb hbd h ω μ x ω' μ' x' hr := accContractK_keep hbd hr
  le cap hc hcap h ω μ x ω' μ' x' hr := accContract_le hc hcap env hr

end Services.Bootstrap.Acc
