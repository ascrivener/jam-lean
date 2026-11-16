import Services.Bootstrap.Acc.Handlers.InstrLoopBody

/-!
# R5, the instruction loop as `Impl.forIn`

Spec `onWorkItem`'s loop (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop):

```
for i in is do
  match i with
  | .checkpoint => store key (encodeResults results)
  | _ => pure ()
  let r ← onInstr C now i
  results := results ++ [r]
```

The loop's body f is taken through the two equations its elaboration satisfies (`hck`, `hother`: the
`Checkpoint` store, then `onInstr` and the yield), so the statement does not depend on the matcher the
`do` notation generates. `LoopInv` is the invariant at the head 8540: `LoopAt` for the instructions
left and the results so far, the flag word for the `Zombify`s done (with those left, the flag of the
whole list), the cursor's alignment, the counter's room, the octets below 196608 and the frame words
`StableKeep` as at the entry, the context invariant Inv. `il_loop`: each body (`il_body`, `il_body_ck`)
keeps it, so the loop ends at the head with no instruction left.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.Acc.Handlers.ResStore
open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `onWorkItem`'s test for `Zombify` (quirk Q4's `is.any`). -/
def isZomb : Spec.Instr → Bool
  | .zombify _ => true
  | _ => false

theorem idx3 (i : Spec.Instr) : (instrIdx i == 3) = isZomb i := by cases i <;> rfl

theorem idx15 {i : Spec.Instr} (h : instrIdx i = 15) : i = .checkpoint := by cases i <;> first | rfl | simp [instrIdx] at h

theorem Prog.bind_assoc' {E : Type → Type} {α β γ : Type} (k : β → Prog E γ) (f : α → Prog E β) :
    ∀ p : Prog E α, Prog.bind (Prog.bind p f) k = Prog.bind p (fun x => Prog.bind (f x) k)
  | .pure _ => rfl
  | .call op k' => by
    show Prog.call op (fun b => Prog.bind (Prog.bind (k' b) f) k) = Prog.call op (fun b => Prog.bind (k' b) _)
    congr 1; funext b; exact Prog.bind_assoc' k f (k' b)
  | .panic => rfl

/-- **The instruction loop's invariant at the head 8540** (see the module doc), against the entry's memory
    μ₀, for the instructions left xs and the results so far rs; Z is the whole list's `Zombify` flag and
    n₀ its length. -/
structure LoopInv (B : InstrRep) (code : ByteArray) (pb S0 S1 sp : Nat) (Inv : AccCtx → Prop) (μ₀ : Memory)
    (Z : Bool) (n₀ : Nat) (xs : List Spec.Instr) (rs : List Spec.Result) (s : St Stream) : Prop where
  /-- At the head, or at 8554 with ω₆ = cur where the loop's entry falls through (some instruction left). -/
  hi : s.i = 8540 ∨ (s.i = 8554 ∧ s.ω[6] = UInt64.ofNat (rdN s.μ (sp + 480) 8) ∧ xs ≠ [])
  h1 : s.ω[1] = UInt64.ofNat sp
  inv : Inv s.c
  la : ∃ st zs, LoopAt B code pb S0 S1 sp xs rs zs s.μ st ∧ (zs || xs.any isZomb) = Z
  hal : rdN s.μ (sp + 480) 8 % 8 = 0
  hk : rdN s.μ (sp + 504) 8 + xs.length < 2 ^ 64
  hlen : rs.length + xs.length = n₀
  ro : ∀ a, a < 196608 → s.μ.read a = μ₀.read a ∧ s.μ.readable a = μ₀.readable a
  stab : ∀ a, a < 4294967296 → StableKeep sp a → s.μ.read a = μ₀.read a

/-- `BodyPost` gives the invariant for the instructions left. -/
theorem LoopInv.of_post {B : InstrRep} {code : ByteArray} {pb S0 S1 sp : Nat} {Inv : AccCtx → Prop}
    {μ₀ : Memory} {Z : Bool} {n₀ : Nat} {x : Spec.Instr} {xs : List Spec.Instr} {rs : List Spec.Result}
    {s : St Stream} {zs zs' : Bool} {r : Spec.Result} {s' : St Stream}
    (I : LoopInv B code pb S0 S1 sp Inv μ₀ Z n₀ (x :: xs) rs s) (hz : (zs || (x :: xs).any isZomb) = Z)
    (hz' : zs' = (zs || isZomb x)) (P : BodyPost B code pb S0 S1 sp xs rs zs' s.μ r s') (hinv : Inv s'.c) :
    LoopInv B code pb S0 S1 sp Inv μ₀ Z n₀ xs (rs ++ [r]) s' := by
  obtain ⟨hi, h1, ⟨st', LA'⟩, m480, m504, ro, stab⟩ := P
  have hk := I.hk
  have hal := I.hal
  have hlen := I.hlen
  simp only [List.length_cons] at hk hlen
  have hl' : (rs ++ [r]).length + xs.length = n₀ := by
    simp only [List.length_append, List.length_singleton]; omega
  refine ⟨.inl hi, h1, hinv, ⟨st', zs', LA', ?_⟩, by omega, by omega, hl', fun a ha => ⟨(ro a ha).1.trans (I.ro a ha).1, (ro a ha).2.trans (I.ro a ha).2⟩,
    fun a h0 h => (stab a h0 h).trans (I.stab a h0 h)⟩
  rw [hz', ← hz, List.any_cons, Bool.or_assoc]

/-- **R5, the instruction loop** (8540 → 8540 with no instruction left): from `LoopInv` for the instructions
    left xs and the results rs, the run implements `forIn xs rs f` (spec `onWorkItem`'s loop, GP v0.8.0
    Appendix B, Ω_W; f through its equations `hck` and `hother`, with key the results key of the package
    at sp + 312 and the item) and ends in `LoopInv` for [] and the final results. Named hypotheses:
    `InstrLogH`, `ResultLogH`, `HandlerH`, `PushH` (and `ExtendH`, `OkEncH` for the `Checkpoint` store).
    Premises: the context invariant Inv (kept by every operation, giving `StoreFit`); at the entry's
    memory μ₀ the item index at sp + 176, the key-size word kc, `set`'s error table, the read-only data's
    access and the dispatch table; and the size bound on the results' encoding for every results list no
    longer than the instructions (`hBall`, open: see `docs/t2-remaining.md`). -/
theorem il_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (B : InstrRep) {C : Consts} {now pb S0 S1 : Nat} {Ab : St Stream → Prop}
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s) (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s)
    (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (Inv : AccCtx → Prop)
    (hIst : ∀ {β : Type} (o : AOp β) (c c₁ : AccCtx) (b : β), Inv c → ASem.step env o c = some (b, c₁) → Inv c₁)
    (hIfit : ∀ c, Inv c → StoreFit c)
    (sp item kc : Nat) (μ₀ : Memory) (Z : Bool) (n₀ : Nat) (hs8 : sp % 8 = 0)
    (f : Spec.Instr → List Spec.Result → Prog AOp (ForInStep (List Spec.Result)))
    (hck : ∀ rs, f .checkpoint rs = Prog.bind (store (.results (μ₀.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => Prog.bind (onInstr C now .checkpoint) (fun r => Prog.pure (.yield (rs ++ [r])))))
    (hother : ∀ i rs, i ≠ .checkpoint → f i rs = Prog.bind (onInstr C now i) (fun r => Prog.pure (.yield (rs ++ [r]))))
    (hitem : μ₀.readN (sp + 176) 2 = fixed 2 item)
    (mkc : μ₀.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN μ₀ 69072 4 = 4294900408) (ht4 : rdN μ₀ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → μ₀.readable a = true)
    (hjt : μ₀.readN 65736 100 = jumpTab) (hjr : ∀ a, 65736 ≤ a → a < 65836 → μ₀.readable a = true)
    (hBall : ∀ rs : List Spec.Result, rs.length ≤ n₀ →
      2 * (144 * rs.length + 4) + 4 * (encodeResults rs).length + 64 < 1073741760) :
    ∀ (xs : List Spec.Instr) (rs : List Spec.Result) (s : St Stream),
      LoopInv B env.code pb S0 S1 sp Inv μ₀ Z n₀ xs rs s →
      Impl p (accContractS env) env Ab (forIn xs rs f)
        (fun rs' s' => LoopInv B env.code pb S0 S1 sp Inv μ₀ Z n₀ [] rs' s') s := by
  refine Impl.forIn f _ (LoopInv B env.code pb S0 S1 sp Inv μ₀ Z n₀) ?_ (fun _ _ h => h)
  intro x xs rs s I
  obtain ⟨st, zs, LA, hz⟩ := I.la
  have hk1 : rdN s.μ (sp + 504) 8 + 1 < 2 ^ 64 := by have := I.hk; simp only [List.length_cons] at this; omega
  have hlen := I.hlen
  simp only [List.length_cons] at hlen
  have hT := LA.H.hS1
  have hsp := LA.hsp
  have hjt' : s.μ.readN 65736 100 = jumpTab := by
    rw [← hjt]; exact Memory.readN_congr fun j hj => (I.ro _ (by omega)).1
  have hjr' : ∀ a, 65736 ≤ a → a < 65836 → s.μ.readable a = true := fun a h1 h2 => by
    rw [(I.ro a (by omega)).2]; exact hjr a h1 h2
  have hinvS := I.inv
  have hfit := hIfit _ hinvS
  -- the post-condition of one body, back to the invariant
  have post : ∀ (zs' : Bool), zs' = (zs || isZomb x) → ∀ (r : Spec.Result) (s' : St Stream),
      BodyPost B env.code pb S0 S1 sp xs rs zs' s.μ r s' ∧ Inv s'.c →
      Impl p (accContractS env) env Ab (Prog.pure (ForInStep.yield (rs ++ [r])))
        (fun r s' => match r with
          | .yield b' => LoopInv B env.code pb S0 S1 sp Inv μ₀ Z n₀ xs b' s'
          | .done b' => LoopInv B env.code pb S0 S1 sp Inv μ₀ Z n₀ [] b' s') s' :=
    fun zs' hz' r s' ⟨hp, hi'⟩ => Impl.pure_of (I.of_post hz hz' hp hi')
  by_cases hx : x = .checkpoint
  · subst hx
    rw [hck, ← Prog.bind_assoc']
    refine Impl.bind _ _ _ _ ?_
    have hitem' : s.μ.readN (sp + 176) 2 = fixed 2 item := by
      rw [← hitem]; exact Memory.readN_congr fun j hj => I.stab _ (by omega) (by unfold StableKeep; omega)
    have hpk : s.μ.readN (sp + 312) 32 = μ₀.readN (sp + 312) 32 :=
      Memory.readN_congr fun j hj => I.stab _ (by omega) (by unfold StableKeep; omega)
    have B1 := il_body_ck (P := P) env B hL hR hH hP hE hO cap hcap1 hcap hAb1 hAb2 hAbX Inv hIst hIfit s st sp item
      kc xs rs zs (I.hi.imp_right fun h => ⟨h.1, h.2.1⟩) I.h1 hs8 LA I.hal hk1 hjt' hjr' hinvS hitem'
      (by rw [← mkc]; exact Memory.readN_congr fun j hj => (I.ro _ (by omega)).1) hkc
      (by rw [← ht8]; exact rdN_frame fun j hj => (I.ro _ (by omega)).1)
      (by rw [← ht4]; exact rdN_frame fun j hj => (I.ro _ (by omega)).1)
      (fun a h1 h2 => by rw [(I.ro a (by omega)).2]; exact hro a h1 h2) (hBall rs (by omega))
    rw [hpk] at B1
    have B2 := Impl.inv (fun _ => True) Inv (fun o c c₁ b _ => hIst o c c₁ b) _ _ (Prog.all_true _) hinvS B1
    exact Impl.mono_post (fun r s' h => post zs (by simp [isZomb]) r s' h) _ _ B2
  · rw [hother x rs hx]
    refine Impl.bind _ _ _ _ ?_
    have B1 := il_body (P := P) env B hL hR hH hP hAbX s st sp x xs rs zs (I.hi.imp_right fun h => ⟨h.1, h.2.1⟩) I.h1 hs8 LA I.hal hk1 hjt' hjr' hfit
      (fun h => hx (idx15 h))
    have B2 := Impl.inv (fun _ => True) Inv (fun o c c₁ b _ => hIst o c c₁ b) _ _ (Prog.all_true _) hinvS B1
    exact Impl.mono_post (fun r s' h => post _ (by rw [idx3]) r s' h) _ _ B2

end Services.Bootstrap.Acc.Handlers.InstrLoop
