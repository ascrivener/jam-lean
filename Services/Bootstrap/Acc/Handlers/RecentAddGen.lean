import Services.Bootstrap.Acc.Handlers.RecentMatch
import Services.Bootstrap.Acc.Impl.Impl

/-!
# Row 8's generic pieces

- `Prog.bind_assoc` and `addRecent_eq`: spec `addRecent` (GP v0.8.0 Appendix B's Ω_R and Ω_W, as
  the SDK calls them) elaborates its `match` with a join point; `addRecent_eq` restates it as the
  four `Prog.bind`s the binary runs one after another (the counter's get, the slot's read and
  removal, the slot's write, the counter's write).
- `StoreFit`: every value of this service's storage is shorter than 2⁶³ octets (`ValuesFit`).
  `Impl.inv` carries such a context invariant through `Impl` along a program whose operations keep
  it; `storeFit_step` shows `read`, `remove` and `write` of a short value keep `StoreFit`.
-/

namespace Services.Bootstrap.Spec

/-- `Prog.bind` is associative. -/
theorem Prog.bind_assoc {E : Type → Type} {α β γ : Type} (m : Prog E α) (f : α → Prog E β)
    (g : β → Prog E γ) : Prog.bind (Prog.bind m f) g = Prog.bind m (fun a => Prog.bind (f a) g) := by
  induction m with
  | pure a => rfl
  | call op k ih => simp only [Prog.bind, ih]
  | panic => rfl

/-- **`addRecent` as four binds**: the counter's get, the slot's read and removal, the slot's
    write and the counter's write (spec `addRecent`, quirks Q12, Q18, Q19). -/
theorem addRecent_eq (C : Consts) (package : Bytes) (item : Nat) :
    addRecent C package item =
      Prog.bind (load .counter (Dec.fixedN 4)) (fun o =>
        Prog.bind (Prog.bind (load (.recent (o.getD 0)) (do return (← Dec.take 32, ← Dec.fixedN 2)))
          (fun v => match v with
            | some (q, k) => Prog.op (AOp.remove (Key.results q k).encode)
            | none => Prog.pure ()))
          (fun _ => Prog.bind (store (.recent (o.getD 0)) (encodeRecent package item)) (fun _ =>
            store .counter (JAM.Codec.fixed 4 (((o.getD 0 + 1) % 2 ^ 32) % C.maxRecent))))) := by
  unfold addRecent
  show Prog.bind _ _ = Prog.bind _ _
  congr 1
  funext o
  rw [Prog.bind_assoc]
  show Prog.bind _ _ = Prog.bind _ _
  congr 1
  funext v
  rcases v with _ | ⟨q, k⟩ <;> rfl

end Services.Bootstrap.Spec

namespace Services.Bootstrap.ASem
open PVM JAM Services.Bootstrap.Spec

/-- `read` keeps the context (Ω_R, dispatched as host call 4, leaves (x, y) as they were). -/
theorem step_read_ctx (env : AccEnv) (key : Bytes) (c c₁ : AccCtx) (b : Option Bytes)
    (h : step env (.read key) c = some (b, c₁)) : c₁ = c := by
  simp only [step, twoPhase, call, AccHost.dispatch] at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    · split at h
      · simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        exact h.2.symm
      · simp at h
  · simp at h

end Services.Bootstrap.ASem

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap.Spec

variable {Qu : Type}

/-- Every operation of a program (whatever the replies) satisfies P. -/
def Prog.All (P : ∀ {β : Type}, AOp β → Prop) {α : Type} : Prog AOp α → Prop
  | .pure _ => True
  | .call op k => P op ∧ ∀ b, Prog.All P (k b)
  | .panic => True

/-- **A context invariant along `Impl`**: if every operation of `prog` keeps `Inv` (whenever it
    steps) and `Inv` holds at the start, then every state the post-condition is asked of has a
    context satisfying `Inv`. -/
theorem Impl.inv {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α : Type} {Q : α → St Qu → Prop} (P : ∀ {β : Type}, AOp β → Prop) (Inv : AccCtx → Prop)
    (hst : ∀ {β : Type} (o : AOp β) (c c₁ : AccCtx) (b : β), P o → Inv c →
      ASem.step env o c = some (b, c₁) → Inv c₁) :
    ∀ (prog : Prog AOp α) (s : St Qu), Prog.All P prog → Inv s.c → Impl p R env Ab prog Q s →
      Impl p R env Ab prog (fun a s' => Q a s' ∧ Inv s'.c) s := by
  intro prog
  induction prog with
  | pure a =>
    intro s _ hI h
    rcases h with h | ⟨s', h1, h2, h3⟩
    · exact .inl h
    · exact .inr ⟨s', h1, h2, h3, by rw [h2]; exact hI⟩
  | panic => intro s _ _ h; exact h
  | call op k ih =>
    intro s hA hI h
    unfold Impl at h ⊢
    rcases h with h | ⟨s₁, h1, h2, h3⟩
    · exact .inl h
    refine .inr ⟨s₁, h1, h2, ?_⟩
    revert h3
    cases hs : ASem.step env op s.c with
    | some bc =>
      intro h3
      rcases h3 with h3 | ⟨s₂, g1, g2, g3⟩
      · exact .inl h3
      · refine .inr ⟨s₂, g1, g2, ih bc.1 s₂ (hA.2 bc.1) ?_ g3⟩
        rw [g2]; exact hst op s.c bc.2 bc.1 hA.1 hI (by rw [hs])
    | none => exact id

/-- Every value of this service's storage is shorter than 2⁶³ octets (`ValuesFit`). -/
def StoreFit (c : AccCtx) : Prop :=
  ∀ key v, c.1.self.storage.get? key = some v → v.length < 2 ^ 63

/-- The operations of row 8 that keep `StoreFit`: `read`, and `remove` / `write` of a key and value
    that fit the operation's memory. -/
inductive SmallOp : {β : Type} → AOp β → Prop
  | read (key : Bytes) : SmallOp (.read key)
  | remove (key : Bytes) (hk : ASem.argBase + key.length ≤ ASem.outBase) : SmallOp (.remove key)
  | write (key value : Bytes) (hk : ASem.argBase + key.length + value.length ≤ ASem.outBase) :
      SmallOp (.write key value)

theorem self_setSelf (x : Implications) (a : ServiceAccount) : (x.setSelf a).self = a := by
  simp [Implications.self, Implications.setSelf]

theorem storeFit_writeAcct {a : ServiceAccount} {key value : Bytes}
    (h : ∀ k v, a.storage.get? k = some v → v.length < 2 ^ 63) (hv : value.length < 2 ^ 63) :
    ∀ k v, (ASem.writeAcct a key value).storage.get? k = some v → v.length < 2 ^ 63 := by
  intro k v hk
  unfold ASem.writeAcct at hk
  split at hk
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at hk
    split at hk
    · simp at hk
    · exact h k v hk
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hk
    split at hk
    · simp only [Option.some.injEq] at hk; rw [← hk]; exact hv
    · exact h k v hk

/-- `read`, `remove` and a short `write` keep `StoreFit`. -/
theorem storeFit_step (env : AccEnv) {β : Type} (o : AOp β) (c c₁ : AccCtx) (b : β) (ho : SmallOp o)
    (hI : StoreFit c) (hs : ASem.step env o c = some (b, c₁)) : StoreFit c₁ := by
  cases ho with
  | read key => rw [ASem.step_read_ctx env key c c₁ b hs]; exact hI
  | remove key hk =>
    rw [ASem.step_remove env key c hk (hI key)] at hs
    split at hs
    · simp at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]
      intro k v hkv
      simp only [self_setSelf, writeSelf] at hkv
      split at hkv
      · exact hI k v hkv
      · exact storeFit_writeAcct hI (by simp) k v hkv
  | write key value hk =>
    rw [ASem.step_write env key value c hk (hI key)] at hs
    have hv : value.length < 2 ^ 63 := by unfold ASem.argBase ASem.outBase at hk; omega
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]; intro k v hkv; rw [self_setSelf] at hkv; exact hI k v hkv
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs
      rw [← hs.2]; intro k v hkv; rw [self_setSelf] at hkv; exact storeFit_writeAcct hI hv k v hkv

end Services.Bootstrap.Acc
