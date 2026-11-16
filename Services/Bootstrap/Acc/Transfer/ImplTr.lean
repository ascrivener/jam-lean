import Services.Bootstrap.Acc.Transfer.ImplW1
import Services.Bootstrap.Acc.Transfer.ImplW2

/-!
# `on_transfer` as `Impl` (7159 → 6766)

Spec `onTransfer src am memo` (GP v0.8.0 §B.7, Ω_R and Ω_W; quirks Q12, Q14):
```
n ← (read "transfer-count").bind (decode (fixedN 4)) |>.getD 0
orPanic (.write "transfer-count" (fixed 4 ((n + 1) % 2 ^ 32)))
orPanic (.write s!"transfer{n}" (fixed 4 src ++ fixed 8 am ++ memo))
```

`tr_impl` composes `tr_read` (7159 → 7326, the `read`, with ASem's `step_read`), `tr_w1`
(7326 → 7399) and `tr_w2` (7399 → 6766, the items loop's head). The post-state is `TrPost`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Spec
open JAM.Codec (fixed)
open Services.Bootstrap.ASem (argBase outBase writeAcct)
set_option maxHeartbeats 8000000

/-- A value stored after `writeAcct a key v` is v or was stored before. -/
theorem writeAcct_get (a : ServiceAccount) (key v k : List UInt8) (w : List UInt8)
    (h : (writeAcct a key v).storage.get? k = some w) : w = v ∨ a.storage.get? k = some w := by
  unfold writeAcct at h
  split at h
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at h
    split at h
    · simp at h
    · exact .inr h
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at h
    split at h
    · exact .inl (Option.some.inj h).symm
    · exact .inr h

/-- x_s of x with x_s replaced by a is a. -/
theorem self_setSelf (x : Implications) (a : ServiceAccount) : (x.setSelf a).self = a := by
  unfold Implications.self Implications.setSelf
  simp

/-- The stack octets `on_transfer` changes (from sp up): `tr_read`'s, the two counters', `tr_w2`'s. -/
def TrW (sp a : Nat) : Prop :=
  TrRdW sp a ∨ (sp + 1496 ≤ a ∧ a < sp + 1500) ∨ (sp + 1568 ≤ a ∧ a < sp + 1572) ∨ TrW2 sp a

/-- The context after `onTransfer src am memo` returns: the counter and the record written. -/
def trCtx (c : AccCtx) (src am : Nat) (memo : Bytes) : AccCtx :=
  let n := trCount (c.1.self.storage.get? trKey)
  let c₁ : AccCtx := (c.1.setSelf (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))), c.2)
  (c₁.1.setSelf (writeAcct c₁.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo)), c₁.2)

/-- **The state at the items loop's head 6766 after `on_transfer`**, from 7159 with memory μ,
    allocator state s₀, context c and stream f: context `trCtx c src am memo`, stream f; sp in ω₁; the
    allocator's context for some state keeping every allocated chunk of s₀ and its data; from sp up
    only `TrW` changed; below 196608 the memory reads and is readable as before. -/
def TrPost (env : AccEnv) (pb S0 S1 sp : Nat) (s₀ : State) (μ : Memory) (c : AccCtx) (f : Stream)
    (src am : Nat) (memo : Bytes) (s' : St Stream) : Prop :=
  s'.i = 6766 ∧ s'.c = trCtx c src am memo ∧ s'.q = f ∧ s'.ω[1] = UInt64.ofNat sp ∧
  (∃ st, HeapCtxC env.code pb S0 S1 s'.μ st ∧
    ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks st ∧ ∀ a, InDataA d a → s'.μ.read a = μ.read a) ∧
  (∀ a, a < 4294967296 → sp ≤ a → ¬ TrW sp a → s'.μ.read a = μ.read a) ∧
  (∀ a, a < 196608 → s'.μ.read a = μ.read a ∧ s'.μ.readable a = μ.readable a)

set_option maxRecDepth 20000 in
/-- **`on_transfer` (7159 → 6766) implements `onTransfer src am memo`**: src = ω₁₀ mod 2³², am = ω₆,
    the memo the 128 octets at ms (ω₈). Early ☇ for any `Ab` holding at `HeapFailT` states.
    Premises: every stored value is shorter than 2⁶³ octets (`hfit`, from `ValuesFit`); the key
    "transfer-count" at 65956 and the error table at 69056 … 69076 (read-only data of the blob, see
    `accRoBytes`); the formatter words of the accumulate prologue at sp + 208 / 136 / 200.
    Named hypotheses: `Utf8Call`, `LogFmt`, `KeyFmt`. -/
theorem tr_impl (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hU : Utf8Call p env pb S0 S1) (hL : LogFmt p env pb S0 S1)
    (hK : KeyFmt p env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp ms src am : Nat) (memo : Bytes)
    (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ms)
    (hsrc : ω[10].toNat % 4294967296 = src) (ham : ω[6].toNat = am) (hmemo : μ.readN ms 128 = memo)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1)
    (hms : 65536 ≤ ms ∧ ms + 128 + 24 ≤ sp - 88)
    (hmr : ∀ a, ms ≤ a → a < ms + 128 → μ.readable a = true)
    (hkey : μ.readN 65956 14 = trKey) (hkr : ∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true)
    (ht8 : rdN μ 69072 4 = 4294900408) (ht4 : rdN μ 69056 4 = 4294900402)
    (htr : ∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)
    (m208 : rdN μ (sp + 208) 8 = 2800) (m136 : rdN μ (sp + 136) 8 = 2804) (m200 : rdN μ (sp + 200) 8 = 678)
    (hfit : ∀ k w, c.1.self.storage.get? k = some w → w.length < 2 ^ 63)
    (Q : Unit → St Stream → Prop)
    (hQ : ∀ s', TrPost env pb S0 S1 sp s₀ μ c f src am memo s' → Q () s') :
    Impl p (accContractS env) env Ab (onTransfer src am memo) Q ⟨7159, ω, μ, c, f⟩ := by
  have hS1 := H.hS1
  have hro := H.ro
  have hfit1 : ∀ w, c.1.self.storage.get? trKey = some w → w.length < 9223372036854775808 := fun w hw => by
    have := hfit _ w hw; simp only [Nat.reducePow] at this; exact this
  have TR := tr_read env cap pb hcap1 hcap (p := p) (P := P) (hb := 0) c f ω μ s₀ sp ms S0 S1 H h1 h8
      ⟨by omega, hsp.2⟩ ⟨by omega, hSTk.2⟩ hms hmr hkey hkr hfit1
  refine Or.elim TR (fun TR => ?_) (fun TR => ?_)
  rotate_left
  · obtain ⟨t, ω1, μ1, N1, ht, run1⟩ := TR
    exact Impl.abort _ Q (aborts_of_trap (P := P) (fun s h => hAb s (.inl h)) ⟨7159, ω, μ, c, f⟩ ht run1)
  obtain ⟨s1, ω1, μ1, N1, run1, e1, e6, H1, keep1, mm1, m472, m1000, -, hv31, fr1⟩ := TR
  -- the read's step
  have hkl : trKey.length = 14 := by rw [← hkey]; exact Memory.length_readN _ _ _
  have hk : argBase + trKey.length ≤ outBase := by rw [hkl]; unfold argBase outBase; omega
  have estep := ASem.step_read env trKey c hk hv31
  have roK := ro_keep (keepCtx_keepsRO env H.bd) run1 hro
  show Impl p (accContractS env) env Ab
    (Prog.bind (Prog.op (AOp.read trKey)) fun v =>
      Prog.bind (orPanic (.write trKey (fixed 4 ((trCount v + 1) % 2 ^ 32)))) fun _ =>
        orPanic (.write (trKey2 (trCount v)) (fixed 4 src ++ fixed 8 am ++ memo))) Q ⟨7159, ω, μ, c, f⟩
  refine impl_call_keep (AOp.read trKey) _ Q _ ⟨7326, ω1, μ1, c, f⟩ estep ⟨N1, run1⟩ rfl ?_
  refine Impl.bind _ Q _ _ ?_
  generalize hn : trCount (c.1.self.storage.get? trKey) = n
  have hn32 : n < 4294967296 := hn ▸ trCount_lt _
  have tw1 := tr_w1 env cap pb hcap1 hcap (p := p) (P := P) hAb c f ω1 μ1 s1 sp S0 S1 H1 e1 e6
    ⟨by omega, hsp.2⟩ ⟨by omega, hSTk.2⟩
    (by rw [Memory.readN_congr fun j hj => (roK _ (by omega)).1]; exact hkey)
    (fun a h1 h2 => by rw [(roK a (by omega)).2.1]; exact hkr a h1 h2)
    (by rw [rdN_frame fun j hj => (roK _ (by omega)).1]; exact ht8)
    (by rw [rdN_frame fun j hj => (roK _ (by omega)).1]; exact ht4)
    (fun a h1 h2 => by rw [(roK a (by omega)).2.1]; exact htr a h1 h2)
    hfit1
  rw [hn] at tw1
  refine tw1 _ fun s' hW => ?_
  obtain ⟨i2, ω2, μ2, c2, f2⟩ := s'
  obtain ⟨hi, hc, hq, w1, -, -, ⟨st, H2, keep2⟩, r1496, -, fr2, ro2, g2⟩ := hW
  dsimp only at hi hc hq w1 H2 keep2 r1496 fr2 ro2 g2
  subst hi c2 f2
  -- from 7326's memory back to μ
  have k21 : ∀ a, a < 4294967296 → sp ≤ a → ¬ TrRdW sp a → (a < sp + 1496 ∨ sp + 1500 ≤ a) →
      (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ2.read a = μ.read a := fun a h0 ha hr hb hc =>
    (fr2 a h0 ha hb hc).trans (fr1 a h0 ha hr)
  have ro21 : ∀ a, a < 196608 → μ2.read a = μ.read a ∧ μ2.readable a = μ.readable a := fun a ha =>
    ⟨(ro2 a ha).1.trans (roK a ha).1, (ro2 a ha).2.trans (roK a ha).2.1⟩
  have hold : ∀ v, ((c.1.setSelf (writeAcct c.1.self trKey (fixed 4 ((n + 1) % 2 ^ 32))), c.2) :
      AccCtx).1.self.storage.get? (trKey2 n) = some v → v.length < 2 ^ 63 := fun v hv => by
    dsimp only at hv
    rw [self_setSelf] at hv
    rcases writeAcct_get _ _ _ _ _ hv with rfl | h
    · rw [show (fixed 4 ((n + 1) % 2 ^ 32)).length = 4 from Num.length_encodeLE _ _]; simp only [Nat.reducePow]; omega
    · exact hfit _ _ h
  refine tr_w2 env cap pb hcap1 hcap (p := p) (P := P) hAb hU hL hK _ f ω2 μ2 st sp n src am memo H2 w1
    hsp hSTk
    (by rw [rdN_frame fun j hj => k21 _ (by omega) (by omega) (by unfold TrRdW; omega) (by omega) (by omega)]
        exact m208)
    (by rw [rdN_frame fun j hj => k21 _ (by omega) (by omega) (by unfold TrRdW; omega) (by omega) (by omega)]
        exact m136)
    (by rw [rdN_frame fun j hj => k21 _ (by omega) (by omega) (by unfold TrRdW; omega) (by omega) (by omega)]
        exact m200)
    r1496 hn32
    (by rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega), m472, hsrc])
    (by rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega), m1000, ham])
    (by rw [Memory.readN_congr fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega), mm1, hmemo])
    (by rw [rdN_frame fun j hj => (ro21 _ (by omega)).1]; exact ht8)
    (by rw [rdN_frame fun j hj => (ro21 _ (by omega)).1]; exact ht4)
    (fun a h1 h2 => by rw [(ro21 a (by omega)).2]; exact htr a h1 h2)
    hold Q fun s' hW => ?_
  obtain ⟨hi3, hc3, hq3, w13, ⟨st3, H3, keep3⟩, fr3, ro3, g3⟩ := hW
  refine hQ s' ⟨hi3, by rw [hc3, ← hn]; rfl, hq3, w13, ⟨st3, H3, fun d hd hu => ?_⟩,
    fun a h0 ha hW => ?_, fun a ha => ⟨(ro3 a ha).1.trans (ro21 a ha).1, (ro3 a ha).2.trans (ro21 a ha).2⟩⟩
  · obtain ⟨hd1, hdat1⟩ := keep1 d hd hu
    obtain ⟨hd2, hdat2⟩ := keep2 d hd1 hu
    obtain ⟨hd3, hdat3⟩ := keep3 d hd2 hu
    exact ⟨hd3, fun a ha => (hdat3 a ha).trans ((hdat2 a ha).trans (hdat1 a ha))⟩
  · simp only [TrW, not_or] at hW
    obtain ⟨n1, n2, n3, n4⟩ := hW
    rw [fr3 a h0 ha n4]
    exact k21 a h0 ha n1 (by omega) (by omega)

end Services.Bootstrap.Acc
