import Services.Bootstrap.Acc.Handlers.RecentAddGen
import Services.Bootstrap.Acc.Handlers.RecentCounterGetCall
import Services.Bootstrap.Acc.Handlers.RecentSlotWriteImpl
import Services.Bootstrap.Acc.Impl.Loop

/-!
# Row 8: `add_recent_work_item`, 8013 → 8416

`add_recent`: from 8013 the run implements spec `addRecent` (`addRecent_eq`'s four binds) in
`Impl`'s form, ending at 8416 (`AddPost`). The four parts: `counter_get` (8013 → 8056, the
counter's typed get), `recent_match` (8056 → 8172, the slot's read and the removal of the results
it names), `slot_write` (8172 → 8326) and `counter_write` (8326 → 8416). `StoreFit` (`ValuesFit`
for this service's storage) is carried through the first two writes by `Impl.inv`.
-/

namespace Services.Bootstrap.Acc.Handlers.RecentAdd

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
open Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Decode.HeapCtx
open Services.Bootstrap.Acc.Handlers Services.Bootstrap.Alloc Services.Bootstrap.Acc.Handlers.HeapKeep
open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The octets above sp row 8 may change: those of the slot's read and removal (`RmOut`, which
    covers the counter get's key value), of the slot write (`SwOut`) and of the counter write
    (`CwOut`). -/
def AddOut (sp a : Nat) : Prop :=
  RecentMatch.RmOut sp a ∨ RecentSlotWrite.SwOut sp a ∨ RecentCounter.CwOut sp a

/-- **The state after row 8** (8416), against the memory μ₀ and allocator state st at 8013: ω₁ = sp;
    the allocator's context for some st′ keeping every allocated chunk of st with its data; memory
    kept above sp off `AddOut`, at the globals 196616 … 196791 and below 196608. -/
def AddPost (code : ByteArray) (pb S0 S1 sp : Nat) (st : State) (μ₀ : Memory) (s' : St Stream) : Prop :=
  s'.i = 8416 ∧ s'.ω[1] = UInt64.ofNat sp ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → sp ≤ a → ¬ AddOut sp a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ₀.read a) ∧ (∀ a, a < 196608 → s'.μ.read a = μ₀.read a)

theorem load_congr {α : Type} {k₁ k₂ : Key} (h : k₁.encode = k₂.encode) (p : Dec α) :
    load k₁ p = load k₂ p := by
  unfold load; rw [h]

theorem store_congr {k₁ k₂ : Key} (h : k₁.encode = k₂.encode) (v : Bytes) : store k₁ v = store k₂ v := by
  unfold store; rw [h]

theorem recent_mod (c : Nat) : (Key.recent (c % 4294967296)).encode = (Key.recent c).encode := by
  simp only [Key.encode, fixed]
  rw [show (4294967296 : Nat) = 256 ^ 4 from rfl, encodeLE_mod]

theorem fixed4_mod (w : Nat) : fixed 4 (w % 4294967296) = fixed 4 w := by
  simp only [fixed]; rw [show (4294967296 : Nat) = 256 ^ 4 from rfl, encodeLE_mod]

/-- The slot's read and removal use only `read` and the `remove` of a 35-octet key. -/
theorem all_match (c : Nat) :
    Prog.All SmallOp (Prog.bind (load (.recent c) RecentSlot.slotDec) (fun v => match v with
        | some (q, k) => Prog.op (AOp.remove (Key.results q k).encode)
        | none => Prog.pure ())) := by
  refine ⟨.read _, fun b => ?_⟩
  show Prog.All SmallOp (match b.bind (decode RecentSlot.slotDec) with
    | some (q, k) => Prog.op (AOp.remove (Key.results q k).encode)
    | none => Prog.pure ())
  rcases b with _ | w
  · trivial
  · by_cases hw : 34 ≤ w.length
    · show Prog.All SmallOp (match decode RecentSlot.slotDec w with
        | some (q, k) => Prog.op (AOp.remove (Key.results q k).encode)
        | none => Prog.pure ())
      rw [RecentSlot.slotDec_long w hw]
      refine ⟨.remove _ ?_, fun _ => trivial⟩
      simp only [Key.encode, fixed, List.length_append, List.length_take, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, ASem.argBase, ASem.outBase]
      omega
    · show Prog.All SmallOp (match decode RecentSlot.slotDec w with
        | some (q, k) => Prog.op (AOp.remove (Key.results q k).encode)
        | none => Prog.pure ())
      rw [RecentSlot.slotDec_short w (by omega)]
      trivial

/-- The slot write uses only the `write` of a 5-octet key and a 34-octet value. -/
theorem all_store (c : Nat) (v : Bytes) (hv : v.length = 34) :
    Prog.All SmallOp (store (.recent c) v) := by
  refine ⟨.write _ _ ?_, fun b => ?_⟩
  · simp only [Key.encode, fixed, List.length_append, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, hv, ASem.argBase, ASem.outBase]
    omega
  · rcases b with _ | _ <;> trivial

/-- **Row 8, `add_recent_work_item`, 8013 → 8416, implements spec `addRecent`** (GP v0.8.0
    Appendix B: Ω_R for the counter and the slot, Ω_W for the removal and both writes; quirks Q12,
    Q18, Q19) for the package the 32 octets at sp + 512 and the item whose ℰ₂ is the two octets at
    sp + 176, from the allocator's context for st, under `accContractS` with any abort reasons `Ab`
    that cover the allocation-failure traps 34070, 47977 and 32584 (heap exhaustion). The end state
    satisfies `AddPost` (8416). Hypotheses: the key-size words kc₀ (tag 0, at 68680) and kc₁ (tag 1,
    at 68688) and `set`'s error-table entries at 69056 and 69072, read-only data, readable; the stack
    frame [sp − 352, sp + 1856); `ParamStatics μ C I` (an obligation: `apply()`'s stores, see
    docs/whats-proven.md), `RingFits C I` and maxRecent = 2·𝖢·𝖨; every value of this service's
    storage shorter than 2⁶³ octets (`ValuesFit`). -/
theorem add_recent {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 34070 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 47977 → Ab s) (hAb3 : ∀ s : St Stream, s.i = 32584 → Ab s)
    (Cs : Consts) (item : Nat)
    (s : St Stream) (st : State) (sp kc0 kc1 C I pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 s.μ st)
    (hi : s.i = 8013) (h1 : s.ω[1] = UInt64.ofNat sp)
    (hsp : 2147483648 + 352 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 352 ≤ sp) (hS1 : sp + 1856 ≤ S1)
    (mc0 : s.μ.readN 68680 8 = Num.encodeLE 8 kc0) (hkc0 : 1 ≤ kc0 ∧ kc0 + 31 < 68719476736)
    (mc1 : s.μ.readN 68688 8 = Num.encodeLE 8 kc1) (hkc1 : 5 ≤ kc1 ∧ kc1 + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true)
    (hPS : RecentSlotWrite.ParamStatics s.μ C I) (hR : RecentSlotWrite.RingFits C I)
    (hmax : Cs.maxRecent = 2 * C * I)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab (addRecent Cs (s.μ.readN (sp + 512) 32) item)
      (fun _ => AddPost env.code pb S0 S1 sp st s.μ) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 H mc0 mc1 ht8 ht4 hro hPS hitem hvals ⊢
  subst hi
  have hb0 := H.hb0
  have hS1H := H.hS1
  rw [addRecent_eq]
  refine Impl.bind _ _ _ _ ?_
  show Impl p (accContractS env) env Ab (Prog.call (AOp.read Key.counter.encode)
    (fun v => Prog.pure (v.bind (decode (Dec.fixedN 4))))) _ _
  unfold Impl
  rcases RecentCounterGet.counter_get (P := P) env cap hcap1 hcap c0 f ω μ st sp kc0 pb S0 S1 H h1 hsp hS0
      (by omega) mc0 hkc0 (fun a h1 h2 => hro a h1 (by omega)) (fun w hw => hvals _ w hw) with
    ⟨st₁, ω₁, μ₁, n₁, run₁, b1, -, b5, H₁, keep₁, fr₁, gl₁, lo₁, rd₁, bd₁⟩ | ⟨e, ωB, μB, nB, he, runB⟩
  rotate_left
  · rcases he with rfl | rfl
    · exact .inl ⟨⟨34070, ωB, μB, c0, f⟩, ⟨nB, runB⟩, hAb1 _ rfl, ωB, μB, f,
        .exit (FreeRun.exit (RecentCounter.trap_34070 (P := P) ωB μB)) (by simp)⟩
    · exact .inl ⟨⟨47977, ωB, μB, c0, f⟩, ⟨nB, runB⟩, hAb2 _ rfl, ωB, μB, f,
        .exit (FreeRun.exit (RecentMatch.trap_47977 (P := P) ωB μB)) (by simp)⟩
  refine .inr ⟨⟨8013, ω, μ, c0, f⟩, ⟨0, .refl⟩, rfl, ?_⟩
  have hk0 : ASem.argBase + Key.counter.encode.length ≤ ASem.outBase := by
    simp only [Key.encode, List.length_cons, List.length_nil, ASem.argBase, ASem.outBase]; decide
  rw [show ({ i := 8013, ω := ω, μ := μ, c := c0, q := f } : St Stream).c = c0 from rfl,
    ASem.step_read env Key.counter.encode c0 hk0 bd₁]
  try dsimp only
  refine .inr ⟨⟨8056, ω₁, μ₁, c0, f⟩, ⟨n₁, RecentCounter.keep_yin run₁ rfl⟩, rfl, ?_⟩
  refine Impl.pure_of ?_
  -- the counter c′ and its register value cv
  generalize hcv : ω₁[5].toNat = cv at b5
  have hc' : ((c0.1.self.storage.get? Key.counter.encode).bind (decode (Dec.fixedN 4))).getD 0 =
      cv % 4294967296 := b5.symm
  rw [hc', load_congr (recent_mod cv), store_congr (recent_mod cv)]
  have hcv64 : cv < 18446744073709551616 := by rw [← hcv]; exact UInt64.toNat_lt _
  have h5₁ : ω₁[5] = UInt64.ofNat cv := by rw [← hcv]; simp
  -- the slot's read and removal
  refine Impl.bind _ _ _ _ ?_
  have mc1₁ : μ₁.readN 68688 8 = Num.encodeLE 8 kc1 := by
    rw [← mc1]; exact Memory.readN_congr fun j hj => lo₁ _ (by omega)
  have RM := RecentMatch.recent_match (P := P) env cap hcap1 hcap Ab hAb1 hAb2 ⟨8056, ω₁, μ₁, c0, f⟩ st₁ sp
    cv kc1 pb S0 S1 H₁ rfl b1 h5₁ hcv64 hsp hS0 (by omega) mc1₁ hkc1
    (fun a h1 h2 => by rw [rd₁ a (by omega)]; exact hro a (by omega) (by omega)) hvals
  refine Impl.mono_post ?_ _ _ (Impl.inv SmallOp StoreFit (storeFit_step env) _ _ (all_match cv) hvals RM)
  rintro - ⟨i₃, ω₃, μ₃, c₃, f₃⟩ ⟨⟨hi₃, b31, b35, st₃, H₃, keep₃, fr₃, gl₃, lo₃, rd₃⟩, sf₃⟩
  dsimp only at hi₃ b31 b35 H₃ keep₃ fr₃ gl₃ lo₃ rd₃ sf₃ ⊢
  subst hi₃
  -- the slot write
  have hpk : μ₃.readN (sp + 512) 32 = μ.readN (sp + 512) 32 := Memory.readN_congr fun j hj => by
    rw [fr₃ _ (by omega) (by omega) (by unfold RecentMatch.RmOut; omega),
      fr₁ _ (by omega) (by omega) (.inl (by omega))]
  have hit : μ₃.readN (sp + 176) 2 = fixed 2 item := by
    rw [← hitem]; exact Memory.readN_congr fun j hj => by
      rw [fr₃ _ (by omega) (by omega) (by unfold RecentMatch.RmOut; omega),
        fr₁ _ (by omega) (by omega) (.inl (by omega))]
  have lo31 : ∀ a, a < 196608 → μ₃.read a = μ.read a := fun a ha => by rw [lo₃ a ha, lo₁ a ha]
  have rd31 : ∀ a, a < 196608 → μ₃.readable a = μ.readable a := fun a ha => by rw [rd₃ a ha, rd₁ a ha]
  have gl31 : ∀ a, Glob a → μ₃.read a = μ.read a := fun a ha => by rw [gl₃ a ha, gl₁ a ha]
  have rn31 : ∀ a n, a + n ≤ 196608 → μ₃.readN a n = μ.readN a n := fun a n h =>
    Memory.readN_congr fun j hj => lo31 _ (by omega)
  have hPS₃ : RecentSlotWrite.ParamStatics μ₃ C I := by
    obtain ⟨p1, p2, p3, p4⟩ := hPS
    refine ⟨?_, p2, ?_, p4⟩
    · rw [← p1]; exact Memory.readN_congr fun j hj => gl31 _ ⟨by omega, by omega⟩
    · rw [← p3]; exact Memory.readN_congr fun j hj => gl31 _ ⟨by omega, by omega⟩
  have henc : encodeRecent (μ.readN (sp + 512) 32) item = μ₃.readN (sp + 512) 32 ++ μ₃.readN (sp + 176) 2 := by
    rw [hpk, hit]; rfl
  rw [henc]
  refine Impl.bind _ _ _ _ ?_
  have SW := RecentSlotWrite.slot_write (P := P) env cap hcap1 hcap Ab hAb3 hAb1 ⟨8172, ω₃, μ₃, c₃, f₃⟩ st₃ sp
    cv kc1 C I pb S0 S1 H₃ rfl b31 b35 hcv64 hsp hS0 (by omega) (by rw [rn31 _ _ (by omega)]; exact mc1) hkc1
    (by unfold rdN; rw [rn31 _ _ (by omega)]; exact ht8) (by unfold rdN; rw [rn31 _ _ (by omega)]; exact ht4)
    (fun a h1 h2 => by rw [rd31 a (by omega)]; exact hro a h1 h2) hPS₃ hR (sf₃ _)
  refine Impl.mono_post ?_ _ _ (Impl.inv SmallOp StoreFit (storeFit_step env) _ _
    (all_store cv _ (by rw [List.length_append, Memory.length_readN, Memory.length_readN])) sf₃ SW)
  rintro - ⟨i₄, ω₄, μ₄, c₄, f₄⟩ ⟨⟨hi₄, b41, b47, st₄, H₄, keep₄, fr₄, gl₄, lo₄, rd₄⟩, sf₄⟩
  dsimp only at hi₄ b41 b47 H₄ keep₄ fr₄ gl₄ lo₄ rd₄ sf₄ ⊢
  subst hi₄
  -- the counter write
  have hw : fixed 4 ((cv % 4294967296 + 1) % 2 ^ 32 % Cs.maxRecent) = fixed 4 ω₄[7].toNat := by
    rw [← fixed4_mod ω₄[7].toNat, b47, hmax]
    congr 2
    omega
  rw [hw]
  have lo41 : ∀ a, a < 196608 → μ₄.read a = μ.read a := fun a ha => by rw [lo₄ a ha, lo31 a ha]
  have rd41 : ∀ a, a < 196608 → μ₄.readable a = μ.readable a := fun a ha => by rw [rd₄ a ha, rd31 a ha]
  have rn41 : ∀ a n, a + n ≤ 196608 → μ₄.readN a n = μ.readN a n := fun a n h =>
    Memory.readN_congr fun j hj => lo41 _ (by omega)
  have CW := RecentCounter.counter_write (P := P) env cap hcap1 hcap Ab hAb1 ⟨8326, ω₄, μ₄, c₄, f₄⟩ st₄ sp
    ω₄[7].toNat kc0 pb S0 S1 H₄ rfl b41 (by simp) (UInt64.toNat_lt _) ⟨by omega, hsp.2⟩ (by omega) hS1
    (by rw [rn41 _ _ (by omega)]; exact mc0) hkc0
    (by unfold rdN; rw [rn41 _ _ (by omega)]; exact ht8) (by unfold rdN; rw [rn41 _ _ (by omega)]; exact ht4)
    (fun a h1 h2 => by rw [rd41 a (by omega)]; exact hro a h1 h2) (sf₄ _)
  refine Impl.mono_post ?_ _ _ CW
  rintro - ⟨i₅, ω₅, μ₅, c₅, f₅⟩ ⟨hi₅, b51, st₅, H₅, keep₅, fr₅, gl₅, lo₅⟩
  dsimp only at hi₅ b51 H₅ keep₅ fr₅ gl₅ lo₅ ⊢
  refine ⟨hi₅, b51, st₅, H₅, fun d hd hu => ?_, fun a h0 ha hn => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨d1, e1⟩ := keep₁ d hd hu
    obtain ⟨d3, e3⟩ := keep₃ d d1 hu
    obtain ⟨d4, e4⟩ := keep₄ d d3 hu
    obtain ⟨d5, e5⟩ := keep₅ d d4 hu
    exact ⟨d5, fun a ha => by rw [e5 a ha, e4 a ha, e3 a ha, e1 a ha]⟩
  · unfold AddOut at hn
    unfold RecentMatch.RmOut at hn
    unfold RecentSlotWrite.SwOut at hn
    unfold RecentCounter.CwOut at hn
    rw [fr₅ a h0 ha (by unfold RecentCounter.CwOut; omega), fr₄ a h0 ha (by unfold RecentSlotWrite.SwOut; omega),
      fr₃ a h0 ha (by unfold RecentMatch.RmOut; omega), fr₁ a h0 ha (by omega)]
  · rw [gl₅ a ha, gl₄ a ha, gl31 a ha]
  · rw [lo₅ a ha, lo41 a ha]

end Services.Bootstrap.Acc.Handlers.RecentAdd
