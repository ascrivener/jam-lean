import Services.Bootstrap.Acc.Handlers.RecentCounter
import Services.Bootstrap.Acc.Handlers.NoCall
import Services.Bootstrap.Acc.Wrappers.GrowS
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.ASemLemmas

/-!
# `add_recent_work_item`'s counter write as an `Impl` step (8326 → 8416)

`counter_write`: from 8326 with the new counter's register value w in ω₇, the run implements spec
`store .counter (fixed 4 w)` (`addRecent`'s last line; GP v0.8.0 Appendix B's Ω_W) in `Impl`'s call
form:
- up to `set`'s call (48104) the context is kept: the key encoder (`kb_call`, whose `alloc` may fail:
  the trap at 34070, the `heap` abort reason) and the argument set-up;
- `set` (`set_call`) is Ω_W of `[0]` with ℰ₄(w), the context becoming `ASem.step`'s;
- after it, `dealloc` of the key's buffer, then `Ok` goes on to 8416 (`CwPost`) and `Err` (FULL) to
  the trap at 15361, as `orPanic` panics.

Hypotheses: the key-size table's word for tag 0 (68680) and `set`'s two error-table entries (69056,
69072) in read-only data, readable; the old value under `[0]` shorter than 2⁶³ octets (`ValuesFit`).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentCounter

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc

open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The octets above sp the counter write may change: the result word's save slot (sp + 232), `set`'s
    out (sp + 744, 16 octets), the value (sp + 1000, 4), the key's `Vec` (sp + 1144, 24) and the key
    value (sp + 1568, 2). -/
def CwOut (sp a : Nat) : Prop :=
  (sp + 232 ≤ a ∧ a < sp + 240) ∨ (sp + 744 ≤ a ∧ a < sp + 760) ∨ (sp + 1000 ≤ a ∧ a < sp + 1004) ∨
    (sp + 1144 ≤ a ∧ a < sp + 1168) ∨ (sp + 1568 ≤ a ∧ a < sp + 1570)

/-- **The state after the counter write** (8416), against the memory μ₀ and allocator state st at
    8326: ω₁ = sp; the allocator's context for some state st′ keeping every allocated chunk of st
    with its data; memory kept above sp off `CwOut`, at the globals 196616 … 196791 (the protocol
    parameters' statics among them) and below 196608 (read-only data). -/
def CwPost (code : ByteArray) (pb S0 S1 sp : Nat) (st : State) (μ₀ : Memory) (s' : St Stream) : Prop :=
  s'.i = 8416 ∧ s'.ω[1] = UInt64.ofNat sp ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → sp ≤ a → ¬ CwOut sp a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ₀.read a) ∧ (∀ a, a < 196608 → s'.μ.read a = μ₀.read a)

/-- The trap at 34070 (`handle_alloc_error`): ☇ (GP §A.5.1). -/
theorem trap_34070 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 34070 ω μ .panic ω μ := by
  have hd := d_34070 (p := p) (P := P)
  have hs : P.freeStep 34070 ω μ = (.panic, P.next 34070, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- A run keeping the context is a run of `YIn a b` when y = a. -/
theorem keep_yin {p : ByteArray} {R : HostRel (AccCtx × Stream)} {a b : JAM.Implications}
    {i ω μ x i' ω' μ' x' n} (h : FreeStepsH p (KeepCtx R) i ω μ x i' ω' μ' x' n) (ha : x.1.2 = a) :
    FreeStepsH p (YIn R a b) i ω μ x i' ω' μ' x' n := by
  revert ha
  induction h with
  | refl => exact fun _ => .refl
  | pad _ ih => exact fun ha => .pad (ih ha)
  | next hn hc _ ih => exact fun ha => .next hn hc (ih ha)
  | host hP hc hst hr _ ih =>
    exact fun ha => .host hP hc hst ⟨hr.1, .inl (by rw [hr.2]; exact ha)⟩ (ih (by rw [hr.2]; exact ha))

open Services.Bootstrap.Decode.DeallocCall in
/-- **From `set`'s return to 8402**, under any host relation: `set`'s return (ω₀ = 290) to 8376, the
    result word r (at sp + 744) saved at sp + 232, and `dealloc` of the key's buffer (the chunk at
    ptr − 32 of ⌈kc/32⌉ + 1 units, kc ≠ 0 the capacity at sp + 1144), returning to 8402. The context
    is kept for `free s ptr`; memory is kept above sp but at sp + 232, at the globals, below 196608,
    and in every other allocated chunk's data. -/
theorem cw_free {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr kc r e : Nat)
    (H : HeapCtxC code pb S0 S1 μ s) (hnew : (⟨ptr - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s)
    (hptr : 32 ≤ ptr) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 290)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp ∧ sp + 1576 < 4294967296) (hS : S0 + 40 ≤ sp ∧ sp + 1576 ≤ S1)
    (hkc : kc < 18446744073709551616) (hc0 : kc ≠ 0) (hr64 : r < 18446744073709551616)
    (mc : μ.readN (sp + 1144) 8 = Num.encodeLE 8 kc) (mr : μ.readN (sp + 744) 8 = Num.encodeLE 8 r) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 8402 ω' μ' x 257 ∧ ω'[1] = UInt64.ofNat sp ∧
      HeapCtxC code pb S0 S1 μ' (free s ptr) ∧ μ'.readN (sp + 232) 8 = Num.encodeLE 8 r ∧
      (∀ a, sp + 232 ≤ a → a < sp + 240 → μ'.readable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 232 ∨ sp + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (kc + 31) / 32 + 1, true⟩ →
        d ∈ chunks (free s ptr) ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
  have hst := H.st
  have hS1 := H.hS1
  have run5 := cw_ret (P := P) (R := R) x ω μ e he h0
  obtain ⟨ω6, run6, e0, e1, e5, e7⟩ := cw_dl (P := P) (R := R) x ω μ sp kc r h1 hsp.2 hkc hc0 hr64 mc mr
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hst a (by omega) (by omega))
  have l8 : (Num.encodeLE 8 r).length = 8 := Num.length_encodeLE ..
  have fr6 : ∀ a, a < 4294967296 → (a < sp + 232 ∨ sp + 240 ≤ a) →
      (μ.writeN (sp + 232) (Num.encodeLE 8 r)).read a = μ.read a := fun a h0 ha =>
    rd_wr _ _ _ _ 8 l8 (by omega) (by omega) h0
  have wr6 : ∀ a, (μ.writeN (sp + 232) (Num.encodeLE 8 r)).writable a = μ.writable a := fun a =>
    Memory.writable_writeN _ _ _ _
  have H6 : HeapCtxC code pb S0 S1 (μ.writeN (sp + 232) (Num.encodeLE 8 r)) s :=
    HeapKeep.keepHi H (fun a ha => fr6 a (by omega) (.inl (by omega))) wr6
  obtain ⟨ω7, μ7, run7, H7, -, -, ro7, stk7, gl7, keep7, g0, g1, -, -⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω6 _ s sp ptr 292 8402 _ H6 hnew rfl
      (by dsimp only; omega) e0 e1 (e7.trans h5) ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_145]) bs_8402 hsp.1 ⟨hS.1, by omega⟩
  have m232 : (μ.writeN (sp + 232) (Num.encodeLE 8 r)).readN (sp + 232) 8 = Num.encodeLE 8 r :=
    Memory.readN_writeN_same _ _ _ _ l8 (by unfold two32; omega)
  refine ⟨ω7, μ7, ((run5.trans run6).trans run7).mono (by omega), g1.trans e1, H7, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← m232]; exact Memory.readN_congr fun j hj => stk7 _ (by omega) (by omega)
  · intro a h1 h2; exact Memory.readable_of_writable (H7.st a (by omega) (by omega))
  · intro a h0 ha hb; rw [stk7 a h0 ha, fr6 a h0 hb]
  · intro a ha; unfold Glob at ha; rw [gl7 a ha, fr6 a (by omega) (.inl (by omega))]
  · intro a ha
    rw [ro7 a (by unfold two32; omega) (by rw [wr6]; exact H.ro a ha), fr6 a (by omega) (.inl (by omega))]
  · intro d hd hu hne
    obtain ⟨k1, k2⟩ := keep7 d hd hu hne
    refine ⟨k1, fun a ha => ?_⟩
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have := H.hbT
    unfold InData at ha
    rw [k2 a ha, fr6 a (by omega) (.inl (by omega))]

/-- **The counter write, 8326 → 8416, implements `store .counter (fixed 4 w)`** (spec `addRecent`'s
    last line), for the register value w in ω₇, from the allocator's context for st, under
    `accContractS` with any abort reasons `Ab` that cover the trap at 34070 (`alloc` failed: heap
    exhaustion). `Ok` ends in `CwPost` (8416); FULL ends ☇ at 15361, as `orPanic` does.
    Hypotheses: the key-size table's word kc for tag 0 at 68680 (1 ≤ kc, kc + 31 < 2³⁶) and `set`'s
    error-table entries at 69056 and 69072, read-only data, readable; the stack frame [sp − 240,
    sp + 1856) in the stack; the old value under `[0]` shorter than 2⁶³ octets (`ValuesFit`). -/
theorem counter_write {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb : ∀ s : St Stream, s.i = 34070 → Ab s)
    (s : St Stream) (st : State) (sp w kc pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 s.μ st)
    (hi : s.i = 8326) (h1 : s.ω[1] = UInt64.ofNat sp) (h7 : s.ω[7] = UInt64.ofNat w)
    (hw64 : w < 18446744073709551616)
    (hsp : 2147483648 + 240 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 240 ≤ sp) (hS1 : sp + 1856 ≤ S1)
    (mc : s.μ.readN 68680 8 = Num.encodeLE 8 kc) (hkc : 1 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true)
    (hold : ∀ v, s.c.1.self.storage.get? [0] = some v → v.length < 2 ^ 63) :
    Impl p (accContractS env) env Ab (store .counter (fixed 4 w))
      (fun _ => CwPost env.code pb S0 S1 sp st s.μ) s := by
  obtain ⟨i, ω, μ, c, f⟩ := s
  dsimp only at hi h1 h7 H mc ht8 ht4 hro hold ⊢
  subst hi
  have hSt := H.st
  have hS1' := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  -- 8326 → 33843
  obtain ⟨ωA, runA, a0, a1, a7, a8⟩ := cw_pre (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp w
    h1 h7 hw64 (by omega) (fun a ha => hSt a (by omega) (by omega))
  have l2 : (Num.encodeLE 2 0).length = 2 := Num.length_encodeLE ..
  have l4 : (Num.encodeLE 4 w).length = 4 := Num.length_encodeLE ..
  have frA : ∀ a, a < 4294967296 → (a < sp + 1000 ∨ sp + 1004 ≤ a) → (a < sp + 1568 ∨ sp + 1570 ≤ a) →
      ((μ.writeN (sp + 1568) (Num.encodeLE 2 0)).writeN (sp + 1000) (Num.encodeLE 4 w)).read a = μ.read a :=
    fun a h0 ha hb => by rw [rd_wr _ _ _ _ 4 l4 (by omega) (by omega) h0, rd_wr _ _ _ _ 2 l2 (by omega) (by omega) h0]
  generalize hμA : (μ.writeN (sp + 1568) (Num.encodeLE 2 0)).writeN (sp + 1000) (Num.encodeLE 4 w) = μA at runA frA
  have wrA : ∀ a, μA.writable a = μ.writable a := fun a => by
    rw [← hμA, Memory.writable_writeN, Memory.writable_writeN]
  have rdA : ∀ a, μA.readable a = μ.readable a := fun a => by
    rw [← hμA, Memory.readable_writeN, Memory.readable_writeN]
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega)) (.inl (by omega))) wrA
  have mt : μA.readN (sp + 1568) 2 = Num.encodeLE 2 0 := by
    rw [← hμA, Memory.readN_congr (μ' := (μ.writeN (sp + 1568) (Num.encodeLE 2 0)).writeN (sp + 1000) _)
      (μ := μ.writeN (sp + 1568) (Num.encodeLE 2 0)) (fun j hj => rd_wr _ _ _ _ 4 l4 (by omega) (by omega) (by omega))]
    exact Memory.readN_writeN_same _ _ _ _ l2 (by unfold two32; omega)
  have mv : μA.readN (sp + 1000) 4 = Num.encodeLE 4 w := by
    rw [← hμA]; exact Memory.readN_writeN_same _ _ _ _ l4 (by unfold two32; omega)
  have mcA : μA.readN (68680 + 8 * 0) 8 = Num.encodeLE 8 kc := by
    rw [← mc]; exact Memory.readN_congr fun j hj => frA _ (by omega) (.inl (by omega)) (.inl (by omega))
  have hk0 : keyEnc μA (sp + 1568) 0 = [0] := by simp [keyEnc]
  -- the call as `Impl`'s call form
  unfold store orPanic
  refine Impl.bind _ _ _ _ ?_
  unfold Prog.op Impl
  -- the key encoder
  rcases kb_call (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ωA μA st sp (sp + 1568) (sp + 1144) 0 kc
      288 8348 pb S0 S1 HA a0 a1 a7 a8 hsp ⟨hS0, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) mt mcA (fun a h1 h2 => by rw [rdA]; exact hro a (by omega) (by omega))
      ⟨by rw [hk0]; simp only [List.length_cons, List.length_nil]; omega, hkc.2⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_143]) bs_8348 with
    ⟨ptr, s1, ωB, μB, nB, -, runB, HB, keepB, hnew, hfresh, oB0, oB8, oB16, oBk, hgB, stkB, b0, b1, b5, b6⟩ |
    ⟨-, ωB, μB, nB, runB⟩
  case inr =>
    -- `alloc` failed: the trap at 34070
    obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
    exact .inl ⟨⟨34070, ωB, μB, c, f⟩, ⟨_, runA.trans runBS⟩, hAb _ rfl, ωB, μB, f,
      .exit (FreeRun.exit (trap_34070 (P := P) ωB μB)) (by simp)⟩
  obtain ⟨roB1, roB2⟩ := HeapHost.keepRO (env := accHeapHost env) HA.bd runB
  obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
  rw [hk0] at oBk oB16
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at oBk oB16
  have hS1B := HB.hS1
  have hb0B := HB.hb0
  have hbTB := HB.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HB.wf hnew rfl
  dsimp only at n1 n2 n3
  have hdiv : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- 8348 → 48104
  obtain ⟨ωC, runC, c0, c1, c5, c7, c8, c9, c10, c11⟩ := cw_mid (P := P) (R := KeepCtx (accContractS env)) (c, f)
    ωB μB sp ptr 1 (b1.trans a1) (by omega) (by omega) (by decide)
    (by rw [show sp + 1152 = sp + 1144 + 8 by omega]; exact oB8)
    (by rw [show sp + 1160 = sp + 1144 + 16 by omega]; exact oB16)
    (fun a h1 h2 => Memory.readable_of_writable (HB.st a (by omega) (by omega)))
  refine .inr ⟨⟨48104, ωC, μB, c, f⟩, ⟨_, (runA.trans runBS).trans runC⟩, rfl, ?_⟩
  -- `set`
  have hkB : μB.readN ptr 1 = [0] := oBk
  have hvB : μB.readN (sp + 1000) 4 = Num.encodeLE 4 w := by
    rw [← mv]; exact Memory.readN_congr fun j hj => stkB _ (by omega) (by omega) (.inl (by omega))
  have kROB : ∀ a, a < 196608 → μB.read a = μ.read a := fun a ha => by
    rw [roB2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (by rw [wrA]; exact H.ro a ha),
      frA a (by omega) (.inl (by omega)) (.inl (by omega))]
  have rdB : ∀ a, a < 196608 → μB.readable a = μ.readable a := fun a ha => by
    rw [← rdA]; unfold Memory.readable; rw [roB1 (a / pageSize) (.inl (by unfold pageSize; omega))]
  have ht8B : rdN μB 69072 4 = 4294900408 := by
    rw [← ht8]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kROB _ (by omega)
  have ht4B : rdN μB 69056 4 = 4294900402 := by
    rw [← ht4]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kROB _ (by omega)
  have hkr : μB.rangeReadable ptr 1 = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HeapKeep.writableData HB hnew rfl
      (by unfold HeapKeep.InData; dsimp only; omega))) (by omega)
  have hvr : μB.rangeReadable (sp + 1000) 4 = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HB.st a (by omega) (by omega))) (by omega)
  obtain ⟨e, ωD, μD, he, runD, d0, d1, d5, d6, sO, frD, rdD, wrD⟩ := set_call (P := P) env c f ωC μB sp (sp + 744)
    ptr 1 (sp + 1000) 4 [0] (fixed 4 w) c1 c7 c8 c9 c10 c11 (by decide) (by decide) (by omega) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => HB.st a (by omega) (by omega))
    (fun a h1 h2 => HB.st a (by omega) (by omega)) (.inr (by omega)) hkr hkB hvr hvB l4 (.inl (by omega))
    (.inr (by omega)) ht8B ht4B (fun a h1 h2 => by rw [rdB a (by omega)]; exact hro a (by omega) (by omega))
    (by omega) hold
  have HD : HeapCtxC env.code pb S0 S1 μD s1 :=
    HeapKeep.keepHi HB (fun a ha => frD a (by omega) (.inl (by omega)) (.inl (by omega))) wrD
  have kD : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → (a < sp + 744 ∨ sp + 760 ≤ a) →
      μD.read a = μB.read a := frD
  have mcD : μD.readN (sp + 1144) 8 = Num.encodeLE 8 kc := by
    rw [← oB0]; exact Memory.readN_congr fun j hj => kD _ (by omega) (.inr (by omega)) (.inr (by omega))
  -- the rest from `set`'s return, for its result word r
  have rest : ∀ r, r < 18446744073709551616 → μD.readN (sp + 744) 8 = Num.encodeLE 8 r →
      ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) e ωD μD
        ((c.1.setSelf (writeSelf c.1.self [0] (fixed 4 w)), c.2), f) 8402 ω' μ'
        ((c.1.setSelf (writeSelf c.1.self [0] (fixed 4 w)), c.2), f) 257 ∧ ω'[1] = UInt64.ofNat sp ∧
        μ'.readN (sp + 232) 8 = Num.encodeLE 8 r ∧ (∀ a, sp + 232 ≤ a → a < sp + 240 → μ'.readable a = true) ∧
        CwPost env.code pb S0 S1 sp st μ ⟨8416, ω', μ', c, f⟩ := by
    intro r hr mr
    obtain ⟨ωG, μG, runG, g1, HG, mG, rG, stkG, glG, roG, keepG⟩ := cw_free (P := P)
      (R := KeepCtx (accContractS env)) env.code pb S0 S1 _ ωD μD s1 sp ptr kc r e HD hnew (by omega) he
      (d0.trans c0) (d1) (d5.trans c5) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hr mcD mr
    refine ⟨ωG, μG, runG, g1, mG, rG, rfl, g1, free s1 ptr, HG, ?_, ?_, ?_, ?_⟩
    · intro d hd hu
      have hd1 := keepB d hd hu
      obtain ⟨k1, k2⟩ := keepG d hd1 hu (hfresh d hd hu)
      refine ⟨k1, fun a ha => ?_⟩
      have hap := InData.apart HB.wf hd1 hnew (Ne.symm (hfresh d hd hu)) ha
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      have hoff := Services.Bootstrap.Alloc.off_hdr_data HB.wf HB.hb0 HB.hbT hd1 ha.1 ha.2
      unfold InData at ha hap
      dsimp only at hap
      rw [k2 a ⟨ha.1, ha.2⟩, kD a (by omega) (.inl (by omega)) (.inl (by omega)),
        hgB a ⟨.inr hoff.1, hoff.2.1, hoff.2.2⟩ (by omega), frA a (by omega) (.inl (by omega)) (.inl (by omega))]
    · intro a h0 ha hc
      unfold CwOut at hc
      rw [stkG a h0 ha (by omega), kD a h0 (.inr ha) (by omega), stkB a h0 ha (by omega),
        frA a h0 (by omega) (by omega)]
    · intro a ha
      have hg := ha
      unfold Glob at hg
      rw [glG a ha, kD a (by omega) (.inl (by omega)) (.inl (by omega)),
        hgB a ⟨.inl ha, by omega, fun h ⟨d, hd, hda⟩ => by
          have ht := HB.wf.2.2.2.1
          unfold TilesOk at ht
          have := ht.mem_lt d hd; subst hda; omega⟩ (.inl (by omega)),
        frA a (by omega) (.inl (by omega)) (.inl (by omega))]
    · intro a ha
      rw [roG a ha, kD a (by omega) (.inl (by omega)) (.inl (by omega)), kROB a ha]
  -- Ω_W's outcome
  have hfit : ASem.argBase + [(0 : UInt8)].length + (fixed 4 w).length ≤ ASem.outBase := by
    simp only [fixed, Num.length_encodeLE, List.length_cons, List.length_nil]; decide
  have hsw := ASem.step_write env [0] (fixed 4 w) c hfit hold
  rw [show Key.counter.encode = [0] from rfl]
  rw [show ({ i := 8326, ω := ω, μ := μ, c := c, q := f } : St Stream).c = c from rfl, hsw]
  by_cases hF : (ASem.writeAcct c.1.self [0] (fixed 4 w)).minBalance >
      (ASem.writeAcct c.1.self [0] (fixed 4 w)).balance
  · -- FULL: `Err`, then ☇ at 15361
    rw [if_pos hF]
    dsimp only
    have hS : writeSelf c.1.self [0] (fixed 4 w) = c.1.self := by unfold writeSelf; rw [if_pos hF]
    have hR : writeR7 c.1.self [0] (fixed 4 w) = Result.FULL := by unfold writeR7; rw [if_pos hF]
    rw [hR] at sO
    unfold SetOut at sO
    rw [if_pos rfl] at sO
    obtain ⟨ωG, μG, runG, g1, mG, rG, -⟩ := rest _ (by decide) sO.1
    rw [hS] at runD runG
    refine .inr ⟨⟨e, ωD, μD, (c.1.setSelf c.1.self, c.2), f⟩, ⟨_, runD⟩, rfl, .inr ⟨_, ⟨0, .refl⟩, rfl, ?_⟩⟩
    obtain ⟨ωE, runE⟩ := cw_err (P := P) (R := KeepCtx (accContractS env)) _ ωG μG sp g1 (by omega) mG rG
    exact ⟨ωE, μG, f, (runG.trans runE).run (.exit (FreeRun.exit (Handlers.trap_15361 (P := P) ωE μG)) (by simp))⟩
  · -- `Ok`: on to 8416
    rw [if_neg hF]
    dsimp only
    have hR : writeR7 c.1.self [0] (fixed 4 w) ≠ Result.FULL ∧
        (writeR7 c.1.self [0] (fixed 4 w) = Result.NONE ∨ writeR7 c.1.self [0] (fixed 4 w) < 2 ^ 63) := by
      unfold writeR7; rw [if_neg hF]
      cases hv : c.1.self.storage.get? [0] with
      | none => simp [Result.NONE, Result.FULL]
      | some v => have := hold v hv; simp [Result.FULL]; omega
    have hS : writeSelf c.1.self [0] (fixed 4 w) = ASem.writeAcct c.1.self [0] (fixed 4 w) := by
      unfold writeSelf; rw [if_neg hF]
    unfold SetOut at sO
    rw [if_neg hR.1] at sO
    have hrw : ∃ r, r < 18446744073709551616 ∧ r ≠ 18446744073709551615 ∧
        μD.readN (sp + 744) 8 = Num.encodeLE 8 r := by
      by_cases hN : writeR7 c.1.self [0] (fixed 4 w) = Result.NONE
      · rw [if_pos hN] at sO; exact ⟨0, by decide, by decide, sO⟩
      · rw [if_neg hN] at sO; exact ⟨1, by decide, by decide, sO.1⟩
    obtain ⟨r, hr, hr1, mr⟩ := hrw
    obtain ⟨ωG, μG, runG, g1, mG, rG, post⟩ := rest r hr mr
    rw [hS] at runD runG
    refine .inr ⟨⟨e, ωD, μD, (c.1.setSelf (ASem.writeAcct c.1.self [0] (fixed 4 w)), c.2), f⟩, ⟨_, runD⟩, rfl,
      .inr ⟨_, ⟨0, .refl⟩, rfl, ?_⟩⟩
    obtain ⟨ωH, runH, h1H⟩ := cw_ok (P := P) (R := KeepCtx (accContractS env)) _ ωG μG sp r g1 (by omega) hr hr1 mG rG
    refine .inr ⟨⟨8416, ωH, μG, _, f⟩, ⟨_, runG.trans runH⟩, rfl, ?_⟩
    obtain ⟨-, -, rest'⟩ := post
    exact ⟨rfl, h1H, rest'⟩

end Services.Bootstrap.Acc.Handlers.RecentCounter
