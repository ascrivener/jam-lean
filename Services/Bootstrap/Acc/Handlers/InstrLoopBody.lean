import Services.Bootstrap.Acc.Handlers.InstrLoopStep
import Services.Bootstrap.Acc.Handlers.InstrLoopTailRun
import Services.Bootstrap.Acc.Impl.ROKeepS

/-!
# R5, the instruction loop: one body (8540 → 8540)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop), for an
instruction other than `Checkpoint`: `let r ← onInstr C now i; results := results ++ [r]`.

- `il_pre` (8540 → 8822): the front (`il_front`, or `il_front_zomb` for `Zombify`, which sets the flag
  at sp + 160) and the middle (`il_mid`: the instruction's log line, `InstrLogH`, and its second copy);
- `il_body`: then the handler (`HandlerH`), and from its end 14278 the result's log line
  (`il_tail_log`, `ResultLogH`), the push (`il_tail_push`, `PushH`) and the back edge
  (`il_tail_post`), back at 8540 with `LoopAt` for the instructions left and rs ++ [r]
  (`LoopAt.step`). A failed allocation on the way is an early ☇ (`ExhaustsP`).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The first slot's buffers are among those the `IntoIter` frees. -/
theorem foot_mem_iterFree {B : InstrRep} {μ : Memory} {v : Nat} {i : Spec.Instr} {is : List Spec.Instr}
    {q : Nat} (hq : q ∈ B.foot (μ.readN (rdN μ (v + 8) 8) 232)) : q ∈ iterFree B μ v (i :: is).length := by
  rw [show (i :: is).length = is.length + 1 from rfl, iterFree_succ]
  exact List.mem_append_left _ hq

/-- **8540 … 8822, the body before the handler** (an instruction other than `Checkpoint`): from the head
    with `LoopAt` for i :: is, the cursor cur at sp + 480 (8-aligned) and the counter k at sp + 504, either
    the run reaches the dispatch 8822 with ω₁ kept, the instruction's slot copied to sp + 1144, the log
    line's `String` { kc, kp, kl } at sp + 976 (`FreshBuf`, readable), the allocator's context for some s₂
    keeping st's allocated chunks with their data, cur + 232 at sp + 480, k + 1 at sp + 504, the flag
    for zs or `Zombify` at sp + 160, and the memory from sp up kept outside sp + 160 … 168, 480 … 488,
    504 … 1008, 1144 … 1376 and 1568 … 1592; or the log line's allocation fails (`ExhaustsP`). -/
theorem il_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (B : InstrRep)
    {pb S0 S1 : Nat} (hL : InstrLogH B p env pb S0 S1) (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory)
    (st : State) (sp : Nat) (i : Spec.Instr) (is : List Spec.Instr) (rs : List Spec.Result) (zs : Bool)
    (h1 : ω[1] = UInt64.ofNat sp) (hs8 : sp % 8 = 0) (LA : LoopAt B env.code pb S0 S1 sp (i :: is) rs zs μ st)
    (hal : rdN μ (sp + 480) 8 % 8 = 0) (hk : rdN μ (sp + 504) 8 + 1 < 2 ^ 64) (hck : instrIdx i ≠ 15) :
    (∃ (s₂ : State) (ω₂ : Regs) (μ₂ : Memory) (N kc kp kl : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 8540 ω μ (c, f) 8822 ω₂ μ₂ (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ₂ s₂ ∧ ω₂[1] = ω[1] ∧
      μ₂.readN (sp + 1144) 232 = μ.readN (rdN μ (sp + 480) 8) 232 ∧
      rdN μ₂ (sp + 976) 8 = kc ∧ rdN μ₂ (sp + 984) 8 = kp ∧ rdN μ₂ (sp + 992) 8 = kl ∧
      FreshBuf st s₂ kc kp ∧ (∀ a, kp ≤ a → a < kp + kl → μ₂.readable a = true) ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks s₂ ∧ ∀ a, InData d a → μ₂.read a = μ.read a) ∧
      rdN μ₂ (sp + 480) 8 = rdN μ (sp + 480) 8 + 232 ∧ rdN μ₂ (sp + 504) 8 = rdN μ (sp + 504) 8 + 1 ∧
      rdN μ₂ (sp + 160) 8 = (if (zs || instrIdx i == 3) then 1 else 0) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 160 ∨ (sp + 168 ≤ a ∧ a < sp + 480) ∨
        (sp + 488 ≤ a ∧ a < sp + 504) ∨ (sp + 1008 ≤ a ∧ a < sp + 1144) ∨ (sp + 1376 ≤ a ∧ a < sp + 1568) ∨
        sp + 1592 ≤ a) → μ₂.read a = μ.read a)) ∨
    ExhaustsP p env pb 8540 ω μ c f := by
  have H := LA.H
  have hT := H.hS1
  have hSt := H.st
  obtain ⟨hs1, hs2, hs3⟩ := LA.hsp
  have I := LA.I
  have hE := I.hend
  have hR0 := I.rep 0 (by simp)
  obtain ⟨-, d, hd, hu, hdq, hbc, hed⟩ := I.slots (List.cons_ne_nil _ _)
  have hfoot0 : ∀ q ∈ B.foot (μ.readN (rdN μ (sp + 480) 8) 232), ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q :=
    fun q hq => I.owned q (foot_mem_iterFree hq)
  simp only [List.length_cons, List.getElem_cons_zero] at hE hR0
  rw [show sp + 472 + 8 = sp + 480 by omega] at hE hR0 hbc
  rw [show sp + 472 + 24 = sp + 496 by omega] at hE hed
  generalize hcur : rdN μ (sp + 480) 8 = cur at hE hR0 hbc hal hfoot0 ⊢
  generalize hk0 : rdN μ (sp + 504) 8 = k at hk ⊢
  have hlo := Handlers.InstrLoop.data_ge H hd hu (a := cur) ⟨by omega, by omega⟩
  have hhi := ResultsDrop.data_lt H hd (a := cur + 231) ⟨by omega, by omega⟩
  have hrs : ∀ a, cur ≤ a → a < cur + 232 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (HeapKeep.writableData H hd hu ⟨by omega, by omega⟩)
  have hws : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.writable a = true := fun a h1 h2 => hSt a (by omega) (by omega)
  have esl : slot μ cur 0 = μ.readN cur 232 := by simp [slot]
  rw [esl] at hR0
  have e8 : (μ.readN cur 232).take 8 = μ.readN cur 8 := PVM.readN_take μ cur 232 8 (by omega)
  have htag := B.tag i _ μ hR0
  have hnn := B.notNone i _ μ hR0
  rw [e8] at htag hnn
  have hw64 : rdN μ cur 8 < 2 ^ 64 := ResultsDrop.rdN_lt8 μ cur
  have mw : μ.readN cur 8 = Num.encodeLE 8 (rdN μ cur 8) := KeyEnc.readN_enc μ cur 8
  have mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 cur := by rw [← hcur]; exact KeyEnc.readN_enc μ _ 8
  have me : μ.readN (sp + 496) 8 = Num.encodeLE 8 (rdN μ (sp + 496) 8) := KeyEnc.readN_enc μ _ 8
  have mk : μ.readN (sp + 504) 8 = Num.encodeLE 8 k := by rw [← hk0]; exact KeyEnc.readN_enc μ _ 8
  have m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808 := by
    rw [← LA.c184]; exact KeyEnc.readN_enc μ _ 8
  have m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809 := by
    rw [← LA.c216]; exact KeyEnc.readN_enc μ _ 8
  have hst : slotTag (rdN μ cur 8) = instrIdx i := htag
  -- the front, 8540 → 8735
  have hfront : ∃ ω₁ μ₁ N, FreeStepsH p (KeepCtx (accContractS env)) 8540 ω μ (c, f) 8735 ω₁ μ₁ (c, f) N ∧
      ω₁[1] = ω[1] ∧ rdN μ₁ (sp + 160) 8 = (if (zs || instrIdx i == 3) then 1 else 0) ∧
      μ₁.readN (sp + 744) 232 = μ.readN cur 232 ∧ μ₁.readN (sp + 480) 8 = Num.encodeLE 8 (cur + 232) ∧
      μ₁.readN (sp + 504) 8 = Num.encodeLE 8 (k + 1) ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
        (a < sp + 160 ∨ sp + 168 ≤ a) → μ₁.read a = μ.read a) ∧
      (∀ a, μ₁.readable a = μ.readable a) ∧ (∀ a, μ₁.writable a = μ.writable a) := by
    by_cases hz : instrIdx i = 3
    · obtain ⟨ω₁, μ₁, N, run, a1, m160, m744, m480, m504, -, fr, rd, wr⟩ := il_front_zomb
        (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp cur (rdN μ (sp + 496) 8) k (rdN μ cur 8) h1
        ⟨by omega, by omega, hs8⟩ ⟨by omega, by omega, hal⟩ (ResultsDrop.rdN_lt8 μ _) (by omega) hk hw64 hnn
        (by rw [hst, hz]) mc me mw mk m184 m216 hrs hws
      refine ⟨ω₁, μ₁, N, run, a1, ?_, m744, m480, m504, fr, rd, wr⟩
      rw [DesignateAlloc.rd8 (by decide) m160]; simp [hz]
    · obtain ⟨ω₁, μ₁, N, run, a1, m744, m480, m504, -, fr, rd, wr⟩ := il_front
        (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp cur (rdN μ (sp + 496) 8) k (rdN μ cur 8) h1
        ⟨by omega, by omega, hs8⟩ ⟨by omega, by omega, hal⟩ (ResultsDrop.rdN_lt8 μ _) (by omega) hk hw64 hnn
        (by rw [hst]; exact hz) (by rw [hst]; exact hck) mc me mw mk m184 m216 hrs hws
      refine ⟨ω₁, μ₁, N, run, a1, ?_, m744, m480, m504, fun a h0 h2 h3 _ => fr a h0 h2 h3, rd, wr⟩
      rw [rdN_frame fun j hj => fr _ (by omega) (.inr (by omega)) (.inl (by omega)), LA.flag]
      simp [hz]
  obtain ⟨ω₁, μ₁, N₁, run1, a1, m160, m744, m480, m504, fr1, rd1, wr1⟩ := hfront
  have heap1 : ∀ a, a < 2147483648 → μ₁.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ₁ st := HeapKeep.keepHi H heap1 wr1
  have hrep1 : B.rep i (μ₁.readN (sp + 744) 232) μ₁ := by
    rw [m744]
    refine B.frame i _ μ μ₁ st hR0 fun q hq => ?_
    obtain ⟨d, hd, hu, hq⟩ := hfoot0 q hq
    exact ⟨d, hd, hu, hq, fun a ha => heap1 a (ResultsDrop.data_lt H hd ha)⟩
  rcases il_mid (P := P) env B hL c f ω₁ μ₁ st sp i H1 (a1.trans h1) hs1 hs2 hs3 hs8 hrep1 (by rw [m744]; exact hfoot0) with
    ⟨s₂, ω₂, μ₂, N₂, kc, kp, kl, run2, H2, b1, -, -, m1144, m976, m984, m992, hfb, hrd, hkeep, fr2⟩ | hX
  rotate_left
  · exact .inr (ResStore.ExhaustsP.pre run1 hX)
  refine .inl ⟨s₂, ω₂, μ₂, _, kc, kp, kl, run1.trans run2, H2, b1.trans a1, by rw [m1144, m744], m976, m984, m992,
    hfb, hrd, fun d hd hu => ?_, ?_, ?_, ?_, fun a h0 hsp h3 => ?_⟩
  · obtain ⟨hd2, hk2⟩ := hkeep d hd hu
    exact ⟨hd2, fun a ha => (hk2 a ha).trans (heap1 a (ResultsDrop.data_lt H hd ha))⟩
  · rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
    exact DesignateAlloc.rd8 (by omega) m480
  · rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
    exact DesignateAlloc.rd8 hk m504
  · rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
    exact m160
  · rw [fr2 a h0 hsp (by omega) (by omega) (by omega)]
    exact fr1 a h0 (.inr hsp) (by omega) (by omega)

/-- Equal octet strings agree octet by octet. -/
theorem read_of_readN {μ ν : Memory} {a b n k : Nat} (h : μ.readN a n = ν.readN b n) (hk : k < n) :
    μ.read (a + k) = ν.read (b + k) := by
  have := congrArg (fun l => l[k]?) h
  simpa [Memory.readN, hk] using this

/-- A run under a contract keeping what is not writable keeps the read-only data below 196608. -/
theorem roKeep {X : Type} {R : HostRel X} {p : ByteArray} {pb : Nat} (hR : KeepsRO R 48 pb)
    {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X} (run : FreeStepsH p R i ω μ x i' ω' μ' x' n)
    (hro : ∀ a, a < 196608 → μ.writable a = false) :
    ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a := by
  intro a ha
  have k := FreeStepsH.keepRO_of hR run
  have hp := k.1 (a / pageSize) (.inl (by unfold pageSize; omega))
  refine ⟨k.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (hro a ha), ?_⟩
  unfold Memory.readable; rw [hp]

/-- The frame words one body keeps (from sp): `LoopKeep` but the flag, the results `Vec`, the
    `IntoIter`, the counter, the index and the instruction's `String`. -/
def StableKeep (sp a : Nat) : Prop :=
  (sp + 16 ≤ a ∧ a < sp + 40) ∨ (sp + 104 ≤ a ∧ a < sp + 152) ∨ (sp + 168 ≤ a ∧ a < sp + 224) ∨
  (sp + 264 ≤ a ∧ a < sp + 280) ∨ (sp + 312 ≤ a ∧ a < sp + 344) ∨ sp + 1632 ≤ a

/-- The state after one body, against the head's memory μ₀: back at 8540 with ω₁ = sp, `LoopAt` for the
    instructions left `is` and rs ++ [r] (flag zs), the cursor advanced by a slot, the counter by one,
    the octets below 196608 and their access kept, and the words `StableKeep` kept. -/
def BodyPost (B : InstrRep) (code : ByteArray) (pb S0 S1 sp : Nat) (is : List Spec.Instr)
    (rs : List Spec.Result) (zs : Bool) (μ₀ : Memory) (r : Spec.Result) (s' : St Stream) : Prop :=
  s'.i = 8540 ∧ s'.ω[1] = UInt64.ofNat sp ∧ (∃ st', LoopAt B code pb S0 S1 sp is (rs ++ [r]) zs s'.μ st') ∧
  rdN s'.μ (sp + 480) 8 = rdN μ₀ (sp + 480) 8 + 232 ∧ rdN s'.μ (sp + 504) 8 = rdN μ₀ (sp + 504) 8 + 1 ∧
  (∀ a, a < 196608 → s'.μ.read a = μ₀.read a ∧ s'.μ.readable a = μ₀.readable a) ∧
  (∀ a, a < 4294967296 → StableKeep sp a → s'.μ.read a = μ₀.read a)

/-- **One body of the instruction loop, 8540 → 8540** (an instruction i other than `Checkpoint`): from the
    head with `LoopAt` for i :: is and rs (the cursor 8-aligned, the counter below 2⁶⁴ − 1, the dispatch
    table and `StoreFit`), the run implements `onInstr C now i` (GP v0.8.0 Appendix B, Ω_W;
    `Spec.onInstr`, through `HandlerH`) and returns to the head in `BodyPost` for is and rs ++ [r], the
    flag also set for `Zombify`. A failed allocation in the log lines or the push is an early ☇
    (`ExhaustsP`, abort reasons at 40611 / 40821). Named hypotheses: `InstrLogH`, `ResultLogH`, `HandlerH`,
    `PushH`. -/
theorem il_body {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (B : InstrRep)
    {C : Consts} {now pb S0 S1 : Nat} {Ab : St Stream → Prop}
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (s : St Stream) (st : State) (sp : Nat) (i : Spec.Instr) (is : List Spec.Instr) (rs : List Spec.Result)
    (zs : Bool) (hi : s.i = 8540) (h1 : s.ω[1] = UInt64.ofNat sp) (hs8 : sp % 8 = 0)
    (LA : LoopAt B env.code pb S0 S1 sp (i :: is) rs zs s.μ st)
    (hal : rdN s.μ (sp + 480) 8 % 8 = 0) (hk : rdN s.μ (sp + 504) 8 + 1 < 2 ^ 64)
    (hjt : s.μ.readN 65736 100 = jumpTab) (hjr : ∀ a, 65736 ≤ a → a < 65836 → s.μ.readable a = true)
    (hfit : StoreFit s.c) (hck : instrIdx i ≠ 15) :
    Impl p (accContractS env) env Ab (onInstr C now i)
      (BodyPost B env.code pb S0 S1 sp is rs (zs || instrIdx i == 3) s.μ) s := by
  obtain ⟨i0, ω, μ, c, f⟩ := s
  dsimp only at hi h1 LA hal hk hjt hjr hfit ⊢
  subst hi
  have H := LA.H
  have hT := H.hS1
  obtain ⟨hs1, hs2, hs3⟩ := LA.hsp
  rcases il_pre (P := P) env B hL c f ω μ st sp i is rs zs h1 hs8 LA hal hk hck with
    ⟨s₂, ω₂, μ₂, N₂, kc, kp, kl, run2, H2, b1, m1144, m976, m984, m992, hfb, hrd, hkeep2, m480, m504, m160, fr2⟩ |
      hX
  rotate_left
  · exact Impl.abort _ _ (ResStore.ExhaustsP.aborts hAbX hX)
  have ro2 := roKeep (keepCtx_keepsRO env H.bd) run2 H.ro
  have hR0 : B.rep i (μ.readN (rdN μ (sp + 480) 8) 232) μ := by
    have := LA.I.rep 0 (by simp)
    simp only [List.getElem_cons_zero] at this
    rw [show sp + 472 + 8 = sp + 480 by omega] at this
    simpa [slot] using this
  have hF0 : ∀ q ∈ B.foot (μ.readN (rdN μ (sp + 480) 8) 232), ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q :=
    fun q hq => LA.I.owned q (foot_mem_iterFree (v := sp + 472) (i := i) (is := is)
      (by rw [show sp + 472 + 8 = sp + 480 by omega]; exact hq))
  have eF : B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) = B.foot (μ.readN (rdN μ (sp + 480) 8) 232) := by
    rw [show sp + 472 + 8 = sp + 480 by omega]; simp [slot]
  have hF0i : ∀ q ∈ B.foot (μ.readN (rdN μ (sp + 480) 8) 232), q ∈ iterFree B μ (sp + 472) (i :: is).length :=
    fun q hq => foot_mem_iterFree (v := sp + 472) (i := i) (is := is)
      (by rw [show sp + 472 + 8 = sp + 480 by omega]; exact hq)
  generalize hcur : rdN μ (sp + 480) 8 = cur at m1144 m480 hR0 hF0 eF hF0i
  generalize hF : B.foot (μ.readN cur 232) = F0 at hF0 eF hF0i
  -- the dispatch
  have e2 : ∀ a, sp + 168 ≤ a → a < sp + 480 → μ₂.read a = μ.read a := fun a h1 h2 =>
    fr2 a (by omega) (by omega) (by omega)
  have hrep2 : B.rep i (μ₂.readN (sp + 1144) 232) μ₂ := by
    rw [m1144]
    refine B.frame i _ μ μ₂ st hR0 fun q hq => ?_
    rw [hF] at hq
    obtain ⟨d, hd, hu, hq⟩ := hF0 q hq
    exact ⟨d, hd, hu, hq, (hkeep2 d hd hu).2⟩
  have hfoot2 : ∀ q ∈ B.foot (μ₂.readN (sp + 1144) 232), ∃ d ∈ chunks s₂, d.used = true ∧ d.addr + 32 = q := by
    rw [m1144, hF]; intro q hq
    obtain ⟨d, hd, hu, hq⟩ := hF0 q hq
    exact ⟨d, (hkeep2 d hd hu).1, hu, hq⟩
  have c184 : rdN μ₂ (sp + 184) 8 = 9223372036854775808 := by
    rw [rdN_frame fun j hj => e2 _ (by omega) (by omega)]; exact LA.c184
  have c216 : rdN μ₂ (sp + 216) 8 = 9223372036854775809 := by
    rw [rdN_frame fun j hj => e2 _ (by omega) (by omega)]; exact LA.c216
  have c200 : rdN μ₂ (sp + 200) 8 = 678 := by
    rw [rdN_frame fun j hj => e2 _ (by omega) (by omega)]; exact LA.c200
  have hjt2 : μ₂.readN 65736 100 = jumpTab := by
    rw [← hjt]; exact Memory.readN_congr fun j hj => (ro2 _ (by omega)).1
  have hjr2 : ∀ a, 65736 ≤ a → a < 65836 → μ₂.readable a = true := fun a h1 h2 => by
    rw [(ro2 a (by omega)).2]; exact hjr a h1 h2
  have hh := hH i c f ω₂ μ₂ s₂ sp H2 (b1.trans h1) hs2 hs3 hs1 hrep2 hfoot2 c184 c216 c200 hjt2 hjr2 hfit
  rw [m1144, hF] at hh
  refine Impl.pre _ _ (s' := ⟨8822, ω₂, μ₂, c, f⟩) ⟨_, run2⟩ rfl (Impl.then ?_ _ _ hh)
  -- the tail, from the handler's end
  intro r s' hp
  obtain ⟨i3, ω₃, μ₃, c₃, f₃⟩ := s'
  obtain ⟨hi3, h31, st₃, H3, hres3, hown3, hkeep3, hLK3, -, hro3, hrd3, -⟩ := hp
  dsimp only at hi3 h31 H3 hres3 hown3 hkeep3 hLK3 hro3 hrd3 ⊢
  subst hi3
  have e3 : ∀ a, a < 4294967296 → sp ≤ a → LoopKeep sp a → (a < sp + 160 ∨ (sp + 168 ≤ a ∧ a < sp + 480) ∨
      (sp + 488 ≤ a ∧ a < sp + 504) ∨ (sp + 1008 ≤ a ∧ a < sp + 1144) ∨ (sp + 1376 ≤ a ∧ a < sp + 1568) ∨
      sp + 1592 ≤ a) → μ₃.read a = μ.read a := fun a h0 h1 h2 h3 => (hLK3 a h0 h2).trans (fr2 a h0 h1 h3)
  have v200 : rdN μ₃ (sp + 200) 8 = 678 := by
    rw [rdN_frame fun j hj => hLK3 _ (by omega) (by unfold LoopKeep; omega)]; exact c200
  have v984 : rdN μ₃ (sp + 984) 8 = kp := by
    rw [rdN_frame fun j hj => hLK3 _ (by omega) (by unfold LoopKeep; omega)]; exact m984
  have v992 : rdN μ₃ (sp + 992) 8 = kl := by
    rw [rdN_frame fun j hj => hLK3 _ (by omega) (by unfold LoopKeep; omega)]; exact m992
  rcases il_tail_log (P := P) env hR c₃ f₃ ω₃ μ₃ st₃ sp r (ResC s₂ st₃ F0) H3 h31 hs1 hs2 hs3 hres3
      (fun d hd => ⟨hd.1, hd.2.1⟩) v200 (by rw [v984, v992]; intro a h1 h2; rw [hrd3]; exact hrd a h1 h2) with
    ⟨st₄, ω₄, μ₄, N₄, run4, H4, c41, hkeep4, fr4⟩ | hX
  rotate_left
  · exact Impl.abort _ _ (ResStore.ExhaustsP.aborts hAbX hX)
  -- the results `Vec`
  obtain ⟨cp, hcp⟩ : ∃ cp, rdN μ (sp + 448) 8 = cp := ⟨_, rfl⟩
  obtain ⟨rp, hrp⟩ : ∃ rp, rdN μ (sp + 456) 8 = rp := ⟨_, rfl⟩
  have e4 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1168 ≤ a) → (a < sp + 1496 ∨ sp + 1512 ≤ a) →
      (a < sp + 1568 ∨ sp + 1616 ≤ a) → LoopKeep sp a → (a < sp + 160 ∨ (sp + 168 ≤ a ∧ a < sp + 480) ∨
      (sp + 488 ≤ a ∧ a < sp + 504) ∨ (sp + 1008 ≤ a ∧ a < sp + 1144) ∨ (sp + 1376 ≤ a ∧ a < sp + 1568) ∨
      sp + 1592 ≤ a) → μ₄.read a = μ.read a := fun a h0 h1 h2 h3 h4 h5 h6 =>
    (fr4 a h0 h1 h2 h3 h4).trans (e3 a h0 h1 h5 h6)
  have v448 : rdN μ₄ (sp + 448) 8 = cp := by
    rw [rdN_frame fun j hj => e4 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold LoopKeep; omega) (by omega)]; exact hcp
  have v456 : rdN μ₄ (sp + 456) 8 = rp := by
    rw [rdN_frame fun j hj => e4 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold LoopKeep; omega) (by omega)]; exact hrp
  have v464 : rdN μ₄ (sp + 464) 8 = rs.length := by
    rw [rdN_frame fun j hj => e4 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold LoopKeep; omega) (by omega)]; exact LA.hn
  have hncp : rs.length ≤ cp := hcp ▸ LA.hcap
  have hnd := LA.hnd
  have rpT : cp ≠ 0 → rp ∈ tailFree μ sp := fun hc => by
    unfold tailFree tailBufs; rw [hcp, hrp]; simp [optBuf, hc]
  have rpF0 : cp ≠ 0 → rp ∉ F0 := fun hc hq => nd_dis hnd (hF0i _ hq) (rpT hc)
  have hroom : cp ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rp ∧ rp + 144 * cp ≤ d.addr + 32 * d.size :=
    fun hc => by have := LA.hroom (by rw [hcp]; exact hc); rw [hcp, hrp] at this; exact this
  -- the results buffer's chunk, kept up to the push
  have kR : cp ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = rp ∧ rp + 144 * cp ≤ d.addr + 32 * d.size ∧
      d ∈ chunks s₂ ∧ d ∈ chunks st₃ ∧ d ∈ chunks st₄ ∧ ∀ a, InData d a → μ₄.read a = μ.read a := by
    intro hc
    obtain ⟨d, hd, hu, hda, hdr⟩ := hroom hc
    obtain ⟨d2, k2⟩ := hkeep2 d hd hu
    obtain ⟨d3, k3⟩ := hkeep3 d d2 hu (by rw [hda]; exact rpF0 hc)
    obtain ⟨d4, k4⟩ := hkeep4 d d3 hu
    exact ⟨d, hd, hu, hda, hdr, d2, d3, d4, fun a ha => (k4 a ha).trans ((k3 a ha).trans (k2 a ha))⟩
  rcases il_tail_push (P := P) env hP c₃ f₃ ω₄ μ₄ st₄ sp cp rp rs.length H4 (c41.trans h31) hs1 hs2 hs3 hs8 v448 v456 v464
      hncp (fun hc => by obtain ⟨d, -, hu, hda, hdr, -, -, d4, -⟩ := kR hc; exact ⟨d, d4, hu, hda, hdr⟩) with
    ⟨st₅, ω₅, μ₅, N₅, cp', rp', run5, H5, d51, d55, m448', m456', m464', hlt, hNB, hmv5, hcopy, fr5⟩ | hX
  rotate_left
  · exact Impl.abort _ _ (ResStore.ExhaustsP.aborts hAbX (ResStore.ExhaustsP.pre run4 hX))
  obtain ⟨d', hd'5, hd'u, hd'a, hd'r, hNBk⟩ := hNB
  -- the log line's `String`
  have hch : kc ≠ 0 → ∃ ch ∈ chunks s₂, ch.used = true ∧ ch.addr + 32 = kp ∧
      ∀ d ∈ chunks st, d.used = true → d ≠ ch := fun hc => hfb.resolve_left hc
  have kpF0 : kc ≠ 0 → kp ∉ F0 := fun hc hq => by
    obtain ⟨ch, hch2, -, hcha, hfr⟩ := hch hc
    obtain ⟨dq, hdq, hdqu, hdqa⟩ := hF0 kp hq
    exact hfr dq hdq hdqu (chunk_addr H2 (hkeep2 dq hdq hdqu).1 hch2 (by rw [hdqa, hcha]))
  have kprp : kc ≠ 0 → kp ≠ rp := fun hc he => by
    obtain ⟨ch, hch2, -, hcha, hfr⟩ := hch hc
    by_cases hc0 : cp = 0
    · have := LA.hrp0 (by rw [hcp]; exact hc0); rw [hrp] at this; omega
    · obtain ⟨dr, hdr, hur, hdra, -, dr2, -⟩ := kR hc0
      exact hfr dr hdr hur (chunk_addr H2 dr2 hch2 (by rw [hdra, hcha, he]))
  have kch : kc ≠ 0 → ∃ ch ∈ chunks st₃, ch.used = true ∧ ch.addr + 32 = kp ∧ ch ∈ chunks st₅ ∧ ch ≠ d' ∧
      ∀ d ∈ chunks st, d.used = true → d ≠ ch := fun hc => by
    obtain ⟨ch, hch2, hchu, hcha, hfr⟩ := hch hc
    obtain ⟨d3, -⟩ := hkeep3 ch hch2 hchu (by rw [hcha]; exact kpF0 hc)
    obtain ⟨d4, -⟩ := hkeep4 ch d3 hchu
    obtain ⟨hne, d5, -⟩ := hNBk ch d4 hchu (by rw [hcha]; exact kprp hc)
    exact ⟨ch, d3, hchu, hcha, d5, hne, hfr⟩
  have v976 : rdN μ₅ (sp + 976) 8 = kc := by
    rw [rdN_frame fun j hj => fr5 _ (by omega) (by omega) (by omega),
      rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => hLK3 _ (by omega) (by unfold LoopKeep; omega)]; exact m976
  have v984' : rdN μ₅ (sp + 984) 8 = kp := by
    rw [rdN_frame fun j hj => fr5 _ (by omega) (by omega) (by omega),
      rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact v984
  have hcp' : cp' < 2 ^ 64 := by have := ResultsDrop.rdN_lt8 μ₅ (sp + 448); rw [m448'] at this; exact this
  obtain ⟨ω₆, μ₆, N₆, run6, H6, e61, m464'', hkeep6, fr6⟩ := il_tail_post (P := P) env c₃ f₃ ω₅ μ₅ st₅ sp rs.length kc kp H5
    (d51.trans (c41.trans h31)) d55 hs1 hs2 hs3 (by omega) v976 v984'
    (fun hc => by obtain ⟨ch, -, hchu, hcha, d5, -⟩ := kch hc; exact ⟨ch, d5, hchu, hcha⟩)
  -- the new buffer, kept by the back edge
  have hd'kp : d'.addr + 32 ∉ optBuf kc kp := by
    by_cases hc : kc = 0
    · simp [optBuf, hc]
    · simp only [optBuf, hc, if_false, List.mem_singleton]
      intro he
      obtain ⟨ch, -, -, hcha, d5, hne, -⟩ := kch hc
      exact hne (chunk_addr H5 d5 hd'5 (by rw [hcha, he]))
  obtain ⟨hd'6, kd'⟩ := hkeep6 d' hd'5 hd'u hd'kp
  -- the head's chunks, kept to the end
  have kst : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ F0 → d.addr + 32 ∉ optBuf cp rp →
      d ∈ chunks st₄ ∧ (∀ a, InData d a → μ₄.read a = μ.read a) ∧ d.addr + 32 ≠ rp ∧ d.addr + 32 ∉ optBuf kc kp := by
    intro d hd hu hF hO
    obtain ⟨d2, k2⟩ := hkeep2 d hd hu
    obtain ⟨d3, k3⟩ := hkeep3 d d2 hu hF
    obtain ⟨d4, k4⟩ := hkeep4 d d3 hu
    refine ⟨d4, fun a ha => (k4 a ha).trans ((k3 a ha).trans (k2 a ha)), fun he => ?_, fun hm => ?_⟩
    · by_cases hc0 : cp = 0
      · have := LA.hrp0 (by rw [hcp]; exact hc0); rw [hrp] at this; omega
      · exact hO (by simp [optBuf, hc0, he])
    · by_cases hc0 : kc = 0
      · simp [optBuf, hc0] at hm
      · simp only [optBuf, hc0, if_false, List.mem_singleton] at hm
        obtain ⟨ch, hch2, -, hcha, hfr⟩ := hch hc0
        exact hfr d hd hu (chunk_addr H2 d2 hch2 (by rw [hm, hcha]))
  -- the result's chunks
  have hC : ∀ d, ResC s₂ st₃ F0 d → NewC st ((optBuf kc kp).foldl free st₅) F0 rp' d ∧
      ∀ a, InData d a → μ₆.read a = μ₃.read a := by
    intro d ⟨hd3, hu, hcase⟩
    have hne : d.addr + 32 ≠ rp ∧ d.addr + 32 ∉ optBuf kc kp ∧
        ∀ d0 ∈ chunks st, d0.used = true → d0.addr + 32 ∉ F0 → d0.addr ≠ d.addr := by
      rcases hcase with hfr | hF
      · refine ⟨fun he => ?_, fun hm => ?_, fun d0 hd0 hu0 hF0' he => ?_⟩
        · by_cases hc0 : cp = 0
          · have := LA.hrp0 (by rw [hcp]; exact hc0); rw [hrp] at this; omega
          · obtain ⟨dr, -, hur, hdra, -, dr2, dr3, -⟩ := kR hc0
            exact hfr dr dr2 hur (chunk_addr H3 dr3 hd3 (by rw [hdra, he]))
        · by_cases hc0 : kc = 0
          · simp [optBuf, hc0] at hm
          · simp only [optBuf, hc0, if_false, List.mem_singleton] at hm
            obtain ⟨ch, hch2, hchu, hcha, -⟩ := hch hc0
            obtain ⟨ch3, -, -, hcha3, -⟩ := kch hc0
            exact hfr ch hch2 hchu (chunk_addr H3 (hkeep3 ch hch2 hchu (by rw [hcha]; exact kpF0 hc0)).1 hd3
              (by rw [hcha, hm]))
        · obtain ⟨d02, -⟩ := hkeep2 d0 hd0 hu0
          obtain ⟨d03, -⟩ := hkeep3 d0 d02 hu0 hF0'
          exact hfr d0 d02 hu0 (chunk_addr H3 d03 hd3 (by omega))
      · refine ⟨fun he => ?_, fun hm => ?_, fun d0 hd0 hu0 hF0' he => hF0' (by rw [show d0.addr + 32 = d.addr + 32 by omega]; exact hF)⟩
        · by_cases hc0 : cp = 0
          · have := LA.hrp0 (by rw [hcp]; exact hc0); rw [hrp] at this; omega
          · exact rpF0 hc0 (he ▸ hF)
        · by_cases hc0 : kc = 0
          · simp [optBuf, hc0] at hm
          · simp only [optBuf, hc0, if_false, List.mem_singleton] at hm
            exact kpF0 hc0 (hm ▸ hF)
    obtain ⟨hrpne, hkpne, h3⟩ := hne
    obtain ⟨d4, k4⟩ := hkeep4 d hd3 hu
    obtain ⟨hdd', d5, k5⟩ := hNBk d d4 hu hrpne
    obtain ⟨d6, k6⟩ := hkeep6 d d5 hu hkpne
    exact ⟨⟨d6, hu, h3, fun he => hdd' (chunk_addr H5 d5 hd'5 (by rw [he, hd'a]))⟩,
      fun a ha => (k6 a ha).trans ((k5 a ha).trans (k4 a ha))⟩
  -- the item's octets and buffers
  have he : ∀ o, o < 144 → μ₆.read (rp' + 144 * rs.length + o) = μ₃.read (sp + 1000 + o) := by
    intro o ho
    rw [kd' _ ⟨by omega, by omega⟩, read_of_readN hcopy ho,
      fr4 _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
  have hres' := ResultAtP.copy hC he hres3
  have hown' := (ItemOwn.copy he hC hown3).2
  have hmv : ∀ k, k < 144 * rs.length → μ₆.read (rp' + k) = μ.read (rdN μ (sp + 456) 8 + k) := by
    intro k hk
    rw [hrp]
    have hc0 : cp ≠ 0 := by intro h; omega
    obtain ⟨dr, -, -, hdra, hdrr, -, -, -, kdr⟩ := kR hc0
    rw [kd' _ ⟨by omega, by omega⟩, read_of_readN hmv5 hk, kdr _ ⟨by omega, by omega⟩]
  -- the frame
  have w62 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 448 ∨ (sp + 472 ≤ a ∧ a < sp + 1144) ∨
      (sp + 1168 ≤ a ∧ a < sp + 1496) ∨ (sp + 1512 ≤ a ∧ a < sp + 1568) ∨ sp + 1616 ≤ a) → LoopKeep sp a →
      μ₆.read a = μ₂.read a := fun a h0 h1 h2 h3 => by
    rw [fr6 a h0 h1 (by omega), fr5 a h0 h1 (by omega), fr4 a h0 h1 (by omega) (by omega) (by omega), hLK3 a h0 h3]
  have w6 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 448 ∨ (sp + 472 ≤ a ∧ a < sp + 1144) ∨
      (sp + 1168 ≤ a ∧ a < sp + 1496) ∨ (sp + 1512 ≤ a ∧ a < sp + 1568) ∨ sp + 1616 ≤ a) → LoopKeep sp a →
      (a < sp + 160 ∨ (sp + 168 ≤ a ∧ a < sp + 480) ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨
        (sp + 1008 ≤ a ∧ a < sp + 1144) ∨ (sp + 1376 ≤ a ∧ a < sp + 1568) ∨ sp + 1592 ≤ a) →
      μ₆.read a = μ.read a := fun a h0 h1 h2 h3 h4 => (w62 a h0 h1 h2 h3).trans (fr2 a h0 h1 h4)
  have ro : ∀ a, a < 196608 → μ₆.read a = μ.read a ∧ μ₆.readable a = μ.readable a := fun a ha => by
    obtain ⟨r6, q6⟩ := roKeep (keepCtx_keepsRO env H.bd) run6 H5.ro a ha
    obtain ⟨r5, q5⟩ := roKeep (keepCtx_keepsRO env H.bd) run5 H4.ro a ha
    obtain ⟨r4, q4⟩ := roKeep (keepCtx_keepsRO env H.bd) run4 H3.ro a ha
    exact ⟨by rw [r6, r5, r4, hro3 a ha, (ro2 a ha).1], by rw [q6, q5, q4, hrd3, (ro2 a ha).2]⟩
  refine Impl.pre _ _ (s' := ⟨8540, ω₆, μ₆, c₃, f₃⟩) ⟨_, run4.trans (run5.trans run6)⟩ rfl (Impl.pure_of
    ⟨rfl, e61.trans (d51.trans (c41.trans h31)), ⟨_, LoopAt.step LA H6 ?_ ?_ ?_ ?_ ?_ ?_ m464'' hlt ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ hmv ?_ ?_ ?_⟩, ?_, ?_, ro, fun a h0 hs => ?_⟩)
  · rw [show sp + 472 + 8 = sp + 480 by omega, rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega)
      (by unfold LoopKeep; omega), m480, hcur]
  · rw [show sp + 472 + 24 = sp + 496 by omega]
    exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · rw [show sp + 472 + 16 = sp + 488 by omega]
    exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · rw [rdN_frame fun j hj => fr6 _ (by omega) (by omega) (by omega)]; exact m448'
  · rw [rdN_frame fun j hj => fr6 _ (by omega) (by omega) (by omega)]; exact m456'
  · exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · exact rdN_frame fun j hj => w6 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega)]; exact m160
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega)]; exact c184
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega)]; exact c216
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega)]; exact c200
  · rw [show sp + 472 + 8 = sp + 480 by omega, hcur, eF, hcp, hrp]
    intro d hd hu hF hO
    obtain ⟨d4, k4, hne, hnk⟩ := kst d hd hu hF hO
    obtain ⟨-, d5, k5⟩ := hNBk d d4 hu hne
    obtain ⟨d6, k6⟩ := hkeep6 d d5 hu hnk
    exact ⟨d6, fun a ha => (k6 a ha).trans ((k5 a ha).trans (k4 a ha))⟩
  · rw [show sp + 472 + 8 = sp + 480 by omega, hcur, eF, hcp, hrp]
    exact ⟨d', hd'6, hd'u, hd'a, hd'r, fun d hd hu hF hO =>
      (hNBk d (kst d hd hu hF hO).1 hu (kst d hd hu hF hO).2.2.1).1⟩
  · rw [show sp + 472 + 8 = sp + 480 by omega, hcur, eF]; exact hres'
  · rw [show sp + 472 + 8 = sp + 480 by omega, hcur, eF]; exact hown'
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega), m480, hcur]
  · rw [rdN_frame fun j hj => w62 _ (by omega) (by omega) (by omega) (by unfold LoopKeep; omega), m504]
  · unfold StableKeep at hs
    exact w6 a h0 (by omega) (by omega) (by unfold LoopKeep; omega) (by omega)

end Services.Bootstrap.Acc.Handlers.InstrLoop
