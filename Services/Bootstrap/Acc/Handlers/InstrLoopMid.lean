import Services.Bootstrap.Acc.Handlers.InstrLoopHyp
import Services.Bootstrap.Acc.Handlers.InstrLoopFront

/-!
# R5, the instruction loop: the body's middle (8735 → 8822)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop): after the
front, the instruction's Debug log line is formatted (`format!` at 8772, the named hypothesis
`InstrLogH`), its `String` moved to sp + 976, and the instruction's copy at sp + 744 copied again to
sp + 1144 (`memcpy`, returning to 8822), where the dispatch (`HandlerH`) starts.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.InstrRep

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **8735 … 8822, the instruction's log line and its second copy**: from 8735 with the instruction's
    copy at sp + 744 representing i (`B.rep`, its buffers allocated in s₀), either the run reaches the
    dispatch 8822 with ω₁, ω₅, ω₆ kept, the copy also at sp + 1144, the log line's `String`
    { kc, kp, kl } at sp + 976 (`FreshBuf`, its kl octets readable), the allocator's context for some
    s′ keeping s₀'s allocated chunks with their data, and from sp up only sp + 976 … sp + 1008,
    sp + 1144 … sp + 1376 and sp + 1568 … sp + 1592 changed; or the log line's
    allocation fails (`ExhaustsP`). -/
theorem il_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (B : InstrRep)
    {pb S0 S1 : Nat} (hL : InstrLogH B p env pb S0 S1) (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory)
    (s₀ : State) (sp : Nat) (i : Spec.Instr) (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h1 : ω[1] = UInt64.ofNat sp) (hs1 : 2147483648 + 4096 ≤ sp) (hs2 : S0 + 4096 ≤ sp)
    (hs3 : sp + 1632 ≤ S1) (hs8 : sp % 8 = 0)
    (hrep : B.rep i (μ.readN (sp + 744) 232) μ)
    (hfoot : ∀ q ∈ B.foot (μ.readN (sp + 744) 232), ∃ d ∈ chunks s₀, d.used = true ∧ d.addr + 32 = q) :
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N kc kp kl : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 8735 ω μ (c, f) 8822 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp + 1144) 232 = μ.readN (sp + 744) 232 ∧
      rdN μ' (sp + 976) 8 = kc ∧ rdN μ' (sp + 984) 8 = kp ∧ rdN μ' (sp + 992) 8 = kl ∧
      FreshBuf s₀ s' kc kp ∧ (∀ a, kp ≤ a → a < kp + kl → μ'.readable a = true) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 976 ∨ sp + 1008 ≤ a) → (a < sp + 1144 ∨ sp + 1376 ≤ a) →
        (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 8735 ω μ c f := by
  have hT := H.hS1
  have hSt := H.st
  -- 8735 → 59375
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, m1a, m1b, m1c, fr1, rd1, wr1⟩ :=
    il_log_pre (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ sp h1 ⟨by omega, by omega⟩
      (fun a h1 h2 => hSt a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
    HeapKeep.keepHi H (fun a ha => fr1 a (by omega) (.inl (by omega)) (.inl (by omega))) wr1
  have e744 : μ1.readN (sp + 744) 232 = μ.readN (sp + 744) 232 :=
    Memory.readN_congr fun j hj => fr1 _ (by omega) (.inl (by omega)) (.inl (by omega))
  have hrep1 : B.rep i (μ1.readN (sp + 744) 232) μ1 := by
    rw [e744]
    refine B.frame i _ μ μ1 s₀ hrep fun q hq => ?_
    obtain ⟨d, hd, hu, hq⟩ := hfoot q hq
    exact ⟨d, hd, hu, hq, fun a ha => fr1 a (by have := ResultsDrop.data_lt H hd ha; omega)
      (.inl (by have := ResultsDrop.data_lt H hd ha; omega))
      (.inl (by have := ResultsDrop.data_lt H hd ha; omega))⟩
  rcases hL c f ω1 μ1 s₀ sp i H1 a0 (a1.trans h1) a7 a8 a9 hs2 hs3 hs1
    (DesignateAlloc.rd8 (by omega) m1b) (DesignateAlloc.rd8 (by omega) m1c)
    (DesignateAlloc.rd8 (by omega) m1a) hrep1 with
    ⟨s', ω2, μ2, N2, kc, kp, kl, run2, H2, b1, b5, b6, m2c, m2p, hfb, m2l, hrd, hkeep, fr2, -⟩ | hX
  rotate_left
  · exact .inr (ResStore.ExhaustsP.pre run1 hX)
  have hSt2 := H2.st
  -- 8779 → 68729
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, m3c, m3p, m3l, fr3, rd3, wr3⟩ :=
    il_log_post (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2 sp kc kp kl (b1.trans (a1.trans h1))
      ⟨by omega, by omega⟩ (by rw [← m2c]; exact ResultsDrop.rdN_lt8 _ _)
      (by rw [← m2p]; exact ResultsDrop.rdN_lt8 _ _) (by rw [← m2l]; exact ResultsDrop.rdN_lt8 _ _)
      (by rw [← m2c]; exact KeyEnc.readN_enc μ2 _ 8) (by rw [← m2p]; exact KeyEnc.readN_enc μ2 _ 8)
      (by rw [← m2l]; exact KeyEnc.readN_enc μ2 _ 8)
      (fun a h1 h2 => Memory.readable_of_writable (hSt2 a (by omega) (by omega)))
      (fun a h1 h2 => hSt2 a (by omega) (by omega))
  -- 68729 → 8822 (memcpy sp + 744 → sp + 1144)
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, m4, fr4, rd4, wr4⟩ := memcpy_val (R := KeepCtx (accContractS env))
    (P := P) (c, f) ω3 μ3 304 8822 sp (sp + 1144) (sp + 744) 232 c0 (c1.trans (b1.trans (a1.trans h1))) c7 c8 c9
    (by decide) jte_151 bs_8822 ⟨by omega, by omega, hs8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (.inr (by omega)) (.inl (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd3]; exact Memory.readable_of_writable (hSt2 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr3]; exact hSt2 a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3]; exact hSt2 a (by omega) (by omega))
  have H4 : HeapCtxC env.code pb S0 S1 μ4 s' :=
    HeapKeep.keepHi (HeapKeep.keepHi H2 (fun a ha => fr3 a (by omega) (.inl (by omega))) wr3)
      (fun a ha => fr4 a (by omega) (.inl (by omega)) (.inl (by omega))) wr4
  have k4 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1144 ∨ sp + 1376 ≤ a) → μ4.read a = μ3.read a :=
    fun a h0 ha hb => fr4 a h0 hb (.inr ha)
  have bc := ResultsDrop.rdN_lt8 μ2 (sp + 1568)
  have bp := ResultsDrop.rdN_lt8 μ2 (sp + 1576)
  have bl := ResultsDrop.rdN_lt8 μ2 (sp + 1584)
  rw [m2c] at bc; rw [m2p] at bp; rw [m2l] at bl
  refine .inl ⟨s', ω4, μ4, _, kc, kp, kl, run1.trans (run2.trans (run3.trans run4)), H4,
    d1.trans (c1.trans (b1.trans a1)), d5.trans (c5.trans (b5.trans a5)), d6.trans (c6.trans (b6.trans a6)),
    ?_, ?_, ?_, ?_, hfb, fun a h1 h2 => by rw [rd4, rd3]; exact hrd a h1 h2, fun d hd hu => ?_,
    fun a h0 ha hb hc hd => ?_⟩
  · rw [m4, ← e744]
    exact Memory.readN_congr fun j hj => (fr3 _ (by omega) (.inl (by omega))).trans
      (fr2 _ (by omega) (by omega) (.inl (by omega)))
  · rw [rdN_frame fun j hj => k4 _ (by omega) (by omega) (.inl (by omega))]
    exact DesignateAlloc.rd8 bc m3c
  · rw [rdN_frame fun j hj => k4 _ (by omega) (by omega) (.inl (by omega))]
    exact DesignateAlloc.rd8 bp m3p
  · rw [rdN_frame fun j hj => k4 _ (by omega) (by omega) (.inl (by omega))]
    exact DesignateAlloc.rd8 bl m3l
  · obtain ⟨hd2, hk⟩ := hkeep d hd hu
    refine ⟨hd2, fun a ha => ?_⟩
    have := ResultsDrop.data_lt H hd ha
    rw [fr4 a (by omega) (.inl (by omega)) (.inl (by omega)), fr3 a (by omega) (.inl (by omega)), hk a ha,
      fr1 a (by omega) (.inl (by omega)) (.inl (by omega))]
  · rw [k4 a h0 ha hc, fr3 a h0 (by omega), fr2 a h0 ha hd, fr1 a h0 (by omega) (by omega)]

end Services.Bootstrap.Acc.Handlers.InstrLoop
