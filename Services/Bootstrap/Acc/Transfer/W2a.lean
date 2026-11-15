import Services.Bootstrap.Acc.Transfer.Tail4
import Services.Bootstrap.Acc.Transfer.CopyVal
import Services.Bootstrap.Acc.Transfer.Trap
import Services.Bootstrap.Acc.Transfer.SetKeyCall

/-!
# `on_transfer`, the memo's copy for the log line (7399 → 7454)

`tr_w2a` composes `tr_a128`, `alloc_callG` (128 octets), `tr_a128_cpy`, `memcpy_val` (the memo, sp + 1144,
into the block), `tr_u8_pre` and `Utf8Call` (`from_utf8` of the copy, a named hypothesis). Or the
allocation failed and the run reaches the trap at 15363 (the `heap` abort, `aborts_of_trap`). The
context and the stream are kept. None of this is in Spec `onTransfer`: the log line is frame-only.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **7399 → 7454**: the memo copied into a fresh 128-octet block ptr (a chunk of the new allocator
    state, fresh against s₀) and `from_utf8` run on it: ω₁ = sp, ω₅ kept, ω₆ = ptr, the tag at
    sp + 744 (0 with the slice (ptr, 128), or 1); every allocated chunk of s₀ and its data kept; from sp
    up only sp + 744 … sp + 768 changed; below 196608 the memory reads and is readable as before. Or
    `alloc` returned null: an early ☇ for a `HeapFailT` reason. -/
theorem tr_w2a (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hU : Utf8Call p env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s₀) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1) :
    (∃ s' ω' μ' N ptr, FreeStepsH p (KeepCtx (accContractS env)) 7399 ω μ (c, f) 7454 ω' μ' (c, f) N ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat ptr ∧
      65536 ≤ ptr ∧ ptr + 128 ≤ 2147483648 ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (⟨ptr - 32, (128 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ≠ ⟨ptr - 32, (128 + 31) / 32 + 1, true⟩) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      ((rdN μ' (sp + 744) 8 = 0 ∧ rdN μ' (sp + 752) 8 = ptr ∧ rdN μ' (sp + 760) 8 = 128) ∨
        rdN μ' (sp + 744) 8 = 1) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 744 ∨ sp + 768 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a)) ∨
    Aborts p (KeepCtx (accContractS env)) Ab ⟨7399, ω, μ, c, f⟩ c := by
  have hst := H.st
  have hS1 := H.hS1
  have hro := H.ro
  -- 7399 → 40494
  obtain ⟨ω1, run1, b0, b7, b8, bj⟩ := tr_a128 (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ
  have b1 : ω1[1] = UInt64.ofNat sp := (bj 1 (by decide)).trans h1
  rcases alloc_callG (p := p) (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ω1 μ s₀ sp 128 1 pb S0 S1 H
      b1 b7 b8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨ptr, s1, ω2, μ2, -, run2, H2, keep2, hnew, hfresh, hkg, e7, stk2, f0, f1, f5, f6⟩ |
    ⟨-, ω2, μ2, run2, e7, stk2, f0, f1, f5, f6⟩
  rotate_left
  · -- `alloc` returned null: 7413 → 15363
    obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
    obtain ⟨ω3, run3⟩ := tr_a128_null (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 e7
    exact .inr (aborts_of_trap (P := P) (fun s h => hAb s (.inl h)) ⟨7399, ω, μ, c, f⟩
      (.inr (.inr (.inr (.inr (.inl rfl)))))
      ((run1.trans (run2S.trans (tr_j252 (p := p) (P := P) _ ω2 μ2 (f0.trans b0)))).trans run3))
  obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
  have kro := HeapHost.keepRO (env := accHeapHost env) H.bd run2
  obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
  dsimp only at Nb1 Nb2 Nb3
  have hb0 := H2.hb0
  have hbT := H2.hbT
  have hst2 := H2.st
  have run2' := run2S.trans (tr_j252 (p := p) (P := P) _ ω2 μ2 (f0.trans b0))
  -- 7413 → 68729 → 7437: the memo's copy
  obtain ⟨ω3, run3, c0, c7, c6, c8, c9, c1, cj⟩ := tr_a128_cpy (p := p) (P := P) (R := KeepCtx (accContractS env))
    (c, f) ω2 μ2 sp ptr (f1.trans b1) e7 (by omega) (by omega) (by omega)
  have hwd : ∀ a, ptr ≤ a → a < ptr + 128 → μ2.writable a = true := fun a h1 h2 =>
    heapC_writable_data H2 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, cp4, fr4, rd4, wr4⟩ := memcpy_val (p := p) (P := P)
    (R := KeepCtx (accContractS env)) (c, f) ω3 μ2 254 7437 sp ptr (sp + 1144) 128 c0 c1 c7 c8 c9 (by decide)
    jte_126 bs_7437 ⟨by omega, by omega, hsp.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega))
    (.inr (by omega)) (.inl (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega))) hwd
    (fun a h1 h2 => hst2 a (by omega) (by omega))
  -- the heap context at 7437: the block's data and the memcpy frame (below sp) written
  have H4 : HeapCtxC env.code pb S0 S1 μ4 s1 :=
    HeapCtxC.keep_data H2 hnew (fun a ha hc => fr4 a (by omega) (by dsimp only at hc; omega) (.inl (by omega))) wr4
  -- 7437 → 60681 → 7454
  obtain ⟨ω5, run5, g0, g1, g7, g8, g9, gj⟩ := tr_u8_pre (p := p) (P := P) (R := KeepCtx (accContractS env))
    (c, f) ω4 μ4 sp (d1.trans c1) (by omega)
  have g8' : ω5[8] = UInt64.ofNat ptr := g8.trans (d6.trans c6)
  obtain ⟨ω6, μ6, N6, run6, H6, k1, k5, k6, tag, fr6, rd6, wr6⟩ := hU c f ω5 μ4 s1 sp ptr H4 g0 g1 g7 g8' g9
    (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [rd4]; exact Memory.readable_of_writable (hwd a h1 h2))
  have run := (run1.trans run2').trans (run3.trans (run4.trans (run5.trans run6)))
  refine .inl ⟨s1, ω6, μ6, _, ptr, run, k1.trans g1, ?_, ?_, by omega, by omega, H6, hnew, hfresh,
    fun d hd hu => ⟨keep2 d hd hu, fun a ha => ?_⟩, tag, fun a h0 ha hb => ?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [k5, (gj 5 (by decide)), d5, (cj 5 (by decide)), f5, (bj 5 (by decide))]
  · rw [k6, (gj 6 (by decide)), d6, c6]
  · -- a chunk of s₀: its data is apart from the new block
    have hd2 := keep2 d hd hu
    have hne := hfresh d hd hu
    have hap := Services.Bootstrap.Decode.LoopA.InData.apart H2.wf hd2 hnew (Ne.symm hne) ha
    unfold Services.Bootstrap.Decode.LoopA.InData at hap
    dsimp only at hap
    have := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hd2 hu
    unfold InDataA at ha
    rw [fr6 a (by omega) (.inl (by omega)) (.inl (by omega)), fr4 a (by omega) (by omega) (.inl (by omega))]
    exact HKeepG.data H2.wf H2.hb0 H2.hbT hkg hd2 ha
  · rw [fr6 a h0 (.inr ha) hb, fr4 a h0 (.inr (by omega)) (.inr ha), stk2 a h0 ha]
  · rw [fr6 a (by omega) (.inl (by omega)) (.inl (by omega)), fr4 a (by omega) (.inl (by omega)) (.inl (by omega)),
      kro.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (hro a ha)]
  · have hp := kro.1 (a / pageSize) (.inl (by unfold pageSize; omega))
    rw [rd6, rd4]; unfold Memory.readable; rw [hp]

end Services.Bootstrap.Acc
