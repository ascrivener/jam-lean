import Services.Bootstrap.Acc.Inputs.FetchVecCall
import Services.Bootstrap.Acc.Inputs.InputsSpec

/-!
# The accumulation inputs decoded, 6630 → 6674

The inputs function of the accumulate entry (6630 … 6674, see the Acc README): `fetch_vec(14)` fetches
ℰ(↕**i**) (GP v0.8.0 Appendix B, `fetch`; §12, the accumulation inputs **i**) into a fresh block, the
`Vec<AccumulateItem>` decoder turns it into n 184-octet slots in a fresh buffer, the fetched block is
freed, and `Vec { n, q, n }` is stored at the caller's sp + 1568. Each slot holds the model's input
(`itemOf`, whose encoding is the model's ℰ: `itemOf_enc`). The temporary bounds: at most 89 inputs, each
work output and auth trace at most 16384 octets (`InputSized`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The accumulation inputs decoded, 6630 → 6674** (GP v0.8.0 §12; at most 89 inputs, each within
    `InputSized`): under the accumulate contract, from the allocator's context. Either
    `Vec { n, q, n }` (n = |**i**|) is stored at sp + 1568, slot j of the buffer at q holding input j
    (`itemOf`) for any memory agreeing on the final state's allocated data, the context holds for the
    final state keeping every allocated chunk and its data, the stack from sp is kept off the output,
    and ω₁, ω₅, ω₆ are as at the call; or the allocator is exhausted (the traps 47554, 45975, 45642). -/
theorem inputs_decode (aenv : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) (hcost : 287 + memGas 400 (inputsEnc aenv).length ≤ cap)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : AccCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s0 : State) (sp S0 S1 : Nat)
    (H : HeapCtxC aenv.code pb S0 S1 μ s0) (h1 : ω[1] = UInt64.ofNat sp)
    (hn : aenv.inputs.length ≤ 89) (hsz : ∀ i ∈ aenv.inputs, InputSized i)
    (hL : (inputsEnc aenv).length + 31 < 68719476736)
    (hsp : 2147483960 + 424 + 480 + 144 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 864 + 480 + 144 ≤ sp)
    (hS : sp + 1568 + 24 ≤ S1) :
    (∃ q st' ω' μ', FreeStepsH p (accContractK cap aenv) 6630 ω μ x 6674 ω' μ' x
        (96 * (((inputsEnc aenv).length + 31) / 32) + (itemSteps + 2100) * aenv.inputs.length + 2700) ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 1568) 8 = aenv.inputs.length ∧ rdN μ' (sp + 1568 + 8) 8 = q ∧
      rdN μ' (sp + 1568 + 16) 8 = aenv.inputs.length ∧
      HeapCtxC aenv.code pb S0 S1 μ' st' ∧
      (∀ c ∈ chunks s0, c.used = true → c ∈ chunks st' ∧ ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∀ (j : Nat) (i : AccumulateInput), aenv.inputs[j]? = some i →
        ∀ μ'' : Memory, (∀ c ∈ chunks st', c.used = true → ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          (itemOf i).2 (μ''.readN (q + 184 * j) 184) μ'') ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1568 + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ j ω' μ', (j = 47554 ∨ j = 45975 ∨ j = 45642) ∧
      FreeStepsH p (accContractK cap aenv) 6630 ω μ x j ω' μ' x
        (96 * (((inputsEnc aenv).length + 31) / 32) + (itemSteps + 2100) * aenv.inputs.length + 2700)) := by
  have hS1 := H.hS1
  have hst := H.st
  have hL0 : 0 < (inputsEnc aenv).length := by
    rw [inputsEnc_items aenv (by omega)]; simp
  -- 6630 → 47417
  obtain ⟨ω1, μ1, r1, a0, a1, a7, a8, s136, s128, s120, s8, s32, fr1, rd1, wr1, k1⟩ :=
    in_pre (p := p) (P := P) (R := accContractK cap aenv) x ω μ sp h1 ⟨by omega, by omega⟩
      (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl (by omega))
  have H1 : HeapCtxC aenv.code pb S0 S1 μ1 s0 := HeapCtxC.keep_hi H lo1 wr1
  -- 47417 → 47722
  rcases fv_call (p := p) (P := P) (hb := hb) aenv cap pb hcap1 hcap hcost x ω1 μ1 s0 (sp - 144) (sp - 144 + 56) (sp - 144 + 32)
      (rdN μ1 (sp - 144 + 40) 8) (rdN μ1 (sp - 144 + 48) 8) S0 S1 H1 a1 a7 a8 hL0 hL (by omega) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) s32
      (by have := encodeLE_decodeLE (μ1.readN (sp - 144 + 32 + 8) 8); simp only [Memory.length_readN] at this
          rw [show sp - 144 + 32 + 8 = sp - 144 + 40 by omega] at this ⊢; unfold rdN; exact this.symm)
      (by have := encodeLE_decodeLE (μ1.readN (sp - 144 + 32 + 16) 8); simp only [Memory.length_readN] at this
          rw [show sp - 144 + 32 + 16 = sp - 144 + 48 by omega] at this ⊢; unfold rdN; exact this.symm)
      (rdN_lt64 _ _) (rdN_lt64 _ _) with
    ⟨ptr, s1, ω2, μ2, r2, b0, b1, b5, b6, v0, v8, v16, H2, keep2, keepd2, hnew, hfresh, dat, fr2⟩ | ⟨ω2, μ2, r2⟩
  · have r3 := fv_ret (p := p) (P := P) (R := accContractK cap aenv) x ω2 μ2 (by rw [b0, a0])
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0' := H2.hb0
    have hbT' := H2.hbT
    have k2 : ∀ o, sp - 144 ≤ o → o + 8 ≤ sp - 144 + 56 ∨ sp - 144 + 80 ≤ o → o + 8 ≤ 4294967296 →
        rdN μ2 o 8 = rdN μ1 o 8 := fun o h1 h2 h3 =>
      rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega)
    rcases g_inputs (p := p) (P := P) (hb := hb) aenv cap pb hcap1 hcap x ω2 μ2 s1 (sp - 144) (sp + 1568)
        (inputsEnc aenv).length ptr (inputsEnc aenv).length S0 S1
        ⟨ptr - 32, ((inputsEnc aenv).length + 31) / 32 + 1, true⟩ hn hsz H2 b1
        (by rw [k2 _ (by omega) (Or.inl (by omega)) (by omega)]; exact s8)
        (by rw [show sp - 144 + 56 = sp - 144 + 56 from rfl]; exact v0)
        (by rw [show sp - 144 + 64 = sp - 144 + 56 + 8 by omega]; exact v8)
        (by rw [show sp - 144 + 72 = sp - 144 + 56 + 16 by omega]; exact v16)
        ⟨hL0, by omega⟩ hnew rfl (by dsimp only; omega) (by dsimp only; omega) ⟨Nat.le_refl _, by omega⟩ dat
        ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ with
      ⟨q, st', ω3, μ3, r4, z0, z1, z5, z6, o0, o8, o16, H3, kd, reps, fr⟩ | ⟨j, ω3, μ3, hj, r4⟩
    · have r5 := in_ret (p := p) (P := P) (R := accContractK cap aenv) x ω3 μ3
        (by rw [z0, k2 _ (by omega) (Or.inr (by omega)) (by omega), s136])
      refine Or.inl ⟨q, st', ω3, μ3, ((((r1.trans r2).trans r3).trans (FreeStepsH.ofAccGrow r4)).trans r5).mono
          (by omega),
        by rw [z1, show sp - 144 + 144 = sp by omega],
        by rw [z5, k2 _ (by omega) (Or.inr (by omega)) (by omega), s128, UInt64.ofNat_toNat],
        by rw [z6, k2 _ (by omega) (Or.inr (by omega)) (by omega), s120, UInt64.ofNat_toNat],
        o0, o8, o16, H3, fun c hc hu => ⟨(kd c (keep2 c hc hu) hu (hfresh c hc hu)).1, fun a ha => ?_⟩, reps,
        fun a h0 ha ho => ?_⟩
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
        have := H.hbT
        rw [(kd c (keep2 c hc hu) hu (hfresh c hc hu)).2 a ha, keepd2 c hc hu a ha]
        unfold InDataA at ha
        exact lo1 a (by omega)
      · rw [fr a h0 (by omega) ho, fr2 a h0 (by omega) (Or.inr (by omega)), fr1 a h0 (Or.inr ha)]
    · exact Or.inr ⟨j, ω3, μ3, Or.inr hj, (((r1.trans r2).trans r3).trans (FreeStepsH.ofAccGrow r4)).mono
        (by omega)⟩
  · exact Or.inr ⟨47554, ω2, μ2, Or.inl rfl, (r1.trans r2).mono (by omega)⟩

end Services.Bootstrap.Acc
