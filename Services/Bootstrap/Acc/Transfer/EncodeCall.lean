import Services.Bootstrap.Acc.Transfer.Encode
import Services.Bootstrap.Acc.Transfer.GetKeyCall

/-!
# The record's encoding, composed (40494 → 7888)

`enc_call`: from `alloc(140, 1)` at the helper's entry, the `Vec` filled with ℰ₄(source) ++
ℰ₈(amount) ++ memo by three `extend_from_slice` calls and copied to out, then the return to 7888; or
`alloc` returned null (the `heap` abort, the trap at 34178). The context and the stream are kept.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- `alloc`'s return (40611) to 34071 (ω₀ = 1576). -/
theorem enc_j0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1576) : FreeStepsH p R 40611 ω μ x 34071 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

open Picoalloc Services.Bootstrap.Decode.HeapCtx in
/-- **The record's encoding, 40494 → 7888**: from `alloc(140, 1)` with the helper's frame at s
    (return 272 at s + 56, ω₅ / ω₆ at s + 48 / + 40), out = ω₅ and the record st = ω₆ (the amount at
    st, the u32 source at st + 8, the memo's 128 octets at st + 12): either the `Vec { 140, ptr, 140 }`
    at out holds ℰ₄(source) ++ ℰ₈(amount) ++ memo in a fresh chunk, the run returns to 7888 with ω₁ =
    s + 64 and ω₅, ω₆ restored, the allocator's context for a state keeping every allocated chunk and
    its data, and the stack from s + 64 up kept off out; or `alloc` returned null and the run reaches
    the trap at 34178. -/
theorem enc_call (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) {hb : Nat} (s₀ : State) (s st out src am r5 r6 S0 S1 : Nat)
    (memo : List UInt8) (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h0 : ω[0] = UInt64.ofNat 1576) (h1 : ω[1] = UInt64.ofNat s) (h7 : ω[7] = UInt64.ofNat 140)
    (h8 : ω[8] = UInt64.ofNat 1) (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat st)
    (hs : 2147483800 + 128 ≤ s ∧ s % 8 = 0) (hSTk : S0 + 300 ≤ s ∧ s + 64 ≤ S1)
    (hst : s + 64 ≤ st ∧ st + 160 ≤ S1) (hout : s + 64 ≤ out ∧ out + 24 ≤ S1)
    (dso : out + 24 ≤ st ∨ st + 140 ≤ out)
    (m56 : rdN μ (s + 56) 8 = 272) (m48 : rdN μ (s + 48) 8 = r5) (m40 : rdN μ (s + 40) 8 = r6)
    (msrc : rdN μ (st + 8) 4 = src) (mam : rdN μ st 8 = am) (mmemo : μ.readN (st + 12) 128 = memo) :
    (∃ s' ω' μ' n ptr, FreeStepsH p (KeepCtx (accContractS env)) 40494 ω μ (c, f) 7888 ω' μ' (c, f) n ∧
      ω'[1] = UInt64.ofNat (s + 64) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      rdN μ' out 8 = 140 ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = 140 ∧
      μ'.readN ptr 140 = Num.encodeLE 4 src ++ Num.encodeLE 8 am ++ memo ∧
      (⟨ptr - 32, (140 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ≠ ⟨ptr - 32, (140 + 31) / 32 + 1, true⟩) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s₀, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → s + 64 ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 40494 ω μ (c, f) 34071 ω' μ' (c, f) n ∧
      ω'[7] = UInt64.ofNat 0 ∧
      FreeStepsH p (KeepCtx (accContractS env)) 34071 ω' μ' (c, f) 34178 ω' μ' (c, f) 1) := by
  have hst0 := H.st
  have hS1 := H.hS1
  rcases alloc_callG (p := p) (P := P) (hb := hb) (accHeapHost env) cap hcap1 hcap c ω μ s₀ s 140 1 pb S0 S1 H
      h1 h7 h8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨ptr, s1, ω1, μ1, -, run1, H1, keep1, hnew, hfresh, hkg, e7, stk1, f0, f1, f5, f6⟩ |
    ⟨-, ω1, μ1, run1, e7, stk1, f0, f1, f5, f6⟩
  · obtain ⟨-, run1S⟩ := FreeStepsH.growS f run1
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0 := H1.hb0
    have hbT := H1.hbT
    have hst1 := H1.st
    have run1' := run1S.trans (enc_j0 (p := p) (P := P) _ ω1 μ1 (f0.trans h0))
    have hwd : ∀ a, ptr ≤ a → a < ptr + 140 → μ1.writable a = true := fun a h1 h2 =>
      heapC_writable_data H1 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩
    -- the record, from the entry
    have kst1 : ∀ o n, s + 64 ≤ o → o + n ≤ 4294967296 → μ1.readN o n = μ.readN o n := fun o n h1 h2 =>
      PVM.Memory.readN_congr fun j hj => stk1 _ (by omega) (by omega)
    -- 34071 → 58508
    obtain ⟨ω2, μ2, run2, a0, a1, a7, a8, a9, a5, a6, v8, v16, v24, m0', m32, fr2, rd2, wr2⟩ :=
      enc_a (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω1 μ1 s st ptr src (f1.trans h1)
        (f6.trans h6) e7 (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (fun a h1 h2 => hst1 a (by omega) (by omega))
        (fun a h1 h2 => Memory.readable_of_writable (hst1 a (by omega) (by omega)))
        (.inr (by omega)) (by rw [← msrc]; unfold rdN; rw [kst1 _ _ (by omega) (by omega)])
    have hwf2 : ∀ a, s - 80 ≤ a → a < s + 64 → μ2.writable a = true := fun a h1 h2 => by
      rw [wr2]; exact hst1 a (by omega) (by omega)
    have hrf2 : ∀ a, s - 80 ≤ a → a < s + 64 → μ2.readable a = true := fun a h1 h2 => by
      rw [rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega))
    -- 58508 → 34112: ℰ₄(source)
    obtain ⟨ω3, μ3, run3, b0, b1, b5, b6, dat3, len3, frm3, rd3, wr3⟩ :=
      Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 s (s + 8) (s + 32) 4 140 ptr 0 1578 34112
        ⟨by omega, by omega, hs.2⟩ a0 a1 a7 a8 a9 (by omega) (by decide) v8 v16 v24 (by omega)
        (.inr (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega))
        (.inl (by omega)) (.inr (by omega)) ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_788]) bs_34112
        (fun a h1 h2 => hrf2 a (by omega) (by omega)) (fun a h1 h2 => hwf2 a (by omega) (by omega))
        (fun a h1 h2 => hrf2 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr2]; exact hwd a (by omega) (by omega))
        (fun a h1 h2 => hwf2 a (by omega) (by omega))
    have hwd2 : ∀ a, ptr ≤ a → a < ptr + 140 → μ2.writable a = true := fun a h1 h2 => by rw [wr2]; exact hwd a h1 h2
    -- 34112 → 58508: ℰ₈(amount)
    have kA : ∀ a, a < 4294967296 → s + 40 ≤ a → μ3.read a = μ1.read a := fun a h0 ha => by
      rw [frm3 a h0 (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), fr2 a h0 (.inr (by omega))]
    obtain ⟨ω4, μ4, run4, c0, c1, c7, c8, c9, c5, c6, m32b, fr4, rd4, wr4⟩ :=
      enc_b (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω3 μ3 s st am b1 (b6.trans a6)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr3]; exact hwf2 a (by omega) (by omega))
        (fun a h1 h2 => by rw [rd3, rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))
        (by rw [← mam]; unfold rdN; congr 1
            exact (PVM.Memory.readN_congr fun j hj => kA _ (by omega) (by omega)).trans (kst1 _ _ (by omega) (by omega)))
    have hwf4 : ∀ a, s - 80 ≤ a → a < s + 64 → μ4.writable a = true := fun a h1 h2 => by
      rw [wr4, wr3]; exact hwf2 a h1 h2
    have hrf4 : ∀ a, s - 80 ≤ a → a < s + 64 → μ4.readable a = true := fun a h1 h2 => by
      rw [rd4, rd3]; exact hrf2 a h1 h2
    -- the Vec's words at 34112 and after
    have k34 : ∀ o, s + 8 ≤ o → o + 8 ≤ s + 24 → μ4.readN o 8 = μ2.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => by
        rw [fr4 _ (by omega) (.inl (by omega)), frm3 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
    have l24 : μ4.readN (s + 24) 8 = Num.encodeLE 8 4 := by
      rw [PVM.Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega))]; exact len3
    obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, dat5, len5, frm5, rd5, wr5⟩ :=
      Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 s (s + 8) (s + 32) 8 140 ptr 4 1580 34132
        ⟨by omega, by omega, hs.2⟩ c0 c1 c7 c8 c9 (by omega) (by decide)
        (by rw [k34 _ (by omega) (by omega)]; exact v8) (by rw [k34 _ (by omega) (by omega)]; exact v16) l24 (by omega)
        (.inr (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega))
        (.inl (by omega)) (.inr (by omega)) ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_789]) bs_34132
        (fun a h1 h2 => hrf4 a (by omega) (by omega)) (fun a h1 h2 => hwf4 a (by omega) (by omega))
        (fun a h1 h2 => hrf4 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr4, wr3]; exact hwd2 a (by omega) (by omega))
        (fun a h1 h2 => hwf4 a (by omega) (by omega))
    -- 34132 → 58508: the memo
    have k5s : rdN μ5 s 8 = st + 12 := by
      rw [← m0']; unfold rdN; congr 1
      exact PVM.Memory.readN_congr fun j hj => by
        rw [frm5 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega)), fr4 _ (by omega) (.inl (by omega)),
          frm3 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
    obtain ⟨ω6, run6, e0, e1, e7', e8, e9, e5, e6⟩ :=
      enc_c (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω5 μ5 s (st + 12) d1 ⟨by omega, by omega⟩
        (fun a h1 h2 => by rw [rd5]; exact hrf4 a (by omega) (by omega)) k5s
    have k56 : ∀ o, s + 8 ≤ o → o + 8 ≤ s + 24 → μ5.readN o 8 = μ2.readN o 8 := fun o h1 h2 =>
      (PVM.Memory.readN_congr fun j hj => frm5 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))).trans
        (k34 o h1 h2)
    have kM : ∀ a, a < 4294967296 → s + 64 ≤ a → μ5.read a = μ1.read a := fun a h0 ha => by
      rw [frm5 a h0 (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), fr4 a h0 (.inr (by omega)), kA a h0 (by omega)]
    have kM' : ∀ a, a < 4294967296 → s + 40 ≤ a → μ5.read a = μ.read a := fun a h0 ha => by
      rw [frm5 a h0 (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), fr4 a h0 (.inr (by omega)),
        frm3 a h0 (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), fr2 a h0 (.inr (by omega)),
        stk1 a h0 (by omega)]
    obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, dat7, len7, frm7, rd7, wr7⟩ :=
      Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω6 μ5 s (s + 8) (st + 12) 128 140 ptr 12 1582 34147
        ⟨by omega, by omega, hs.2⟩ e0 e1 e7' e8 e9 (by omega) (by decide)
        (by rw [k56 _ (by omega) (by omega)]; exact v8) (by rw [k56 _ (by omega) (by omega)]; exact v16) len5 (by omega)
        (.inr (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega))
        (.inl (by omega)) (.inr (by omega)) ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_790]) bs_34147
        (fun a h1 h2 => by rw [rd5]; exact hrf4 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr5]; exact hwf4 a (by omega) (by omega))
        (fun a h1 h2 => by rw [rd5, rd4, rd3, rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wr5, wr4, wr3]; exact hwd2 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr5]; exact hwf4 a (by omega) (by omega))
    -- 34147 → 34176 → 7888
    have kH : ∀ a, a < 4294967296 → s + 40 ≤ a → μ7.read a = μ.read a := fun a h0 ha => by
      rw [frm7 a h0 (.inr (by omega)) (.inr (by omega)) (.inr (by omega)), kM' a h0 ha]
    have toR : ∀ {μ' : Memory} {a v : Nat}, μ'.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 →
        rdN μ' a 8 = v := fun h hv => by unfold rdN; rw [h, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hv
    have k7v : ∀ o, s + 8 ≤ o → o + 8 ≤ s + 24 → μ7.readN o 8 = μ2.readN o 8 := fun o h1 h2 =>
      (PVM.Memory.readN_congr fun j hj => frm7 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))).trans
        (k56 o h1 h2)
    have kF : ∀ o, s + 40 ≤ o → o + 8 ≤ s + 64 → rdN μ7 o 8 = rdN μ o 8 := fun o h1 h2 => by
      unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => kH _ (by omega) (by omega)
    obtain ⟨ω8, μ8, run8, i0, i5, i6, i1, o0, o8, o16, fr8, rd8, wr8⟩ :=
      enc_ret (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω7 μ7 s out 140 ptr 140 272 r5 r6 g1
        (g5.trans (e5.trans (d5.trans (c5.trans (b5.trans (a5.trans (f5.trans h5)))))))
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega))
        (fun a h1 h2 => by rw [rd7, rd5]; exact hrf4 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr7, wr5, wr4, wr3, wr2]; exact hst1 a (by omega) (by omega))
        (toR (by rw [k7v _ (by omega) (by omega)]; exact v8) (by decide))
        (toR (by rw [k7v _ (by omega) (by omega)]; exact v16) (by omega))
        (toR len7 (by decide))
        (by rw [kF _ (by omega) (by omega)]; exact m56) (by rw [kF _ (by omega) (by omega)]; exact m48)
        (by rw [kF _ (by omega) (by omega)]; exact m40)
    have run9 := enc_j (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω8 μ8 i0
    -- the heap context: stack writes and the new chunk's data
    have H8 : HeapCtxC env.code pb S0 S1 μ8 s1 := by
      have hc := hnew
      refine Services.Bootstrap.Acc.HeapCtxC.keep_hi ?_ (fun a ha => fr8 a (by omega) (.inl (by omega))) wr8
      refine Services.Bootstrap.Acc.HeapCtxC.keep_data ?_ hnew (fun a ha hc => frm7 a (by omega) (.inl (by omega))
        (by dsimp only at hc; omega) (.inl (by omega))) wr7
      refine Services.Bootstrap.Acc.HeapCtxC.keep_data ?_ hnew (fun a ha hc => frm5 a (by omega) (.inl (by omega))
        (by dsimp only at hc; omega) (.inl (by omega))) wr5
      refine Services.Bootstrap.Acc.HeapCtxC.keep_hi ?_ (fun a ha => fr4 a (by omega) (.inl (by omega))) wr4
      refine Services.Bootstrap.Acc.HeapCtxC.keep_data ?_ hnew (fun a ha hc => frm3 a (by omega) (.inl (by omega))
        (by dsimp only at hc; omega) (.inl (by omega))) wr3
      exact Services.Bootstrap.Acc.HeapCtxC.keep_hi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
    -- the heap below the stack: each write is the new chunk's data
    have kL : ∀ a, a < 2147483648 → (a < ptr ∨ ptr + 140 ≤ a) → μ8.read a = μ1.read a := fun a ha hp => by
      rw [fr8 a (by omega) (.inl (by omega)), frm7 a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)),
        frm5 a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)), fr4 a (by omega) (.inl (by omega)),
        frm3 a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)), fr2 a (by omega) (.inl (by omega))]
    refine .inl ⟨s1, ω8, μ8, _, ptr, (((((((run1'.trans run2).trans run3).trans run4).trans run5).trans run6).trans
      run7).trans run8).trans run9, i1, i5, i6, o0, o8, o16, ?_, hnew, hfresh, H8, keep1, ?_, ?_⟩
    · -- the value: ℰ₄(source), then ℰ₈(amount), then the memo
      have p8 : ∀ a, ptr ≤ a → a < ptr + 140 → μ8.read a = μ7.read a := fun a h1 h2 =>
        fr8 a (by omega) (.inl (by omega))
      have q8 : ∀ o n, ptr ≤ o → o + n ≤ ptr + 140 → μ8.readN o n = μ7.readN o n := fun o n h1 h2 =>
        PVM.Memory.readN_congr fun j hj => p8 _ (by omega) (by omega)
      rw [show (140 : Nat) = 4 + 8 + 128 from rfl, Memory.readN_split, Memory.readN_split,
        q8 ptr 4 (by omega) (by omega), q8 (ptr + 4) 8 (by omega) (by omega), q8 (ptr + 4 + 8) 128 (by omega) (by omega)]
      congr 1; congr 1
      · rw [PVM.Memory.readN_congr fun j hj => frm7 _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
          PVM.Memory.readN_congr fun j hj => frm5 _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
          PVM.Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega)), show ptr = ptr + 0 from rfl, dat3]
        exact readN_of_rdN m32
      · rw [PVM.Memory.readN_congr fun j hj => frm7 _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
          show ptr + 4 = ptr + 4 + 0 from rfl, dat5]
        exact readN_of_rdN m32b
      · rw [show ptr + 4 + 8 = ptr + 12 by omega, dat7, ← mmemo]
        exact PVM.Memory.readN_congr fun j hj => by rw [kM _ (by omega) (by omega), stk1 _ (by omega) (by omega)]
    · intro d hd hu a ha
      have hd1 := keep1 d hd hu
      have hne := hfresh d hd hu
      have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hd1 hu
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H1.wf hd1 hnew (Ne.symm hne) ha
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      dsimp only at hap
      unfold InDataA at ha
      rw [kL a (by omega) (by omega)]
      exact HKeepG.data H1.wf H1.hb0 H1.hbT hkg hd1 ha
    · intro a h0 ha ho
      rw [fr8 a h0 ho]; exact kH a h0 (by omega)
  · obtain ⟨-, run1S⟩ := FreeStepsH.growS f run1
    exact .inr ⟨ω1, μ1, _, run1S.trans (enc_j0 (p := p) (P := P) _ ω1 μ1 (f0.trans h0)), e7,
      enc_null (p := p) (P := P) _ ω1 μ1 e7⟩

end Services.Bootstrap.Acc
