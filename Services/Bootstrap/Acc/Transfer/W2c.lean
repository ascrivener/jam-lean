import Services.Bootstrap.Acc.Transfer.W2b
import Services.Bootstrap.Acc.Transfer.Tail2
import Services.Bootstrap.Acc.Transfer.EncodeCall

/-!
# `on_transfer`, from the log line to the second `set` (7763 → 48104)

`tr_w2c` composes `t2_kfmt_pre`, `format!("transfer{n}")` (`KeyFmt`), `t2_rec`, `memcpy_val` (the memo
into the record at sp + 1580), `t2_enc_pre`, `enc_call` (ℰ₄(source) ++ ℰ₈(amount) ++ memo; null: the
trap at 34178) and `t2_set`. The context and the stream are kept.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The key of Spec `onTransfer`'s second write. -/
def trKey2 (n : Nat) : List UInt8 := (s!"transfer{n}").toUTF8.toList

/-- The scratch words from sp up that 7763 … 48104 writes. -/
def T2W (sp a : Nat) : Prop :=
  (sp + 248 ≤ a ∧ a < sp + 256) ∨ (sp + 512 ≤ a ∧ a < sp + 536) ∨ (sp + 744 ≤ a ∧ a < sp + 768) ∨
  (sp + 1568 ≤ a ∧ a < sp + 1708)

/-- **7763 → 48104**: the key "transfer{n}" formatted into a live chunk kch (its `String` at sp + 512),
    the record encoded into a fresh 140-octet chunk vch (its `Vec` at sp + 744), and `set(out = sp + 264,
    key, value)` entered (return 274). Every allocated chunk of s₀ kept, with its data, and apart from
    kch and vch; from sp up only `T2W` changed. Or an allocation failed (34178, or `ExhaustsP`). -/
theorem tr_w2c (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hK : KeyFmt p env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp n src am : Nat) (memo : List UInt8)
    (H : HeapCtxC env.code pb S0 S1 μ s₀) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1)
    (m208 : rdN μ (sp + 208) 8 = 2800) (m1496 : rdN μ (sp + 1496) 4 = n) (hn : n < 4294967296)
    (m472 : rdN μ (sp + 472) 4 = src) (m1000 : rdN μ (sp + 1000) 8 = am)
    (mmemo : μ.readN (sp + 1144) 128 = memo) :
    (∃ s' ω' μ' N kc kp vp, ∃ kch vch : Chunk,
      FreeStepsH p (KeepCtx (accContractS env)) 7763 ω μ (c, f) 48104 ω' μ' (c, f) N ∧
      ω'[0] = UInt64.ofNat 274 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 264) ∧
      ω'[8] = UInt64.ofNat kp ∧ ω'[9] = UInt64.ofNat (trKey2 n).length ∧ ω'[10] = UInt64.ofNat vp ∧
      ω'[11] = UInt64.ofNat 140 ∧ ω'[6] = UInt64.ofNat vp ∧ ω'[5] = UInt64.ofNat kp ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      rdN μ' (sp + 512) 8 = kc ∧ kch ∈ chunks s' ∧ kch.used = true ∧ kch.addr + 32 = kp ∧
      (∀ a, kp ≤ a → a < kp + (trKey2 n).length → InDataA kch a) ∧
      μ'.readN kp (trKey2 n).length = trKey2 n ∧
      rdN μ' (sp + 744) 8 = 140 ∧ rdN μ' (sp + 752) 8 = vp ∧
      vch ∈ chunks s' ∧ vch.used = true ∧ vch.addr + 32 = vp ∧ vch ≠ kch ∧
      (∀ a, vp ≤ a → a < vp + 140 → InDataA vch a) ∧
      μ'.readN vp 140 = Num.encodeLE 4 src ++ Num.encodeLE 8 am ++ memo ∧
      (∀ d ∈ chunks s₀, d.used = true → d ≠ kch ∧ d ≠ vch ∧ d ∈ chunks s' ∧
        ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → ¬ T2W sp a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Aborts p (KeepCtx (accContractS env)) Ab ⟨7763, ω, μ, c, f⟩ c := by
  have hst := H.st
  have hS1 := H.hS1
  have hwS : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  -- 7763 → 59375 → 7799: the key
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, a5, a6, r1568, r1576, fr1, rd1, wr1⟩ :=
    t2_kfmt_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 ⟨by omega, by omega⟩ hwS
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
    HeapCtxC.keep_hi H (fun a ha => fr1 a (by omega) (.inl (by omega))) wr1
  have k10 : ∀ o n, o + n ≤ sp + 1568 → rdN μ1 o n = rdN μ o n := fun o n h =>
    rdN_frame fun j hj => fr1 _ (by omega) (.inl (by omega))
  rcases hK c f ω1 μ1 s₀ sp n H1 a0 a1 a7 a8 a9 (by omega) (by omega) (by omega) r1568 (r1576.trans m208)
      (by rw [k10 _ _ (by omega)]; exact m1496) hn with
    ⟨s2, ω2, μ2, N2, kc, kp, run2, H2, k1, k5, k6, mkc, mkp, mkl, mkey,
      ⟨kch, hkch, hkcu, hkca, hkcf, hkin⟩, keep2, fr2, g2⟩ | hx
  rotate_left
  · exact .inr (Aborts.prepend ⟨8, run1⟩ (aborts_of_exhaustsP hAb ⟨59375, ω1, μ1, c, f⟩ hx))
  have hst2 := H2.st
  have k20 : ∀ o n, sp ≤ o → o + n ≤ sp + 512 → rdN μ2 o n = rdN μ o n := fun o n h1 h2 =>
    (rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega))).trans (k10 _ _ (by omega))
  have k20' : ∀ o n, sp + 536 ≤ o → o + n ≤ sp + 1568 → rdN μ2 o n = rdN μ o n := fun o n h1 h2 =>
    (rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inr (by omega))).trans (k10 _ _ (by omega))
  obtain ⟨Nk1, Nk2, Nk3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hkch hkcu
  have hb0 := H2.hb0
  have hbT := H2.hbT
  -- 7799 → 68729 → 7846: the record
  obtain ⟨ω3, μ3, run3, b0, b1, b7, b8, b9, b5, b6, r248, r1568', r1576', fr3, rd3, wr3⟩ :=
    t2_rec (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 sp src am kp (trKey2 n).length
      (k1.trans a1) ⟨by omega, by omega⟩ (fun a h1 h2 => hst2 a (by omega) (by omega))
      (by rw [k20 _ _ (by omega) (by omega)]; exact m472) (by rw [k20' _ _ (by omega) (by omega)]; exact m1000)
      mkp mkl
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, cp4, fr4, rd4, wr4⟩ := memcpy_val (p := p) (P := P)
    (R := KeepCtx (accContractS env)) (c, f) ω3 μ3 270 7846 sp (sp + 1580) (sp + 1144) 128 b0 b1 b7 b8 b9
    (by decide) jte_134 bs_7846 ⟨by omega, by omega, hsp.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (.inr (by omega)) (.inl (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd3]; exact Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr3]; exact hst2 a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3]; exact hst2 a (by omega) (by omega))
  -- 7846 → 40494: the encoder's frame
  obtain ⟨ω5, μ5, run5, g0, g1, g7, g8, g5, g6, r56, r48, r40, fr5, rd5, wr5⟩ :=
    t2_enc_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 sp (d1.trans b1)
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr4, wr3]; exact hst2 a (by omega) (by omega))
  have fr52 : ∀ a, a < 2147483648 → μ5.read a = μ2.read a := fun a ha => by
    rw [fr5 a (by omega) (.inl (by omega)), fr4 a (by omega) (.inl (by omega)) (.inl (by omega)),
      fr3 a (by omega) (.inl (by omega)) (.inl (by omega))]
  have H5 : HeapCtxC env.code pb S0 S1 μ5 s2 :=
    HeapCtxC.keep_hi H2 fr52 (fun a => by rw [wr5, wr4, wr3])
  have fr53 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1580 ∨ sp + 1708 ≤ a) → μ5.read a = μ3.read a :=
    fun a h0 ha hb => by rw [fr5 a h0 (.inr ha), fr4 a h0 hb (.inr ha)]
  have hkp : kp < 18446744073709551616 := mkp ▸ rdN_lt64 _ _
  have hkp5 : ω4[5].toNat = kp := by rw [d5, b5, UInt64.toNat_ofNat_of_lt' (show kp < 2 ^ 64 by omega)]
  -- 40494 → 7888: the encoding
  rcases enc_call env cap pb hcap1 hcap (p := p) (P := P) (hb := 0) c f ω5 μ5 s2 (sp - 64) (sp + 1568) (sp + 744)
      src am ω4[5].toNat ω4[6].toNat S0 S1 memo H5 g0 g1 g7 g8 g5 g6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) r56 r48 r40
      (by rw [rdN_frame fun j hj => fr53 _ (by omega) (by omega) (.inl (by omega))]; exact r1576')
      (by rw [rdN_frame fun j hj => fr53 _ (by omega) (by omega) (.inl (by omega))]; exact r1568')
      (by
        rw [show sp + 1568 + 12 = sp + 1580 by omega, Memory.readN_congr fun j hj => fr5 _ (by omega) (.inr (by omega)),
          cp4, Memory.readN_congr fun j hj => fr3 _ (by omega) (.inr (by omega)) (.inl (by omega)),
          Memory.readN_congr fun j hj => fr2 _ (by omega) (by omega) (.inr (by omega)),
          Memory.readN_congr fun j hj => fr1 _ (by omega) (.inl (by omega))]
        exact mmemo) with
    ⟨s3, ω6, μ6, n6, vp, run6, e1, e5, e6, o0, o8, o16, vdat, hvch, hvfr, H6, kch6, kdat6, khi6, g6⟩ |
    ⟨ω6, μ6, n6, run6, -, run6b⟩
  rotate_left
  · exact .inr (aborts_of_trap (P := P) (fun s h => hAb s (.inl h)) ⟨7763, ω, μ, c, f⟩
      (.inr (.inr (.inr (.inr (.inr rfl)))))
      ((run1.trans run2).trans (run3.trans (run4.trans (run5.trans (run6.trans run6b))))))
  have hst6 := H6.st
  obtain ⟨Nv1, Nv2, Nv3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H6.wf hvch rfl
  dsimp only at Nv1 Nv2 Nv3
  have hb6 := H6.hb0
  have e1' : ω6[1] = UInt64.ofNat sp := by rw [e1]; congr 1; omega
  have k63 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → (o + n ≤ sp + 744 ∨ sp + 768 ≤ o) →
      (o + n ≤ sp + 1580 ∨ sp + 1708 ≤ o) → rdN μ6 o n = rdN μ3 o n := fun o n h1 h2 h3 h4 =>
    rdN_frame fun j hj => by rw [khi6 _ (by omega) (by omega) (by omega)]; exact fr53 _ (by omega) (by omega) (by omega)
  -- 7888 → 48104
  obtain ⟨ω7, run7, j0, j1, j7, j8, j9, j10, j11, j6, j5⟩ :=
    t2_set (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω6 μ6 sp (trKey2 n).length vp 140 e1'
      ⟨by omega, by omega⟩ (fun a h1 h2 => Memory.readable_of_writable (hst6 a (by omega) (by omega)))
      (by rw [k63 _ _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega))]; exact r248)
      (by rw [show sp + 752 = sp + 744 + 8 by omega]; exact o8)
      (by rw [show sp + 760 = sp + 744 + 16 by omega]; exact o16)
  have hkv : (⟨vp - 32, (140 + 31) / 32 + 1, true⟩ : Chunk) ≠ kch := fun h => hvfr kch hkch hkcu h.symm
  have hkch6 := kch6 kch hkch hkcu
  -- the key's octets, kept by everything after `KeyFmt`
  have keyD : ∀ a, kp ≤ a → a < kp + (trKey2 n).length → μ6.read a = μ2.read a := fun a h1 h2 => by
    have ha := hkin a h1 h2
    have hlt := heapC_data_lt H2 hkch ha
    rw [kdat6 kch hkch hkcu a ha, fr52 a hlt.2]
  refine .inl ⟨s3, ω7, μ6, _, kc, kp, vp, kch, ⟨vp - 32, (140 + 31) / 32 + 1, true⟩,
    (run1.trans run2).trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))),
    j0, j1, j7, ?_, j9, j10, j11, j6, ?_, H6, ?_, hkch6, hkcu, hkca, hkin, ?_, o0, ?_, hvch, rfl,
    by dsimp only; omega, hkv, fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩, vdat,
    fun d hd hu => ?_, fun a h0 ha hW => ?_, fun a hg => ?_⟩
  · rw [j8, e5, hkp5]
  · rw [j5, e5, hkp5]
  · rw [k63 _ _ (by omega) (by omega) (.inl (by omega)) (.inl (by omega))]
    rw [rdN_frame fun j hj => fr3 _ (by omega) (.inr (by omega)) (.inl (by omega))]; exact mkc
  · rw [Memory.readN_congr fun j hj => keyD _ (by omega) (by omega)]; exact mkey
  · rw [show sp + 752 = sp + 744 + 8 by omega]; exact o8
  · obtain ⟨hd2, hdat2⟩ := keep2 d hd hu
    have hne : d ≠ kch := hkcf d hd hu
    refine ⟨hne, hvfr d hd2 hu, kch6 d hd2 hu, fun a ha => ?_⟩
    have hlt := heapC_data_lt H hd ha
    rw [kdat6 d hd2 hu a ha, fr52 a (by omega), hdat2 a ha, fr1 a (by omega) (.inl (by omega))]
  · unfold T2W at hW
    rw [khi6 a h0 (by omega) (by omega), fr53 a h0 ha (by omega), fr3 a h0 (by omega) (by omega),
      fr2 a h0 ha (by omega), fr1 a h0 (by omega)]
  · have ha := hg; unfold Glob at ha
    rw [g6 a hg, fr52 a (by omega), g2 a hg, fr1 a (by omega) (.inl (by omega))]

end Services.Bootstrap.Acc
