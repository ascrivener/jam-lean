import Services.Bootstrap.Acc.ItemsLoop.Inv
import Services.Bootstrap.Acc.Impl.Loop

/-!
# The items loop's transfer arm (R1)

From the loop head 6766 with a transfer next (`ItemsInv` for `.transfer x :: rest`): 6766 → 6782
(`il_step`), the dispatch 6782 → 7159 (`il_disp_tr`, the slot's first word −1), then `on_transfer`
(`tr_impl`, 7159 → 6766) implements `Spec.onTransfer x.source x.amount x.memo`; back at 6766,
`ItemsInv` holds for `rest`. This is the transfer case of the body of `Spec.accumulate`'s loop.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc
open JAM.Codec (fixed)
open Services.Bootstrap.ASem (writeAcct)

/-- `writeAcct` keeps an account's fit for a value shorter than 2⁶³. -/
theorem acctFit_writeAcct {a : ServiceAccount} (ha : AcctFit a) (key value : List UInt8)
    (hv : value.length < 2 ^ 63) : AcctFit (writeAcct a key value) := by
  unfold writeAcct
  split
  · refine ⟨fun k w hk => ?_, ha.2⟩
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at hk
    split at hk
    · cases hk
    · exact ha.1 k w hk
  · refine ⟨fun k w hk => ?_, ha.2⟩
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hk
    split at hk
    · cases hk; exact hv
    · exact ha.1 k w hk

/-- `ValuesFit` of the context after `onTransfer` (`trCtx`): two writes of short values. -/
theorem valuesFit_trCtx {env : AccEnv} {c : AccCtx} (h : ValuesFit env c.1) (src am : Nat)
    (memo : List UInt8) (hm : memo.length = 128) : ValuesFit env (trCtx c src am memo).1 := by
  rw [valuesFit_iff] at h ⊢
  refine ⟨?_, h.2⟩
  unfold trCtx
  dsimp only
  have h1 := impFit_setSelf h.1 (acctFit_writeAcct (acctFit_self h.1) trKey
    (fixed 4 ((trCount (c.1.self.storage.get? trKey) + 1) % 2 ^ 32)) (by simp [fixed]))
  refine impFit_setSelf h1 (acctFit_writeAcct (acctFit_self h1) _ _ ?_)
  simp [fixed, hm]

/-- The loop's stack words are not written by `on_transfer` (`TrW`). -/
theorem not_trW_loop {sp a : Nat}
    (h : (sp + 16 ≤ a ∧ a < sp + 24) ∨ (sp + 32 ≤ a ∧ a < sp + 40) ∨ (sp + 136 ≤ a ∧ a < sp + 152) ∨
      (sp + 168 ≤ a ∧ a < sp + 176) ∨ (sp + 184 ≤ a ∧ a < sp + 192) ∨ (sp + 200 ≤ a ∧ a < sp + 224) ∨
      (sp + 1848 ≤ a ∧ a < sp + 1856)) : ¬ TrW sp a := by
  unfold TrW TrRdW TrW2 LgW T2W
  omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The items loop's transfer arm**: from the loop head with a transfer x next, the run implements
    the loop body's transfer case, `onTransfer x.source x.amount x.memo` then `yield`, and returns to
    the loop head with `ItemsInv` for the rest. Early ☇ for any `Ab` holding at `HeapFailT` states.
    Named hypotheses (of `tr_impl`): `Utf8Call`, `LogFmt`, `KeyFmt`. -/
theorem loop_tr (env : AccEnv) (gcap pb : Nat) (hcap1 : 134217728 ≤ gcap)
    (hcap : gcap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hU : Utf8Call p env pb S0 S1)
    (hL : LogFmt p env pb S0 S1) (hK : KeyFmt p env pb S0 S1) {sp q nc e : Nat} {μ₀ : Memory}
    (x : DeferredTransfer) (rest : List AccumulateInput) (s : St Stream)
    (Q : ForInStep PUnit → St Stream → Prop)
    (hQ : ∀ s', ItemsInv env pb S0 S1 sp q nc e μ₀ rest s' → Q (.yield ⟨⟩) s')
    (hI : ItemsInv env pb S0 S1 sp q nc e μ₀ (.transfer x :: rest) s) :
    Impl p (accContractS env) env Ab
      (Spec.Prog.bind (Spec.onTransfer x.source x.amount x.memo.toList)
        fun _ => pure (ForInStep.yield PUnit.unit)) Q s := by
  obtain ⟨st, H, hbuf, hslots, hown⟩ := hI.heap
  have hS1 := H.hS1
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hl := hI.cur
  simp only [List.length_cons] at hl
  generalize hc : curAt sp s = cur at hl hbuf hslots hown
  have hnc : nc ≠ 0 := by have := hI.hcap; simp only [List.length_cons] at this; omega
  obtain ⟨d, hd, hdu, hdq, hdata⟩ := hbuf hnc
  have hin : ∀ a, cur ≤ a → a < cur + 184 → InDataA d a := fun a h1 h2 => hdata a h1 (by omega)
  have hlo := heapC_data_lt H hd (hin cur (Nat.le_refl _) (by omega))
  have hhi := heapC_data_lt H hd (hin (cur + 183) (by omega) (by omega))
  have hrq : ∀ a, cur ≤ a → a < cur + 184 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heapC_writable_data H hd hdu (hin a h1 h2))
  have hwf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.writable a = true := fun a h1 h2 =>
    H.st a (by omega) (by omega)
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf a h1 h2)
  have hslot := hslots 0 (.transfer x) rfl
  simp only [itemOf, RepTr, Nat.mul_zero, Nat.add_zero] at hslot
  obtain ⟨w0, wm, wa, -, ws, -⟩ := hslot
  have hsz := hI.sized (.transfer x) (by simp)
  simp only [InputSized] at hsz
  have e0 : rdN s.μ cur 8 = 18446744073709551615 := by
    have := readN_drop_take s.μ cur 184 0 8 (by omega)
    rw [List.drop_zero, Nat.add_zero] at this
    rw [← w0]; unfold rdN; rw [this]
  have e136 : rdN s.μ (cur + 136) 8 = x.amount := by
    rw [← wa]; unfold rdN; rw [readN_drop_take s.μ cur 184 136 8 (by omega)]
  have e152 : rdN s.μ (cur + 152) 4 = x.source := by
    rw [← ws]; unfold rdN; rw [readN_drop_take s.μ cur 184 152 4 (by omega)]
  have e8 : s.μ.readN (cur + 8) 128 = x.memo.toList := by
    rw [← wm, readN_drop_take s.μ cur 184 8 128 (by omega)]
  -- 6766 → 6782 → 7159
  obtain ⟨ω1, N1, r1, g1', e5⟩ := hI.to6782 (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q)
    (by omega) hrf
  rw [hc] at e5
  obtain ⟨ω2, μ2, r2, g1, -, -, g8, g6, g10, n168, n200, fr2, rd2, wr2, -⟩ :=
    il_disp_tr (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω1 s.μ sp cur g1' e5
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ e0 hwf hrq
  have lo2 : ∀ a, a < sp + 168 → μ2.read a = s.μ.read a := fun a ha =>
    fr2 a (by omega) (Or.inl ha) (Or.inl (by omega))
  have H2 : HeapCtxC env.code pb S0 S1 μ2 st :=
    HeapCtxC.keep_hi H (fun a ha => lo2 a (by omega)) wr2
  have st2 : ∀ k, (k + 8 ≤ 168 ∨ 176 ≤ k) → (k + 8 ≤ 200 ∨ 208 ≤ k) → k + 8 ≤ 1856 →
      rdN μ2 (sp + k) 8 = rdN s.μ (sp + k) 8 := fun k h1 h2 h3 =>
    rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega)
  have ro2 : TrRO μ2 := hI.ro.keep (fun a ha => ⟨lo2 a (by omega), rd2 a⟩)
  refine Impl.pre _ Q (s' := ⟨7159, ω2, μ2, s.c, s.q⟩) ⟨_, r1.trans r2⟩ rfl ?_
  refine Impl.bind _ Q _ _ ?_
  refine tr_impl env gcap pb hcap1 hcap (P := P) hAb hU hL hK s.c s.q ω2 μ2 st sp (cur + 8) x.source
    x.amount x.memo.toList H2 g1 g8 ?_ ?_ ?_ ⟨by omega, hsp.2⟩ hstk ⟨by omega, by omega⟩
    (fun a h1 h2 => by rw [rd2]; exact hrq a (by omega) (by omega)) ?_ ?_ ?_ ?_ ?_
    (by rw [st2 208 (by omega) (by omega) (by omega)]; exact hI.m208)
    (by rw [st2 136 (by omega) (by omega) (by omega)]; exact hI.m136) n200 hI.fit.storage _ ?_
  · rw [g10, UInt64.toNat_ofNat', sxw4_cut _ (by rw [e152]; exact hsz.1), e152]
  · rw [g6, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (rdN_lt64 _ _), e136]
  · rw [Memory.readN_congr fun j hj => lo2 _ (by omega)]; exact e8
  · exact ro2.1
  · exact ro2.2.1
  · exact ro2.2.2.1
  · exact ro2.2.2.2.1
  · exact ro2.2.2.2.2
  · intro s' hT
    obtain ⟨hi, hcx, -, h1', ⟨st', H', keep'⟩, fr', lo', gl'⟩ := hT
    refine Impl.pure_of (hQ s' ?_)
    have kk : ∀ k, ((16 ≤ k ∧ k < 24) ∨ (32 ≤ k ∧ k < 40) ∨ (136 ≤ k ∧ k < 152) ∨
        (168 ≤ k ∧ k < 176) ∨ (184 ≤ k ∧ k < 192) ∨ (200 ≤ k ∧ k < 224) ∨
        (1848 ≤ k ∧ k < 1856)) → (∀ j, j < 8 → k + j < 1856 ∧
          ((16 ≤ k + j ∧ k + j < 24) ∨ (32 ≤ k + j ∧ k + j < 40) ∨ (136 ≤ k + j ∧ k + j < 152) ∨
          (168 ≤ k + j ∧ k + j < 176) ∨ (184 ≤ k + j ∧ k + j < 192) ∨ (200 ≤ k + j ∧ k + j < 224) ∨
          (1848 ≤ k + j ∧ k + j < 1856))) →
        rdN s'.μ (sp + k) 8 = rdN μ2 (sp + k) 8 := fun k _ hj =>
      rdN_frame fun j hj' => fr' _ (by have := hj j hj'; omega) (by omega)
        (not_trW_loop (by have := (hj j hj').2; omega))
    have hcur' : curAt sp s' = cur + 184 := by
      rw [curAt_6766 hi, kk 168 (by omega) (fun j hj => ⟨by omega, by omega⟩), n168]
    have kw : ∀ k, (k = 16 ∨ k = 32 ∨ k = 136 ∨ k = 144 ∨ k = 184 ∨ k = 208 ∨ k = 216 ∨
        k = 1848) → rdN s'.μ (sp + k) 8 = rdN s.μ (sp + k) 8 := fun k hk => by
      rw [kk k (by omega) (fun j hj => ⟨by omega, by omega⟩), st2 k (by omega) (by omega) (by omega)]
    have dat : ∀ d0 ∈ chunks st, d0.used = true → ∀ a, InDataA d0 a → s'.μ.read a = s.μ.read a :=
      fun d0 h0 hu a ha => by
        rw [(keep' d0 h0 hu).2 a ha, lo2 a (by have := heapC_data_lt H h0 ha; omega)]
    refine ⟨.inl hi, h1', hsp, hstk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ro2.keep lo',
      (hI.ro2.keep fun a ha => ⟨lo2 a (by omega), rd2 a⟩).keep lo', ?_, ?_, ?_⟩
    · rw [hcur']; omega
    · rw [kw 144 (by omega)]; exact hI.m144
    · rw [kw 16 (by omega)]; exact hI.m16
    · rw [kw 32 (by omega)]; exact hI.m32
    · rw [kw 208 (by omega)]; exact hI.m208
    · rw [kw 136 (by omega)]; exact hI.m136
    · rw [kw 184 (by omega)]; exact hI.m184
    · rw [kw 216 (by omega)]; exact hI.m216
    · rw [kw 1848 (by omega)]; exact hI.m1848
    · have := hI.hcap; simp only [List.length_cons] at this; omega
    · obtain ⟨sl', own'⟩ := rest_keep (st' := st') (μ' := s'.μ) (db := d) hslots hown
        (fun a h1 h2 => hdata a h1 (by omega)) (fun a ha => dat d hd hdu a ha)
        (fun d0 h0 hu _ => ⟨(keep' d0 h0 hu).1, dat d0 h0 hu⟩)
      refine ⟨st', H', fun _ => ⟨d, (keep' d hd hdu).1, hdu, hdq, fun a h1 h2 => ?_⟩, ?_, ?_⟩
      · rw [hcur'] at h1; exact hdata a (by omega) h2
      · rw [hcur']; exact sl'
      · rw [hcur']; exact own'
    · intro a ha
      rw [gl' a ha, lo2 a (by unfold Glob at ha; omega)]; exact hI.glob a ha
    · rw [hcx]; exact valuesFit_trCtx hI.fit _ _ _ (by rw [ByteArray.length_toList']; exact hsz.2.2.2.2)
    · intro i hi; exact hI.sized i (by simp [hi])

end Services.Bootstrap.Acc
