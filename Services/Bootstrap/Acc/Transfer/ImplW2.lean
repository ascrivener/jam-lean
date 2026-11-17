import Services.Bootstrap.Acc.Transfer.W2c
import Services.Bootstrap.Acc.Transfer.OrPanic
import Services.Bootstrap.Acc.Impl.ROKeepS

/-!
# `on_transfer`, the record's write as `Impl` (7399 → 6766)

Spec `onTransfer`'s third line (GP v0.8.0 §B.7, Ω_W):
`orPanic (.write s!"transfer{n}" (fixed 4 source ++ fixed 8 amount ++ memo))`.

`tr_w2` composes `tr_w2a` (the memo's copy, `from_utf8`), `lg_part1` and `lg_part2` (the log line,
frame-only), `tr_w2c` (the key, the record's encoding, the call of `set`): all keeping the context. Then
`set_call` does Ω_W (under `YIn`). FULL goes to 15361 (☇, as `orPanic` of the spec's `error`). Otherwise
`t2_chk_ok` and `dealloc_callG` free the value, and `t2_kfree` / `t2_knofree` free the key, back to the
items loop's head 6766 (`W2Post`). The early ☇ are the heap traps 15362 / 15363 / 34178 and the
formatting calls' `ExhaustsP`, all `HeapFailT`.

Named hypotheses: `Utf8Call`, `LogFmt`, `KeyFmt`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Spec
open JAM.Codec (fixed)
open Services.Bootstrap.ASem (argBase outBase writeAcct)
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A run under a contract keeping what is not writable keeps the read-only data below 196608. -/
theorem ro_keep {X : Type} {R : HostRel X} {p : ByteArray} {pb : Nat} (hR : KeepsRO R 48 pb)
    {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X} (run : FreeStepsH p R i ω μ x i' ω' μ' x' n)
    (hro : ∀ a, a < 196608 → μ.writable a = false) :
    ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a ∧ μ'.writable a = false := by
  intro a ha
  have k := FreeStepsH.keepRO_of hR run
  have hp := k.1 (a / pageSize) (.inl (by unfold pageSize; omega))
  refine ⟨k.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (hro a ha), ?_, ?_⟩
  · unfold Memory.readable; rw [hp]
  · have := hro a ha
    unfold Memory.writable at this ⊢; rw [hp]; exact this

/-- The scratch words `on_transfer`'s second part writes from sp up. -/
def TrW2 (sp a : Nat) : Prop := LgW sp a ∨ T2W sp a ∨ (sp + 264 ≤ a ∧ a < sp + 280)

/-- **The state at the items loop's head 6766 after the record's write**, from s at 7399 with memory μ
    and allocator state s₀: context c and stream f; sp in ω₁; the allocator's context for some state keeping every allocated
    chunk of s₀ and its data; from sp up only `TrW2` changed; below 196608 the memory reads and is
    readable as before. -/
def W2Post (env : AccEnv) (pb S0 S1 sp : Nat) (s₀ : State) (μ : Memory) (c : AccCtx) (f : Stream)
    (s' : St Stream) : Prop :=
  s'.i = 6766 ∧ s'.c = c ∧ s'.q = f ∧ s'.ω[1] = UInt64.ofNat sp ∧
  (∃ st, HeapCtxC env.code pb S0 S1 s'.μ st ∧
    ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks st ∧ ∀ a, InDataA d a → s'.μ.read a = μ.read a) ∧
  (∀ a, a < 4294967296 → sp ≤ a → ¬ TrW2 sp a → s'.μ.read a = μ.read a) ∧
  (∀ a, a < 196608 → s'.μ.read a = μ.read a ∧ s'.μ.readable a = μ.readable a)

/-- **`on_transfer`'s record write implements
    `orPanic (.write s!"transfer{n}" (fixed 4 src ++ fixed 8 am ++ memo))`** from 7399, with n the u32 at
    sp + 1496, src at sp + 472, am at sp + 1000 and the memo's 128 octets at sp + 1144 (as `tr_w1` and
    `tr_read` leave them), the formatter words of the accumulate prologue at sp + 208 / 136 / 200, and the
    error table (read-only data). Early ☇ for any `Ab` holding at `HeapFailT` states. Named hypotheses:
    `Utf8Call`, `LogFmt`, `KeyFmt`. -/
theorem tr_w2 (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hU : Utf8Call p env pb S0 S1) (hL : LogFmt p env pb S0 S1)
    (hK : KeyFmt p env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp n src am : Nat) (memo : List UInt8)
    (H : HeapCtxC env.code pb S0 S1 μ s₀) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1)
    (m208 : rdN μ (sp + 208) 8 = 2800) (m136 : rdN μ (sp + 136) 8 = 2804) (m200 : rdN μ (sp + 200) 8 = 678)
    (m1496 : rdN μ (sp + 1496) 4 = n) (hn : n < 4294967296)
    (m472 : rdN μ (sp + 472) 4 = src) (m1000 : rdN μ (sp + 1000) 8 = am)
    (mmemo : μ.readN (sp + 1144) 128 = memo)
    (ht8 : rdN μ 69072 4 = 4294900408) (ht4 : rdN μ 69056 4 = 4294900402)
    (htr : ∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)
    (hold : ∀ v, c.1.self.storage.get? (trKey2 n) = some v → v.length < 2 ^ 63)
    (Q : Unit → St Stream → Prop) (hQ : ∀ s', W2Post env pb S0 S1 sp s₀ μ
      (c.1.setSelf (writeAcct c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo)), c.2) f s' → Q () s') :
    Impl p (accContractS env) env Ab
      (orPanic (.write (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo))) Q ⟨7399, ω, μ, c, f⟩ := by
  have hS1 := H.hS1
  have hmemo : memo.length = 128 := by rw [← mmemo, Memory.length_readN]
  -- 7399 → 7454
  rcases tr_w2a env cap pb hcap1 hcap (p := p) (P := P) hAb hU c f ω μ s₀ sp H h1 hsp hSTk with
    ⟨sA, ωA, μA, NA, ptr, runA, A1, -, A6, hp1, hp2, HA, hch, hfrA, keepA, tagA, frA, -⟩ | hab
  rotate_left
  · exact Impl.abort _ Q hab
  -- 7454 → 7631
  rcases lg_part1 env cap pb hcap1 hcap (p := p) (P := P) hAb c f ωA μA sA sp ptr HA A1 A6 hsp hSTk ⟨hp1, hp2⟩
      hch tagA with
    ⟨sB, ωB, μB, NB, chq, cp, q, len, runB, B1, HB, hq, hqu, hqa, mB512, hcp, mB520, mB528, hql, keepB, frB⟩ | hab
  rotate_left
  · exact Impl.abort _ Q (Aborts.prepend ⟨NA, runA⟩ hab)
  -- frames from 7399 to 7631
  have frAB : ∀ a, a < 4294967296 → sp ≤ a → ¬ LgW sp a → μB.read a = μ.read a := fun a h0 ha hW => by
    unfold LgW at hW
    rw [frB a h0 ha (by unfold LgW; omega), frA a h0 ha (by omega)]
  have kB : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → (∀ j, j < n → ¬ LgW sp (o + j)) → rdN μB o n = rdN μ o n :=
    fun o n h1 h2 h3 => rdN_frame fun j hj => frAB _ (by omega) (by omega) (h3 j hj)
  -- 7631 → 7763
  rcases lg_part2 env (p := p) (P := P) hAb hL c f ωB μB sB sp chq cp q len HB B1 hsp hSTk hq hqu hqa mB512 hcp
      mB520 mB528 hql (by rw [kB _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m208)
      (by rw [kB _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m136)
      (by rw [kB _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m200) with
    ⟨sC, ωC, μC, NC, runC, C1, HC, keepC, frC⟩ | hab
  rotate_left
  · exact Impl.abort _ Q (Aborts.prepend ⟨NA + NB, runA.trans runB⟩ hab)
  have frAC : ∀ a, a < 4294967296 → sp ≤ a → ¬ LgW sp a → μC.read a = μ.read a := fun a h0 ha hW => by
    unfold LgW at hW
    rw [frC a h0 ha (by omega) (by omega)]; exact frAB a h0 ha (by unfold LgW; omega)
  have kC : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → (∀ j, j < n → ¬ LgW sp (o + j)) → rdN μC o n = rdN μ o n :=
    fun o n h1 h2 h3 => rdN_frame fun j hj => frAC _ (by omega) (by omega) (h3 j hj)
  -- 7763 → 48104
  rcases tr_w2c env cap pb hcap1 hcap (p := p) (P := P) hAb hK c f ωC μC sC sp n src am memo HC C1 hsp hSTk
      (by rw [kC _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m208)
      (by rw [kC _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m1496) hn
      (by rw [kC _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m472)
      (by rw [kC _ _ (by omega) (by omega) (fun j hj => by unfold LgW; omega)]; exact m1000)
      (by rw [Memory.readN_congr fun j hj => frAC _ (by omega) (by omega) (by unfold LgW; omega)]; exact mmemo) with
    ⟨sD, ωD, μD, ND, kc, kp, vp, kch, vch, runD, D0, D1, D7, D8, D9, D10, D11, D6, D5, HD, mkc, hkch, hkcu, hkca,
      hkin, mkey, m744, m752, hvch, hvcu, hvca, hvk, hvin, vdat, keepD, frD⟩ | hab
  rotate_left
  · exact Impl.abort _ Q (Aborts.prepend ⟨NA + NB + NC, (runA.trans runB).trans runC⟩ hab)
  have runK := ((runA.trans runB).trans runC).trans runD
  have hstD := HD.st
  have roD := ro_keep (keepCtx_keepsRO env H.bd) runK H.ro
  obtain ⟨Nk1, Nk2, Nk3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HD.wf hkch hkcu
  obtain ⟨Nv1, Nv2, Nv3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HD.wf hvch hvcu
  have hbD := HD.hb0
  have hbTD := HD.hbT
  -- the key's octets lie in kch's data, the value's in vch's
  have hkl : kp + (trKey2 n).length ≤ 2147483648 := by
    by_cases h0 : (trKey2 n).length = 0
    · have ht := HD.wf.2.2.2.1
      unfold TilesOk at ht
      have := (ht.mem_lt kch hkch).2.2
      omega
    · have := heapC_data_lt HD hkch (hkin (kp + (trKey2 n).length - 1) (by omega) (by omega))
      omega
  have hkl1 : kp ≤ kp + (trKey2 n).length := Nat.le_add_right _ _
  have hkb : 65536 ≤ kp := by omega
  have hvb : 65536 ≤ vp ∧ vp + 140 ≤ 2147483648 := by
    have := hvin (vp + 139) (by omega) (by omega)
    unfold InDataA at this; omega
  -- the operation's step
  have hvl : (fixed 4 src ++ fixed 8 am ++ memo).length = 140 := by
    simp only [List.length_append, fixed, Num.length_encodeLE, hmemo]
  have hk : argBase + (trKey2 n).length + (fixed 4 src ++ fixed 8 am ++ memo).length ≤ outBase := by
    rw [hvl]; unfold argBase outBase; omega
  have estep := ASem.step_write env (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) c hk hold
  have h1R : Reaches p (KeepCtx (accContractS env)) ⟨7399, ω, μ, c, f⟩ ⟨48104, ωD, μD, c, f⟩ := ⟨_, runK⟩
  have ht8D : rdN μD 69072 4 = 4294900408 := by
    rw [← ht8, rdN_frame fun j hj => (roD _ (by omega)).1]
  have ht4D : rdN μD 69056 4 = 4294900402 := by
    rw [← ht4, rdN_frame fun j hj => (roD _ (by omega)).1]
  have hval : μD.readN vp 140 = fixed 4 src ++ fixed 8 am ++ memo := vdat
  -- `set`, 48104 → 7915
  obtain ⟨e, ω8, μ8, he, run8, i0, i1, i5, i6, sout, fr8, rd8, wr8⟩ :=
    set_call (p := p) (P := P) env c f ωD μD sp (sp + 264) kp (trKey2 n).length vp 140 (trKey2 n)
      (fixed 4 src ++ fixed 8 am ++ memo) D1 D7 D8 D9 D10 D11 (by omega) (by decide) (by omega) (by omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => hstD a (by omega) (by omega))
      (fun a h1 h2 => hstD a (by omega) (by omega)) (.inr (by omega))
      (Services.Witness.rangeReadable_of (fun a h1 h2 => Memory.readable_of_writable
        (heapC_writable_data HD hkch hkcu (hkin a h1 h2))) (by omega)) mkey
      (Services.Witness.rangeReadable_of (fun a h1 h2 => Memory.readable_of_writable
        (heapC_writable_data HD hvch hvcu (hvin a h1 h2))) (by omega)) hval hvl (.inl (by omega)) (.inl (by omega))
      ht8D ht4D (fun a h1 h2 => by rw [(roD a (by omega)).2.1]; exact htr a h1 h2) (by omega) hold
  have run8' := run8.trans (t2_j (p := p) (P := P) _ ω8 μ8 e he (i0.trans D0))
  have H8 : HeapCtxC env.code pb S0 S1 μ8 sD :=
    HeapCtxC.keep_hi HD (fun a ha => fr8 a (by omega) (.inl (by omega)) (.inl (by omega))) wr8
  have hst8 := H8.st
  have hrf8 : ∀ a, sp ≤ a → a < sp + 1856 → μ8.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst8 a (by omega) (by omega))
  have k8 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → (o + n ≤ sp + 264 ∨ sp + 280 ≤ o) → rdN μ8 o n = rdN μD o n :=
    fun o n h1 h2 h3 => rdN_frame fun j hj => fr8 _ (by omega) (.inr (by omega)) (by omega)
  by_cases hF : (writeAcct c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo)).minBalance >
      (writeAcct c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo)).balance
  · -- FULL: the trap at 15361
    rw [if_pos hF] at estep
    refine impl_orPanic _ Q ⟨7399, ω, μ, c, f⟩ ⟨48104, ωD, μD, c, f⟩ h1R rfl estep (.inr ?_)
    have hR7 : writeR7 c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) = Result.FULL := by
      unfold writeR7; rw [if_pos hF]
    have hS : writeSelf c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) = c.1.self := by
      unfold writeSelf; rw [if_pos hF]
    rw [hS] at run8'
    rw [hR7] at sout
    unfold SetOut at sout
    rw [if_pos rfl] at sout
    refine ⟨⟨7915, ω8, μ8, (c.1.setSelf c.1.self, c.2), f⟩, ⟨_, run8'⟩, rfl, ?_⟩
    obtain ⟨ω9, run9⟩ := t2_chk_full (p := p) (P := P) (R := KeepCtx (accContractS env))
      ((c.1.setSelf c.1.self, c.2), f) ω8 μ8 sp i1 ⟨by omega, by omega⟩ hrf8
      (by unfold rdN; rw [sout.1, Num.decodeLE_encodeLE])
    exact ends_of_15361 (P := P) ⟨7915, ω8, μ8, (c.1.setSelf c.1.self, c.2), f⟩ run9
  · -- the write succeeded: free the value and the key, back to 6766
    rw [if_neg hF] at estep
    refine impl_orPanic _ Q ⟨7399, ω, μ, c, f⟩ ⟨48104, ωD, μD, c, f⟩ h1R rfl estep (.inr ?_)
    have hR7 : writeR7 c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) ≠ Result.FULL := by
      unfold writeR7; rw [if_neg hF]
      cases hv : c.1.self.storage.get? (trKey2 n) with
      | none => simp only [Option.map_none, Option.getD_none]; unfold Result.NONE Result.FULL; omega
      | some w =>
        have := hold w hv
        simp only [Option.map_some, Option.getD_some]; unfold Result.FULL; omega
    have hS : writeSelf c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) =
        writeAcct c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo) := by
      unfold writeSelf; rw [if_neg hF]
    rw [hS] at run8'
    obtain ⟨c₁, hc1⟩ : ∃ c₁ : AccCtx,
        (c.1.setSelf (writeAcct c.1.self (trKey2 n) (fixed 4 src ++ fixed 8 am ++ memo)), c.2) = c₁ := ⟨_, rfl⟩
    rw [hc1] at run8'
    -- the reply word is not −1
    have hw : rdN μ8 (sp + 264) 8 ≠ 18446744073709551615 := by
      unfold SetOut at sout
      rw [if_neg hR7] at sout
      split at sout
      · unfold rdN; rw [sout, Num.decodeLE_encodeLE]; decide
      · unfold rdN; rw [sout.1, Num.decodeLE_encodeLE]; decide
    have roY := ro_keep (yIn_keepsRO env H.bd c.2 c.2) run8 HD.ro
    refine ⟨⟨7915, ω8, μ8, c₁, f⟩, ⟨_, run8'⟩, hc1.symm, .inr ?_⟩
    obtain ⟨ω9, run9, b0, b1, b7, b8, b5⟩ := t2_chk_ok (p := p) (P := P) (R := KeepCtx (accContractS env))
      (c₁, f) ω8 μ8 sp _ 140 vp i1 (i6.trans D6) ⟨by omega, by omega⟩ hrf8 rfl hw
      (by rw [k8 _ _ (by omega) (by omega) (.inr (by omega))]; exact m744) (by decide) (by omega)
    obtain ⟨ω10, μ10, run10, H10, -, -, -, stk10, -, oth10, -, e1, e5, -⟩ :=
      dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c₁, f) ω9 μ8 sD sp vp
        276 7946 vch H8 hvch hvcu hvca b0 b1 b7 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_137]) bs_7946 (by omega) ⟨by omega, by omega⟩
    have hst10 := H10.st
    have hrf10 : ∀ a, sp ≤ a → a < sp + 1856 → μ10.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (hst10 a (by omega) (by omega))
    have mkc10 : rdN μ10 (sp + 512) 8 = kc := by
      rw [rdN_frame fun j hj => stk10 _ (by omega) (by omega), k8 _ _ (by omega) (by omega) (.inr (by omega)), mkc]
    have e5' : ω10[5] = UInt64.ofNat kp := e5.trans (b5.trans (i5.trans D5))
    have e1' : ω10[1] = UInt64.ofNat sp := e1.trans b1
    have roK2 := ro_keep (keepCtx_keepsRO env H.bd) run10 H8.ro
    have hkch10 : kch ∈ chunks (free sD vp) := (oth10 kch hkch hkcu (Ne.symm hvk)).1
    -- the post-state, from a final memory μ' with the frame facts
    have post : ∀ (ω' : Regs) (μ' : Memory) (st : State), ω'[1] = UInt64.ofNat sp →
        HeapCtxC env.code pb S0 S1 μ' st →
        (∀ d ∈ chunks (free sD vp), d.used = true → d ≠ kch → d ∈ chunks st ∧
          ∀ a, InDataA d a → μ'.read a = μ10.read a) →
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ10.read a) →
        (∀ a, a < 196608 → μ'.read a = μ10.read a ∧ μ'.readable a = μ10.readable a) →
        Q () ⟨6766, ω', μ', c₁, f⟩ := by
      intro ω' μ' st e1'' H' kp' fr' ro'
      refine hQ _ ⟨rfl, hc1.symm, rfl, e1'', ⟨st, H', fun d hd hu => ?_⟩, fun a h0 ha hW => ?_, fun a ha => ?_⟩
      · obtain ⟨hdA, hdatA⟩ := keepA d hd hu
        have hneA := hfrA d hd hu
        obtain ⟨-, hdB, hdatB⟩ := keepB d hdA hu hneA
        obtain ⟨hneq, -⟩ := keepB d hdA hu hneA
        obtain ⟨hdC, hdatC⟩ := keepC d hdB hu hneq
        obtain ⟨hnek, hnev, hdD, hdatD⟩ := keepD d hdC hu
        obtain ⟨hd10, hdat10⟩ := oth10 d hdD hu hnev
        obtain ⟨hdE, hdatE⟩ := kp' d hd10 hu hnek
        refine ⟨hdE, fun a ha => ?_⟩
        have hlt := heapC_data_lt H hd ha
        rw [hdatE a ha, hdat10 a ha, fr8 a (by omega) (.inl (by omega)) (.inl (by omega)), hdatD a ha, hdatC a ha,
          hdatB a ha, hdatA a ha]
      · unfold TrW2 at hW
        have hW1 : ¬ LgW sp a := fun h => hW (.inl h)
        have hW2 : ¬ T2W sp a := fun h => hW (.inr (.inl h))
        unfold T2W at hW2
        rw [fr' a h0 ha, stk10 a h0 ha, fr8 a h0 (.inr ha) (by omega), frD a h0 ha (by unfold T2W; omega),
          frAC a h0 ha hW1]
      · obtain ⟨r', rd'⟩ := ro' a ha
        obtain ⟨r10, rd10, -⟩ := roK2 a ha
        obtain ⟨rY, rdY, -⟩ := roY a ha
        obtain ⟨rD, rdD, -⟩ := roD a ha
        exact ⟨by rw [r', r10, rY, rD], by rw [rd', rd10, rdY, rdD]⟩
    by_cases hk0 : kc = 0
    · obtain ⟨ω11, run11, j11⟩ := t2_knofree (p := p) (P := P) (R := KeepCtx (accContractS env)) (c₁, f) ω10 μ10 sp
        e1' ⟨by omega, by omega⟩ hrf10 (by rw [mkc10, hk0])
      refine ⟨⟨6766, ω11, μ10, c₁, f⟩, ⟨_, (run9.trans run10).trans run11⟩, rfl, ?_⟩
      exact post ω11 μ10 (free sD vp) ((j11 1 (by decide)).trans e1') H10
        (fun d hd hu _ => ⟨hd, fun a _ => rfl⟩) (fun a _ _ => rfl) (fun a _ => ⟨rfl, rfl⟩)
    · obtain ⟨ω11, run11, c0, c1, c7, c8⟩ := t2_kfree (p := p) (P := P) (R := KeepCtx (accContractS env)) (c₁, f)
        ω10 μ10 sp kc kp e1' e5' ⟨by omega, by omega⟩ hrf10 mkc10 hk0 (by omega)
      obtain ⟨ω12, μ12, run12, H12, -, -, -, stk12, -, oth12, -, g1, -, -⟩ :=
        dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c₁, f) ω11 μ10
          (free sD vp) sp kp 228 6766 kch H10 hkch10 hkcu hkca c0 c1 c7 ⟨by decide, by decide, by decide⟩
          (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_113]) bs_6766 (by omega) ⟨by omega, by omega⟩
      have roK3 := ro_keep (keepCtx_keepsRO env H.bd) run12 H10.ro
      refine ⟨⟨6766, ω12, μ12, c₁, f⟩, ⟨_, (run9.trans run10).trans (run11.trans run12)⟩, rfl, ?_⟩
      exact post ω12 μ12 _ (g1.trans c1) H12 (fun d hd hu hne => oth12 d hd hu hne)
        (fun a h0 ha => stk12 a h0 ha) (fun a ha => ⟨(roK3 a ha).1, (roK3 a ha).2.1⟩)

end Services.Bootstrap.Acc
