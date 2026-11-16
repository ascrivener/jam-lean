import Services.Bootstrap.Acc.Handlers.ResStoreLoop
import Services.Bootstrap.Acc.Handlers.ResStoreImpl

/-!
# The results store (36170) for any n ≥ 1, against `ExtendH` and `OkEncH`

The value written by `on_work_item`'s results store is ℰ(↕rs) (`encodeResults`, GP v0.8.0 Appendix B,
Ω_W). In the callee frame S = sp − 96:
- `res_enter` (36170 → 36346): `rs_pre`, `alloc(144n + 4, 1)` (null: the trap at 36528), `rs_vec`,
  ℰ(n) by `prefix_any`, `rl_enter`; it ends in `LoopInv 0` against the memory there;
- `rl_loop` (36346 → 36405, in `ResStoreLoop`);
- `res_exit` (36405 → 48104): `rl_tail`, the key encoder (`kb_call`, tag 2; its `alloc` may fail: the trap
  at 34070), `rs_set`.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow
  Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.KeyEnc
  Services.Bootstrap.Acc.Handlers.RecentSlotWrite

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- ℰ(x) has at most 9 octets. -/
theorem encodeNat_len_le9 (x : Nat) : (Blob.encodeNat x).length ≤ 9 := by
  unfold Blob.encodeNat
  split
  · simp
  · split
    · rename_i l hl
      have := List.mem_of_find?_eq_some hl
      simp at this ⊢
      omega
    · simp

/-- **From 36170 to the loop (36346), n ≥ 1**, under accumulate's contract with the context and the
    stream kept: either the value buffer's `alloc` fails (the trap at 36528), or the run reaches 36346 in
    `LoopInv 0` against the memory μ₀ there, with the key value kp at S + 16 and n at S + 24
    (S = sp − 96), ω₀, ω₅, ω₆ saved at S + 88, S + 80, S + 72, every allocated chunk of st kept with its
    data, memory from sp up, the globals and read-only data (with its access) kept. -/
theorem res_enter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (c : AccCtx) (f : Stream)
    (ω : Regs) (μ : Memory) (st : State) (sp rp n kp pb S0 S1 : Nat) (rs : List Spec.Result)
    (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rp) (h8 : ω[8] = UInt64.ofNat n)
    (h9 : ω[9] = UInt64.ofNat kp) (hkp : kp < 2 ^ 64) (hn0 : n ≠ 0)
    (L : LoopHyp pb S0 S1 sp rp n rs st μ) :
    (∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36170 ω μ (c, f) 36528 ω' μ' (c, f) N) ∨
    ∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 36170 ω μ (c, f) 36346 ω' μ' (c, f) N ∧
      LoopInv env.code pb S0 S1 sp rp n rs st μ' 0 ω' μ' s' ∧
      μ'.readN (sp - 96 + 16) 8 = Num.encodeLE 8 kp ∧ μ'.readN (sp - 96 + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN (sp - 96 + 88) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp - 96 + 80) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 96 + 72) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.readable a = μ.readable a) := by
  obtain ⟨hsp, hS1, hn, ⟨hrp1, hrp2⟩, hB, hR⟩ := L
  have hSt := H.st
  have hS1' := H.hS1
  have hSb := H.hSb
  have hb0 := H.hb0
  have hbT := H.hbT
  have hE9 := encodeNat_len_le9 n
  have hn32 : 144 * n + 4 < 4294967296 := by omega
  -- A: 36170 → 40494
  obtain ⟨ωA, μA, runA, a0, a1, a5, a6, a7, a8, mA0, mA5, mA6, mAk, mAn, -, frA, rdA, wrA⟩ :=
    rs_pre (R := (accHeapHost env).rel cap) (P := P) (c) ω μ sp rp n kp h1 h7 h8 h9 ⟨by omega, by omega⟩
      (by omega) hn32 hkp (fun a h1 h2 => hSt a (by omega) (by omega))
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega))) wrA
  -- B: `alloc(144n + 4, 1)`
  rcases alloc_callG (p := p) (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ωA μA st (sp - 96)
      (144 * n + 4) 1 pb S0 S1 HA a1 a7 a8 (by decide) (by decide) (by omega) (by omega)
      ⟨by omega, by omega⟩ with
    ⟨vp, s1, ω1, μ1, -, run1, H1, keep1, hnew1, hfresh1, hkg1, e7, stk1, f0, f1, f5, f6⟩ |
    ⟨-, ω1, μ1, run1, e7, -, f0, -, -, -⟩
  case inr =>
    obtain ⟨-, runS⟩ := FreeStepsH.growS f (((runA.trans run1).trans (rs_j1 (P := P) c ω1 μ1 (f0.trans a0))).trans
      (rs_null (P := P) c ω1 μ1 e7))
    exact .inl ⟨ω1, μ1, _, runS⟩
  have hb01 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew1 rfl
  dsimp only at n1 n2 n3
  have hvp0 : vp ≠ 0 := by omega
  have run1' := run1.trans (rs_j1 (P := P) c ω1 μ1 (f0.trans a0))
  -- C: 36217 → 30977
  have k1A : ∀ a, a < 4294967296 → sp - 96 ≤ a → μ1.read a = μA.read a := fun a h0 ha => stk1 a h0 ha
  obtain ⟨ω2, μ2, run2, c0, c1, c5, c6, c7, c8, mV32, mV40, mV48, mV56, fr2, rd2, wr2⟩ :=
    rs_vec (R := (accHeapHost env).rel cap) (P := P) c ω1 μ1 (sp - 96) n vp (f1.trans a1) (by rw [f5, a5]) e7
      hvp0 (by omega) (by omega) (by omega)
      (by rw [show sp - 96 + 24 = sp - 72 by omega, ← mAn]
          exact Memory.readN_congr fun j hj => k1A _ (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H1.st a (by omega) (by omega)))
      (fun a h1 h2 => H1.st a (by omega) (by omega))
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s1 :=
    HeapKeep.keepHi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
  -- D: ℰ(n) by `prefix_any`
  have hn0' : rdN μ2 (sp - 96 + 56) 4 = n := by
    show Num.decodeLE _ = _; rw [mV56, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]
  have hdat : ∀ a, vp ≤ a → a < vp + (144 * n + 4) → InData ⟨vp - 32, (144 * n + 4 + 31) / 32 + 1, true⟩ a :=
    fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, dval, dlen, fr3, rd3, wr3⟩ :=
    Services.Bootstrap.Encode.Enc.prefix_any (p := p) (P := P) (R := (accHeapHost env).rel cap) c ω2 μ2 (sp - 96)
      (sp - 96 + 56) (sp - 96 + 32) (144 * n + 4) vp 0 1694 36263 (144 * n) ω2[6].toNat n
      ⟨by omega, by omega, by omega⟩ c0 c1
      (by rw [c5, f5, a5]) UInt64.ofNat_toNat.symm c7 c8 (by omega) (UInt64.toNat_lt _) (by omega) (.inr (by omega))
      hn0' (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega))) mV32 mV40 mV48
      (by omega) (by omega) (by omega) (.inr (by omega)) ⟨by omega, by omega⟩ (.inr (by omega)) (.inr (by omega))
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_846]) bs_36263
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => H2.st a (by omega) (by omega))
      (fun a h1 h2 => HeapKeep.writableData H2 hnew1 rfl (hdat a (by omega) (by omega)))
      (fun a h1 h2 => H2.st a (by omega) (by omega))
  simp only [Nat.zero_add, Nat.add_zero] at dval dlen fr3
  have H3 : HeapCtxC env.code pb S0 S1 μ3 s1 :=
    HeapKeep.keepData H2 hnew1 (fun a h1 h2 => fr3 a (by omega) (.inl (by omega))
      (by dsimp only at h2; omega) (.inl (by omega))) (fun a => by rw [wr3])
  have k3 : ∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 48 ∨ sp - 96 + 56 ≤ a) →
      μ3.read a = μ2.read a := fun a h0 h1 h2 => fr3 a h0 (.inr (by omega)) (.inr (by omega)) h2
  have k31 : ∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 60 ≤ a) →
      μ3.read a = μA.read a := fun a h0 h1 h2 => by
    rw [k3 a h0 h1 (by omega), fr2 a h0 h2, k1A a h0 h1]
  -- E: 36263 → 36346
  obtain ⟨ω4, run4, g1, g5, g6⟩ :=
    rl_enter (R := (accHeapHost env).rel cap) (P := P) c ω3 μ3 (sp - 96) n d1 (by omega) (by omega) hn0
      (by rw [show sp - 96 + 24 = sp - 72 by omega, ← mAn]
          exact Memory.readN_congr fun j hj => k31 _ (by omega) (by omega) (.inl (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
  have run04 := (((runA.trans run1').trans run2).trans run3).trans run4
  obtain ⟨ro1, ro2⟩ := HeapHost.keepRO (env := accHeapHost env) H.bd run04
  obtain ⟨-, runS⟩ := FreeStepsH.growS f run04
  -- the heap, across the run
  have k32 : ∀ a, a < 2147483648 → (a < vp ∨ vp + (Blob.encodeNat n).length ≤ a) → μ3.read a = μ2.read a :=
    fun a ha hv => fr3 a (by omega) (.inl (by omega)) hv (.inl (by omega))
  have k2A : ∀ a, a < 2147483648 → OffHdrG (fun h => ∃ d ∈ chunks s1, d.addr = h) a → μ2.read a = μA.read a :=
    fun a ha ho => by rw [fr2 a (by omega) (.inl (by omega)), hkg1 a ho]
  have kA0 : ∀ a, a < 2147483648 → μA.read a = μ.read a := fun a ha => frA a (by omega) (.inl (by omega))
  have hdata : ∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ3.read a = μ.read a := by
    intro d hd hu a ha
    have hd1 := keep1 d hd hu
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have ap1 := InData.apart H1.wf hd1 hnew1 (Ne.symm (hfresh1 d hd hu)) ha
    unfold InData at ap1; dsimp only at ap1
    have ha' := ha; unfold InData at ha'
    rw [k32 _ (by omega) (by omega), k2A _ (by omega) (data_off H1.wf hb01 hbT1 hd1 ha), kA0 _ (by omega)]
  have k3sp : ∀ a, a < 4294967296 → sp ≤ a → μ3.read a = μ.read a := fun a h0 ha => by
    rw [k31 a h0 (by omega) (.inr (by omega)), frA a h0 (.inr ha)]
  have k3g : ∀ a, Glob a → μ3.read a = μ.read a := fun a ha => by
    have hg := ha
    unfold Glob at hg
    rw [k32 _ (by omega) (by omega), k2A _ (by omega) (glob_off H1.wf hb01 ha), kA0 _ (by omega)]
  have k3ro : ∀ a, a < 196608 → μ3.read a = μ.read a := fun a ha =>
    ro2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  have r3ro : ∀ a, a < 196608 → μ3.readable a = μ.readable a := fun a ha => by
    unfold Memory.readable; rw [ro1 (a / pageSize) (.inl (by unfold pageSize; omega))]
  have mS : ∀ b v, sp - 96 + 60 ≤ b → b + 8 ≤ sp → μA.readN b 8 = Num.encodeLE 8 v →
      μ3.readN b 8 = Num.encodeLE 8 v := fun b v h1 h2 hv => by
    rw [← hv]; exact Memory.readN_congr fun j hj => k31 _ (by omega) (by omega) (.inr (by omega))
  have mS' : ∀ b v, sp - 96 ≤ b → b + 8 ≤ sp - 96 + 32 → μA.readN b 8 = Num.encodeLE 8 v →
      μ3.readN b 8 = Num.encodeLE 8 v := fun b v h1 h2 hv => by
    rw [← hv]; exact Memory.readN_congr fun j hj => k31 _ (by omega) (by omega) (.inl (by omega))
  have hE0 : encK n rs 0 = Blob.encodeNat n := by simp [encK]
  have rd : ∀ b n', sp - 96 ≤ b → b + n' ≤ sp - 96 + 48 → μ3.readN b n' = μ2.readN b n' := fun b n' h1 h2 =>
    Memory.readN_congr fun j hj => k3 _ (by omega) (by omega) (.inl (by omega))
  refine .inr ⟨ω4, μ3, s1, _, runS, ⟨by rw [g1, d1], by rw [g5, d5]; simp, ?_, H3,
    ⟨144 * n + 4, vp, ?_, by rw [hE0]; exact dval, by rw [hE0]; omega, ?_⟩, fun _ _ _ _ => rfl,
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, hdata, k3sp, k3g, k3ro, r3ro⟩
  · rw [g6, d6, UInt64.ofNat_toNat, c6, f6, a6]; simp
  · rw [hE0]
    refine ⟨by omega, by omega, by rw [rd _ _ (by omega) (by omega)]; exact mV32,
      by rw [rd _ _ (by omega) (by omega)]; exact mV40, by rw [show sp - 96 + 32 + 16 = sp - 96 + 32 + 16 from rfl]; exact dlen,
      by omega, by omega, by omega, _, hnew1, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · intro d hd hu
    refine ⟨keep1 d hd hu, fun e => ?_, fun _ _ => rfl⟩
    have ht := H1.wf.2.2.2.1
    unfold TilesOk at ht
    exact hfresh1 d hd hu (Tiles.addr_inj ht d (keep1 d hd hu) _ hnew1 (by simp only; omega))
  · exact mS' _ _ (by omega) (by omega) (by rw [show sp - 96 + 16 = sp - 80 by omega]; exact mAk)
  · exact mS' _ _ (by omega) (by omega) (by rw [show sp - 96 + 24 = sp - 72 by omega]; exact mAn)
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 88 = sp - 8 by omega]; exact mA0)
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 80 = sp - 16 by omega]; exact mA5)
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 72 = sp - 24 by omega]; exact mA6)

/-- **The state at `set`'s call (48104)**, against the memory μ at an earlier point: `set`'s arguments (the
    key `key` (35 octets) in a new chunk at kp′, the value `val` the data of an allocated chunk dv at vp,
    out S + 56, S = sp − 96, return address 1706), the callee frame (vp at S, the value's capacity vc ≠ 0 at
    S + 24, the key's kc at S + 32), every allocated chunk of st kept, neither dv nor the key's, with its
    data; memory kept where `Fr` holds, at the globals and below 196608 (with its access). -/
def SetPre (code : ByteArray) (pb S0 S1 sp kc : Nat) (st : State) (μ : Memory) (Fr : Nat → Prop)
    (key val : List UInt8) (ω' : Regs) (μ' : Memory) : Prop :=
  ∃ (vp kp' vc : Nat) (dv : Chunk) (s' : State), HeapCtxC code pb S0 S1 μ' s' ∧
    (∀ d ∈ chunks st, d.used = true → d ∈ chunks s' ∧ d ≠ dv ∧ d ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ ∧
      ∀ a, InData d a → μ'.read a = μ.read a) ∧
    dv ∈ chunks s' ∧ dv.used = true ∧ dv.addr + 32 = vp ∧
    (⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧ dv ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ ∧
    65536 ≤ vp ∧ vp + val.length ≤ 2147483648 ∧ 65536 ≤ kp' ∧ kp' + 35 ≤ 2147483648 ∧ 0 < vc ∧ vc < 2 ^ 64 ∧
    ω'[0] = UInt64.ofNat 1706 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat kp' ∧
    ω'[6] = UInt64.ofNat vp ∧ ω'[7] = UInt64.ofNat (sp - 96 + 56) ∧ ω'[8] = UInt64.ofNat kp' ∧
    ω'[9] = UInt64.ofNat 35 ∧ ω'[10] = UInt64.ofNat vp ∧ ω'[11] = UInt64.ofNat val.length ∧
    μ'.readN kp' 35 = key ∧ μ'.readN vp val.length = val ∧
    μ'.readN (sp - 96 + 32) 8 = Num.encodeLE 8 kc ∧ μ'.readN (sp - 96 + 24) 8 = Num.encodeLE 8 vc ∧
    μ'.readN (sp - 96) 8 = Num.encodeLE 8 vp ∧
    (∀ a, a < 4294967296 → Fr a → μ'.read a = μ.read a) ∧ (∀ a, Glob a → μ'.read a = μ.read a) ∧
    (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a)

/-- **From the loop's end (36405) to `set`'s call (48104)**, under accumulate's contract with the context
    and the stream kept: from `LoopInv n`, the key value kp at S + 16 (tag 2 at kp, on the stack above S),
    either the key buffer's `alloc` fails (the trap at 34070) or `SetPre` holds against the memory at
    36405 with the value ℰ(n) ++ ℰ(rs₀) ++ … (`encK n rs n`) and the frame from S + 56 up kept. -/
theorem res_exit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (c : AccCtx) (f : Stream)
    (ω : Regs) (μ : Memory) (s : State) (st : State) (μ₀ : Memory) (sp rp n kp kc pb S0 S1 : Nat)
    (rs : List Spec.Result) (L : LoopHyp pb S0 S1 sp rp n rs st μ₀)
    (I : LoopInv env.code pb S0 S1 sp rp n rs st μ₀ n ω μ s)
    (mk : μ.readN (sp - 96 + 16) 8 = Num.encodeLE 8 kp) (hkp : sp ≤ kp ∧ kp + 36 ≤ S1 ∧ kp + 64 < 4294967296)
    (mt : μ.readN kp 2 = Num.encodeLE 2 2)
    (mc : μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68696 ≤ a → a < 68704 → μ.readable a = true) :
    (∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36405 ω μ (c, f) 34070 ω' μ' (c, f) N) ∨
    ∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36405 ω μ (c, f) 48104 ω' μ' (c, f) N ∧
      SetPre env.code pb S0 S1 sp kc st μ (fun a => sp - 96 + 56 ≤ a) (keyEnc μ kp 2) (encK n rs n) ω' μ' := by
  obtain ⟨h1, -, -, H, ⟨vc, ptr, WP, mout, -, hst⟩, -, -, -⟩ := I
  obtain ⟨hsp, hS1, -, -, hB, -⟩ := L
  obtain ⟨-, -, mv, mp, ml, hlc, hc0, hcb, ch, hch, hchu, hcha, hchs⟩ := WP
  have hSt := H.st
  have hS1' := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have hci := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hch hchu
  generalize hlen : (encK n rs n).length = len at mout ml hlc
  -- A: 36405 → 33843
  obtain ⟨ω4, μ4, run4, g0, g1, -, g6, g7, g8, mS24, mS8, fr4, rd4, wr4⟩ :=
    rl_tail (R := (accHeapHost env).rel cap) (P := P) c ω μ (sp - 96) vc ptr len kp h1 (by omega) (by omega)
      (by omega) (by omega) (by omega) mv (by rw [show sp - 96 + 40 = sp - 96 + 32 + 8 by omega]; exact mp)
      (by rw [show sp - 96 + 48 = sp - 96 + 32 + 16 by omega]; exact ml) mk
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega))
  have H4 : HeapCtxC env.code pb S0 S1 μ4 s :=
    HeapKeep.keepHi H (fun a ha => fr4 a (by omega) (.inl (by omega)) (.inl (by omega))) wr4
  have k4 : ∀ a, a < 4294967296 → (a < sp - 96 + 8 ∨ sp - 96 + 32 ≤ a) → μ4.read a = μ.read a :=
    fun a h0 h => fr4 a h0 (by omega) (by omega)
  obtain ⟨ro1, ro2⟩ := HeapHost.keepRO (env := accHeapHost env) H.bd run4
  have kRO : ∀ a, a < 196608 → μ4.read a = μ.read a := fun a ha =>
    ro2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rRO : ∀ a, a < 196608 → μ4.readable a = μ.readable a := fun a ha => by
    unfold Memory.readable; rw [ro1 (a / pageSize) (.inl (by unfold pageSize; omega))]
  have hkE : keyEnc μ4 kp 2 = keyEnc μ kp 2 := by
    have e1 : μ4.readN (kp + 4) 32 = μ.readN (kp + 4) 32 :=
      Memory.readN_congr (fun j hj => k4 (kp + 4 + j) (by omega) (.inr (by omega)))
    have e2 : μ4.readN (kp + 2) 2 = μ.readN (kp + 2) 2 :=
      Memory.readN_congr (fun j hj => k4 (kp + 2 + j) (by omega) (.inr (by omega)))
    unfold keyEnc
    simp only [show (2 : Nat) = 1 ↔ False by decide, ite_false, ite_true, e1, e2]
  -- B: the key encoder
  rcases kb_call (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ω4 μ4 s (sp - 96) kp (sp - 96 + 32) 2 kc
      1704 36432 pb S0 S1 H4 g0 g1 g7 g8 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by rw [← mt]; exact Memory.readN_congr fun j hj => k4 _ (by omega) (.inr (by omega)))
      (by rw [← mc]; exact Memory.readN_congr fun j hj => kRO _ (by omega))
      (fun a h1 h2 => by rw [rRO a (by omega)]; exact hrt a (by omega) (by omega))
      ⟨by rw [keyEnc_length]; simp only [show (2 : Nat) ≠ 1 from by decide, if_false, if_true]; omega, hkc.2⟩
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_851]) bs_36432 with
    ⟨kp', s2, ω5, μ5, n5, -, run5, H5, keep5, hnew5, hfresh5, o0, o8, o16, okey, hg5, stk5, q0, q1, q5, q6⟩ |
    ⟨-, ω5, μ5, n5, run5⟩
  case inr =>
    obtain ⟨-, runS⟩ := FreeStepsH.growS f (run4.trans run5)
    exact .inl ⟨ω5, μ5, _, runS⟩
  have hkl : (keyEnc μ4 kp 2).length = 35 := by
    rw [keyEnc_length]; simp only [show (2 : Nat) ≠ 1 from by decide, if_false, if_true]
  rw [hkl] at okey o16
  rw [hkE] at okey
  have hb05 := H5.hb0
  have hbT5 := H5.hbT
  obtain ⟨n4, n5', n6⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H5.wf hnew5 rfl
  dsimp only at n4 n5' n6
  have hdiv : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- C: 36432 → 48104
  obtain ⟨ω6, μ6, run6, r0, r1, r5, r6, r7, r8, r9, r10, r11, mT, fr6, rd6, wr6⟩ :=
    rs_set (R := (accHeapHost env).rel cap) (P := P) c ω5 μ5 (sp - 96) kp' 35 ptr len (q1.trans g1)
      (q6.trans g6) (by omega) (by omega) (by decide) (by omega) (by omega)
      (by rw [show sp - 96 + 40 = sp - 96 + 32 + 8 by omega]; exact o8)
      (by rw [show sp - 96 + 48 = sp - 96 + 32 + 16 by omega]; exact o16)
      (by rw [← mS8]; exact Memory.readN_congr fun j hj => stk5 _ (by omega) (by omega) (.inl (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have H6 : HeapCtxC env.code pb S0 S1 μ6 s2 :=
    HeapKeep.keepHi H5 (fun a ha => fr6 a (by omega) (.inl (by omega))) wr6
  have run06 := (run4.trans run5).trans run6
  obtain ⟨ro1', ro2'⟩ := HeapHost.keepRO (env := accHeapHost env) H.bd run06
  obtain ⟨-, runS⟩ := FreeStepsH.growS f run06
  have hCv : ch ∈ chunks s2 := keep5 _ hch hchu
  have hCvk : ch ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ := hfresh5 _ hch hchu
  have k65 : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a ha => fr6 a (by omega) (.inl (by omega))
  -- a heap octet off the key's chunk is kept
  have kH : ∀ (d : Chunk), d ∈ chunks s → d.used = true → d ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ →
      ∀ a, InData d a → μ6.read a = μ.read a := by
    intro d hd hu hne a ha
    have hd2 := keep5 d hd hu
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have ap5 := InData.apart H5.wf hd2 hnew5 (Ne.symm hne) ha
    unfold InData at ap5; dsimp only at ap5
    have ha' := ha; unfold InData at ha'
    rw [k65 _ (by omega), hg5 _ (data_off H5.wf hb05 hbT5 hd2 ha) (by omega), k4 _ (by omega) (.inl (by omega))]
  refine .inr ⟨ω6, μ6, _, runS, ptr, kp', vc, ch, s2, H6, fun d hd hu => ?_, hCv, hchu, hcha, hnew5, hCvk,
    by omega, by omega, by omega, by omega, hc0, by omega, r0, r1, r5, r6.trans (q6.trans g6), r7, r8, r9, r10,
    by rw [r11, hlen], ?_, ?_, ?_, ?_, mT, ?_, ?_, ?_⟩
  · obtain ⟨k1, k2, k3⟩ := hst d hd hu
    have hne := hfresh5 d k1 hu
    refine ⟨keep5 d k1 hu, fun e => k2 (by rw [e, hcha]), hne, fun a ha => kH d k1 hu hne a ha⟩
  · rw [← okey]; exact Memory.readN_congr fun j hj => k65 _ (by omega)
  · rw [hlen, ← mout]
    exact Memory.readN_congr fun j hj => kH ch hch hchu hCvk _ ⟨by omega, by omega⟩
  · rw [← o0]; exact Memory.readN_congr fun j hj => fr6 _ (by omega) (.inr (by omega))
  · rw [← mS24]
    exact Memory.readN_congr fun j hj => by
      rw [fr6 _ (by omega) (.inr (by omega)), stk5 _ (by omega) (by omega) (.inl (by omega))]
  · intro a h0 ha
    rw [fr6 a h0 (.inr (by omega)), stk5 a h0 (by omega) (.inr (by omega)), k4 a h0 (.inr (by omega))]
  · intro a ha
    have hg := ha
    unfold Glob at hg
    rw [k65 _ (by omega), hg5 _ (glob_off H5.wf hb05 ha) (by omega), k4 _ (by omega) (.inl (by omega))]
  · intro a ha
    refine ⟨ro2' a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha), ?_⟩
    unfold Memory.readable; rw [ro1' (a / pageSize) (.inl (by unfold pageSize; omega))]

theorem encodeResults_nil' : encodeResults [] = [0] := rfl

theorem encK_all (n : Nat) (rs : List Spec.Result) (hn : rs.length = n) : encK n rs n = encodeResults rs := by
  unfold encK encodeResults vec
  rw [← hn, List.take_length]
  rfl

/-- `SetPre` against an earlier memory μ₀ that μ agrees with on st's data, on `Fr'` (inside `Fr`), at the
    globals and below 196608. -/
theorem SetPre.mono {code : ByteArray} {pb S0 S1 sp kc : Nat} {st : State} {μ μ₀ : Memory}
    {Fr Fr' : Nat → Prop} {key val : List UInt8} {ω' : Regs} {μ' : Memory}
    (h : SetPre code pb S0 S1 sp kc st μ Fr key val ω' μ')
    (hd : ∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ.read a = μ₀.read a)
    (hf : ∀ a, a < 4294967296 → Fr' a → Fr a ∧ μ.read a = μ₀.read a)
    (hg : ∀ a, Glob a → μ.read a = μ₀.read a)
    (hr : ∀ a, a < 196608 → μ.read a = μ₀.read a ∧ μ.readable a = μ₀.readable a) :
    SetPre code pb S0 S1 sp kc st μ₀ Fr' key val ω' μ' := by
  obtain ⟨vp, kp', vc, dv, s', H, hst, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
    r18, r19, r20, r21, r22, r23, r24, r25, fr, gl, ro⟩ := h
  refine ⟨vp, kp', vc, dv, s', H, fun d hd' hu => ?_, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14,
    r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, fun a h0 ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨k1, k2, k3, k4⟩ := hst d hd' hu
    exact ⟨k1, k2, k3, fun a ha => (k4 a ha).trans (hd d hd' hu a ha)⟩
  · obtain ⟨h1, h2⟩ := hf a h0 ha
    exact (fr a h0 h1).trans h2
  · exact (gl a ha).trans (hg a ha)
  · obtain ⟨a1, a2⟩ := ro a ha
    obtain ⟨b1, b2⟩ := hr a ha
    exact ⟨a1.trans b1, a2.trans b2⟩

/-- **The results store (36170 → `set`'s call at 48104), any n**, under accumulate's contract with the
    context and the stream kept, against `ExtendH` (R8) and `OkEncH` (R9): from ω₇ = rp, ω₈ = n, ω₉ = kp
    (the tag-2 key value on the stack above sp) and the n results at rp (`ResultsAt`, in `LoopHyp`),
    either an allocation fails (the trap at 36528 for the value's buffer, 34070 for the key's, or
    `ExhaustsP` while the value grows), or the run reaches 48104 in `SetPre` with the key `keyEnc μ kp 2`
    and the value ℰ(↕rs) (`encodeResults rs`), memory from sp up kept, and ω₀, ω₅, ω₆ saved at S + 88,
    S + 80, S + 72 (S = sp − 96). -/
theorem res_store {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (c : AccCtx) (f : Stream)
    (ω : Regs) (μ : Memory) (st : State) (sp rp n kp kc : Nat) (rs : List Spec.Result)
    (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rp) (h8 : ω[8] = UInt64.ofNat n)
    (h9 : ω[9] = UInt64.ofNat kp) (L : LoopHyp pb S0 S1 sp rp n rs st μ)
    (hkp : sp ≤ kp ∧ kp + 36 ≤ S1 ∧ kp + 64 < 4294967296) (mt : μ.readN kp 2 = Num.encodeLE 2 2)
    (mc : μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68696 ≤ a → a < 68704 → μ.readable a = true) :
    (∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36170 ω μ (c, f) 36528 ω' μ' (c, f) N) ∨
    (∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36170 ω μ (c, f) 34070 ω' μ' (c, f) N) ∨
    ExhaustsP p env pb 36170 ω μ c f ∨
    ∃ ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 36170 ω μ (c, f) 48104 ω' μ' (c, f) N ∧
      SetPre env.code pb S0 S1 sp kc st μ (fun a => sp ≤ a) (keyEnc μ kp 2) (encodeResults rs) ω' μ' ∧
      μ'.readN (sp - 96 + 88) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp - 96 + 80) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 96 + 72) 8 = Num.encodeLE 8 ω[6].toNat := by
  have L0 := L
  obtain ⟨hsp, hS1, hn, ⟨hrp1, hrp2⟩, hB, hR⟩ := L0
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · -- n = 0: `res_head`
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero hn
    subst hrs
    rcases res_head (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ω μ st sp rp kp kc pb S0 S1 H h1 h7 h8
        h9 (by omega) ⟨by omega, hsp.2.2.1⟩ (by omega) hkp mt mc hkc hrt with
      ⟨ω', μ', N, run⟩ | ⟨ω', μ', N, run⟩ |
      ⟨vp, kp', s', ω', μ', N, run, H', keep, hCv, hCk, hfr, hne, hv1, hv2, hk1, hk2, b0, b1, b5, b6, b7, b8,
        b9, b10, b11, mkey, mval, mkc, m4, mvp, m0, m5, m6, data, frs, gl, ro, rd⟩
    · exact .inl ⟨ω', μ', N, (FreeStepsH.growS f run).2⟩
    · exact .inr (.inl ⟨ω', μ', N, (FreeStepsH.growS f run).2⟩)
    refine .inr (.inr (.inr ⟨ω', μ', N, (FreeStepsH.growS f run).2, ⟨vp, kp', 4, _, s', H',
      fun d hd hu => ⟨keep d hd hu, (hfr d hd hu).1, (hfr d hd hu).2, data d hd hu⟩, hCv, rfl,
      by dsimp only; omega, hCk, hne, hv1, by simp [encodeResults_nil']; omega, hk1, hk2, by decide, by decide,
      b0, b1, b5, b6, b7, b8, b9, b10, by rw [b11]; rfl, mkey, by rw [encodeResults_nil']; exact mval, mkc, m4,
      mvp, frs, gl, fun a ha => ⟨ro a ha, rd a ha⟩⟩, m0, m5, m6⟩))
  -- n ≥ 1: into the loop
  rcases res_enter (P := P) env cap hcap1 hcap c f ω μ st sp rp n kp pb S0 S1 rs H h1 h7 h8 h9 (by omega)
      (by omega) L with
    ⟨ω', μ', N, run⟩ | ⟨ω1, μ1, s1, N1, run1, I0, mk1, mn1, m01, m51, m61, hd1, hsp1, hg1, hro1, hrd1⟩
  · exact .inl ⟨ω', μ', N, run⟩
  have L1 : LoopHyp pb S0 S1 sp rp n rs st μ1 :=
    ⟨hsp, hS1, hn, ⟨hrp1, hrp2⟩, hB, ResultsAt.keep (fun d hd hu => ⟨hd, hd1 d hd hu⟩) hR⟩
  rcases rl_loop hE hO c f sp rp n rs st μ1 L1 0 ω1 μ1 s1 (by omega) I0 with
    ⟨ω2, μ2, s2, N2, run2, In⟩ | hx
  rotate_left
  · exact .inr (.inr (.inl (ExhaustsP.pre run1 hx)))
  have In' := In
  obtain ⟨-, -, -, -, ⟨_, _, -, -, -, hst2⟩, fr2, lo2, gl2⟩ := In'
  have k2 : ∀ a, a < 4294967296 → sp ≤ a → μ2.read a = μ.read a := fun a h0 ha => by
    rw [fr2 a h0 (by omega) (.inr (by omega)), hsp1 a h0 ha]
  have mS : ∀ b v, sp - 96 + 57 ≤ b → b + 8 ≤ sp → μ1.readN b 8 = Num.encodeLE 8 v →
      μ2.readN b 8 = Num.encodeLE 8 v := fun b v h1 h2 hv => by
    rw [← hv]; exact Memory.readN_congr fun j hj => fr2 _ (by omega) (by omega) (.inr (by omega))
  rcases res_exit (P := P) env cap hcap1 hcap c f ω2 μ2 s2 st μ1 sp rp n kp kc pb S0 S1 rs L1 In
      (by rw [← mk1]; exact Memory.readN_congr fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega)))
      hkp (by rw [← mt]; exact Memory.readN_congr fun j hj => k2 _ (by omega) (by omega))
      (by rw [← mc]; exact Memory.readN_congr fun j hj => by rw [(lo2 _ (by omega)).1, hro1 _ (by omega)])
      hkc (fun a h1 h2 => by rw [(lo2 _ (by omega)).2, hrd1 _ (by omega)]; exact hrt a h1 h2) with
    ⟨ω', μ', N, run3⟩ | ⟨ω3, μ3, N3, run3, SP⟩
  · exact .inr (.inl ⟨ω', μ', _, (run1.trans run2).trans run3⟩)
  have hkE : keyEnc μ2 kp 2 = keyEnc μ kp 2 := by
    have e1 : μ2.readN (kp + 4) 32 = μ.readN (kp + 4) 32 :=
      Memory.readN_congr (fun j hj => k2 (kp + 4 + j) (by omega) (by omega))
    have e2 : μ2.readN (kp + 2) 2 = μ.readN (kp + 2) 2 :=
      Memory.readN_congr (fun j hj => k2 (kp + 2 + j) (by omega) (by omega))
    unfold keyEnc
    simp only [show (2 : Nat) = 1 ↔ False by decide, ite_false, ite_true, e1, e2]
  rw [hkE, encK_all n rs hn] at SP
  have SPg := SetPre.mono (μ₀ := μ) (Fr' := fun a => sp ≤ a) SP
    (fun d hd hu a ha => by rw [(hst2 d hd hu).2.2 a ha, hd1 d hd hu a ha])
    (fun a h0 (ha : sp ≤ a) => ⟨show sp - 96 + 56 ≤ a by omega, k2 a h0 ha⟩)
    (fun a ha => by rw [gl2 a ha, hg1 a ha])
    (fun a ha => ⟨by rw [(lo2 a ha).1, hro1 a ha], by rw [(lo2 a ha).2, hrd1 a ha]⟩)
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fr3, -, -⟩ :=
    SP
  have mF : ∀ b v, sp - 96 + 57 ≤ b → b + 8 ≤ sp → μ1.readN b 8 = Num.encodeLE 8 v →
      μ3.readN b 8 = Num.encodeLE 8 v := fun b v h1 h2 hv => by
    rw [← mS b v h1 h2 hv]; exact Memory.readN_congr fun j hj => fr3 _ (by omega) (by dsimp only; omega)
  exact .inr (.inr (.inr ⟨ω3, μ3, _, (run1.trans run2).trans run3, SPg, mF _ _ (by omega) (by omega) m01,
    mF _ _ (by omega) (by omega) m51, mF _ _ (by omega) (by omega) m61⟩))

end Services.Bootstrap.Acc.Handlers.ResStore
