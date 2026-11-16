import Services.Bootstrap.Acc.Handlers.ResStoreSeg
import Services.Bootstrap.Acc.Handlers.RecentSlotWriteImpl
import Services.Bootstrap.Encode.VecCore

/-!
# The results store (36170) for n = 0: up to `set` and after it

`on_work_item`'s empty results write (GP v0.8.0 Appendix B, Ω_W of ℰ(↕[]) = [0]) through 36170 in the
callee frame S = sp − 96, composed like the slot write's `sw_head` / `sw_free`:
- `res_head` (36170 → 48104, `set`'s call): `rs_pre`, `alloc(4, 1)` (null: the trap at 36528), `rs_vec`,
  ℰ(0) by `prefix_any`, `rs_zero`, the key encoder (`kb_call`, tag 2; its `alloc` may fail: the trap at
  34070), `rs_set`;
- `res_free` (`set`'s return → 8477): `rs_ret`, `rs_d1`, `dealloc` of the key's buffer, `rs_d2`, `dealloc`
  of the value's buffer, `rs_end` (ω₇ = −1 for `Ok`, else `set`'s error code).
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc Services.Bootstrap.Acc.Handlers.RecentSlotWrite

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type}

/-- **40611, `alloc`'s return** with ω₀ = 1692: on to 36217. -/
theorem rs_j1 {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h0 : ω[0] = UInt64.ofNat 1692) : FreeStepsH p R 40611 ω μ x 36217 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **From 36170 to `set`'s call (48104), n = 0**, under any `HeapHost` at a cap of at least 2²⁷, with
    the key value at kp (tag 2: the `u16` 2 at kp, then the item's `u16` and the 32 package octets) on
    the stack above sp: either an allocation fails (the trap at 36528 for the value's buffer, 34070 for
    the key's), or the run reaches 48104 with `set`'s arguments: the key `keyEnc μ kp 2` (35 octets) in
    a new chunk at kp′, the value ℰ(0) = [0] in a new chunk at vp, out S + 56 (S = sp − 96); the callee
    frame (vp at S, the value's capacity 4 at S + 24, the key's kc at S + 32, ω₀, ω₅, ω₆ saved at S + 88,
    S + 80, S + 72); every old chunk kept with its data, memory from sp up, the globals and read-only
    data (with its access) kept. -/
theorem res_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs) (μ : Memory)
    {hb : Nat} (st : State) (sp rp kp kc pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rp) (h8 : ω[8] = UInt64.ofNat 0)
    (h9 : ω[9] = UInt64.ofNat kp) (hrp : rp < 2 ^ 64)
    (hsp : 2147483648 + 352 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 352 ≤ sp)
    (hkp : sp ≤ kp ∧ kp + 36 ≤ S1 ∧ kp + 64 < 4294967296)
    (mt : μ.readN kp 2 = Num.encodeLE 2 2)
    (mc : μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68696 ≤ a → a < 68704 → μ.readable a = true) :
    (∃ ω' μ' n, FreeStepsH p (env.rel cap) 36170 ω μ x 36528 ω' μ' x n) ∨
    (∃ ω' μ' n, FreeStepsH p (env.rel cap) 36170 ω μ x 34070 ω' μ' x n) ∨
    ∃ vp kp' s' ω' μ' n, FreeStepsH p (env.rel cap) 36170 ω μ x 48104 ω' μ' x n ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ d ∈ chunks st, d.used = true → d ∈ chunks s') ∧
      (⟨vp - 32, 2, true⟩ : Chunk) ∈ chunks s' ∧ (⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks st, d.used = true → d ≠ ⟨vp - 32, 2, true⟩ ∧ d ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩) ∧
      (⟨vp - 32, 2, true⟩ : Chunk) ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ ∧
      65536 ≤ vp ∧ vp + 1 ≤ 2147483648 ∧ 65536 ≤ kp' ∧ kp' + 35 ≤ 2147483648 ∧
      ω'[0] = UInt64.ofNat 1706 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat kp' ∧
      ω'[6] = UInt64.ofNat vp ∧ ω'[7] = UInt64.ofNat (sp - 96 + 56) ∧ ω'[8] = UInt64.ofNat kp' ∧
      ω'[9] = UInt64.ofNat 35 ∧ ω'[10] = UInt64.ofNat vp ∧ ω'[11] = UInt64.ofNat 1 ∧
      μ'.readN kp' 35 = keyEnc μ kp 2 ∧ μ'.readN vp 1 = [0] ∧
      μ'.readN (sp - 96 + 32) 8 = Num.encodeLE 8 kc ∧ μ'.readN (sp - 96 + 24) 8 = Num.encodeLE 8 4 ∧
      μ'.readN (sp - 96) 8 = Num.encodeLE 8 vp ∧ μ'.readN (sp - 96 + 88) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp - 96 + 80) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 96 + 72) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.readable a = μ.readable a) := by
  have hSt := H.st
  have hS1' := H.hS1
  have hSb := H.hSb
  have hb0 := H.hb0
  have hbT := H.hbT
  have hkp64 : kp < 2 ^ 64 := by omega
  -- A: 36170 → 40494
  obtain ⟨ωA, μA, runA, a0, a1, a5, a6, a7, a8, mA0, mA5, mA6, mAk, mAn, -, frA, rdA, wrA⟩ :=
    rs_pre (R := env.rel cap) (P := P) x ω μ sp rp 0 kp h1 h7 h8 h9 ⟨by omega, by omega⟩ hrp (by decide) hkp64
      (fun a h1 h2 => hSt a (by omega) (by omega))
  simp only [Nat.mul_zero, Nat.zero_add] at a5 a7
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega))) wrA
  -- B: `alloc(4, 1)`
  rcases alloc_callG (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ωA μA st (sp - 96) 4 1 pb S0 S1 HA
      a1 a7 a8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨vp, s1, ω1, μ1, -, run1, H1, keep1, hnew1, hfresh1, hkg1, e7, stk1, f0, f1, f5, f6⟩ |
    ⟨-, ω1, μ1, run1, e7, -, f0, -, -, -⟩
  case inr =>
    exact .inl ⟨ω1, μ1, _, ((runA.trans run1).trans (rs_j1 (P := P) x ω1 μ1 (f0.trans a0))).trans
      (rs_null (P := P) x ω1 μ1 e7)⟩
  simp only [Nat.reduceAdd, Nat.reduceDiv] at hnew1 hfresh1
  have hb01 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew1 rfl
  dsimp only at n1 n2 n3
  have hvp0 : vp ≠ 0 := by omega
  have run1' := run1.trans (rs_j1 (P := P) x ω1 μ1 (f0.trans a0))
  -- C: 36217 → 30977
  have k1A : ∀ a, a < 4294967296 → sp - 96 ≤ a → μ1.read a = μA.read a := fun a h0 ha => stk1 a h0 ha
  obtain ⟨ω2, μ2, run2, c0, c1, c5, c6, c7, c8, mV32, mV40, mV48, mV56, fr2, rd2, wr2⟩ :=
    rs_vec (R := env.rel cap) (P := P) x ω1 μ1 (sp - 96) 0 vp (f1.trans a1) (by rw [f5, a5]) e7 hvp0
      (by omega) (by decide) (by omega)
      (by rw [show sp - 96 + 24 = sp - 72 by omega, ← mAn]
          exact Memory.readN_congr fun j hj => k1A _ (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H1.st a (by omega) (by omega)))
      (fun a h1 h2 => H1.st a (by omega) (by omega))
  simp only [Nat.mul_zero, Nat.zero_add] at mV32
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s1 :=
    HeapKeep.keepHi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
  -- D: ℰ(0) by `prefix_any`
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := rfl
  have hn0 : rdN μ2 (sp - 96 + 56) 4 = 0 := by
    show Num.decodeLE _ = _; rw [mV56, Num.decodeLE_encodeLE]
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, dval, dlen, fr3, rd3, wr3⟩ :=
    Services.Bootstrap.Encode.Enc.prefix_any (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 96)
      (sp - 96 + 56) (sp - 96 + 32) 4 vp 0 1694 36263 0 ω2[6].toNat 0 ⟨by omega, by omega, by omega⟩ c0 c1
      (by rw [c5, f5, a5]) UInt64.ofNat_toNat.symm c7 c8 (by decide) (UInt64.toNat_lt _) (by omega) (.inr (by omega))
      hn0 (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega))) mV32 mV40 mV48
      (by rw [he]; decide) (by decide) (by omega) (.inr (by omega))
      (by rw [he]; simp only [List.length_cons, List.length_nil]; omega)
      (.inr (by rw [he]; simp only [List.length_cons, List.length_nil]; omega))
      (.inr (by rw [he]; simp only [List.length_cons, List.length_nil]; omega))
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_846]) bs_36263
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => H2.st a (by omega) (by omega))
      (fun a h1 h2 => HeapKeep.writableData H2 hnew1 rfl
        ⟨by dsimp only; rw [he] at h2; omega, by dsimp only; rw [he] at h2; simp at h2; omega⟩)
      (fun a h1 h2 => H2.st a (by omega) (by omega))
  rw [he] at dval dlen fr3
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] at dval dlen fr3
  have H3 : HeapCtxC env.code pb S0 S1 μ3 s1 :=
    HeapKeep.keepData H2 hnew1 (fun a h1 h2 => fr3 a (by omega) (.inl (by omega))
      (by dsimp only at h2; omega) (.inl (by omega))) (fun a => by rw [wr3])
  -- E: 36263 → 33843
  have k3 : ∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 48 ∨ sp - 96 + 56 ≤ a) →
      μ3.read a = μ2.read a := fun a h0 h1 h2 => fr3 a h0 (.inr (by omega)) (.inr (by omega)) h2
  have k31 : ∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 60 ≤ a) →
      μ3.read a = μA.read a := fun a h0 h1 h2 => by
    rw [k3 a h0 h1 (by omega), fr2 a h0 h2, k1A a h0 h1]
  obtain ⟨ω4, μ4, run4, g0, g1, g5, g6, g7, g8, mS24, mS8, fr4, rd4, wr4⟩ :=
    rs_zero (R := env.rel cap) (P := P) x ω3 μ3 (sp - 96) 4 vp 1 kp (d1) (by omega) (by decide) (by omega)
      (by decide) hkp64
      (by rw [show sp - 96 + 24 = sp - 72 by omega, ← mAn]
          exact Memory.readN_congr fun j hj => k31 _ (by omega) (by omega) (.inl (by omega)))
      (by rw [← mV32]; exact Memory.readN_congr fun j hj => k3 _ (by omega) (by omega) (.inl (by omega)))
      (by rw [← mV40]; exact Memory.readN_congr fun j hj => k3 _ (by omega) (by omega) (.inl (by omega)))
      (by rw [show sp - 96 + 48 = sp - 96 + 32 + 16 by omega]; exact dlen)
      (by rw [show sp - 96 + 16 = sp - 80 by omega, ← mAk]
          exact Memory.readN_congr fun j hj => k31 _ (by omega) (by omega) (.inl (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have H4 : HeapCtxC env.code pb S0 S1 μ4 s1 :=
    HeapKeep.keepHi H3 (fun a ha => fr4 a (by omega) (.inl (by omega)) (.inl (by omega))) wr4
  have k4A : ∀ a, a < 4294967296 → sp ≤ a → μ4.read a = μ.read a := fun a h0 ha => by
    rw [fr4 a h0 (.inr (by omega)) (.inr (by omega)), k31 a h0 (by omega) (.inr (by omega)),
      frA a h0 (.inr ha)]
  -- read-only data, up to the key encoder
  have run04 := (((runA.trans run1').trans run2).trans run3).trans run4
  obtain ⟨ro1, ro2⟩ := HeapHost.keepRO (env := env) H.bd run04
  have kRO : ∀ a, a < 196608 → μ4.read a = μ.read a := fun a ha =>
    ro2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rRO : ∀ a, a < 196608 → μ4.readable a = μ.readable a := fun a ha => by
    unfold Memory.readable; rw [ro1 (a / pageSize) (.inl (by unfold pageSize; omega))]
  -- F: the key encoder
  have hkE : keyEnc μ4 kp 2 = keyEnc μ kp 2 := by
    have e1 : μ4.readN (kp + 4) 32 = μ.readN (kp + 4) 32 :=
      Memory.readN_congr (fun j hj => k4A (kp + 4 + j) (by omega) (by omega))
    have e2 : μ4.readN (kp + 2) 2 = μ.readN (kp + 2) 2 :=
      Memory.readN_congr (fun j hj => k4A (kp + 2 + j) (by omega) (by omega))
    unfold keyEnc
    simp only [show (2 : Nat) = 1 ↔ False by decide, ite_false, ite_true, e1, e2]
  rcases kb_call (P := P) (hb := hb) env cap hcap1 hcap x ω4 μ4 s1 (sp - 96) kp (sp - 96 + 32) 2 kc
      1704 36432 pb S0 S1 H4 g0 g1 g7 g8 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by rw [← mt]; exact Memory.readN_congr fun j hj => k4A _ (by omega) (by omega))
      (by rw [← mc]; exact Memory.readN_congr fun j hj => kRO _ (by omega))
      (fun a h1 h2 => by rw [rRO a (by omega)]; exact hrt a (by omega) (by omega))
      ⟨by rw [keyEnc_length]; simp only [show (2 : Nat) ≠ 1 from by decide, if_false, if_true]; omega, hkc.2⟩
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_851]) bs_36432 with
    ⟨kp', s2, ω5, μ5, n5, -, run5, H5, keep5, hnew5, hfresh5, o0, o8, o16, okey, hg5, stk5, q0, q1, q5, q6⟩ |
    ⟨-, ω5, μ5, n5, run5⟩
  case inr => exact .inr (.inl ⟨ω5, μ5, _, run04.trans run5⟩)
  have hkl : (keyEnc μ4 kp 2).length = 35 := by
    rw [keyEnc_length]; simp only [show (2 : Nat) ≠ 1 from by decide, if_false, if_true]
  rw [hkl] at okey o16
  rw [hkE] at okey
  have hb05 := H5.hb0
  have hbT5 := H5.hbT
  obtain ⟨n4, n5', n6⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H5.wf hnew5 rfl
  dsimp only at n4 n5' n6
  have hdiv : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- G: 36432 → 48104
  obtain ⟨ω6, μ6, run6, r0, r1, r5, r6, r7, r8, r9, r10, r11, mT, fr6, rd6, wr6⟩ :=
    rs_set (R := env.rel cap) (P := P) x ω5 μ5 (sp - 96) kp' 35 vp 1 (q1.trans g1) (q6.trans g6) (by omega)
      (by omega) (by decide) (by decide) (by omega)
      (by rw [show sp - 96 + 40 = sp - 96 + 32 + 8 by omega]; exact o8)
      (by rw [show sp - 96 + 48 = sp - 96 + 32 + 16 by omega]; exact o16)
      (by rw [← mS8]; exact Memory.readN_congr fun j hj => stk5 _ (by omega) (by omega) (.inl (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have H6 : HeapCtxC env.code pb S0 S1 μ6 s2 :=
    HeapKeep.keepHi H5 (fun a ha => fr6 a (by omega) (.inl (by omega))) wr6
  have run06 := (run04.trans run5).trans run6
  obtain ⟨ro1', ro2'⟩ := HeapHost.keepRO (env := env) H.bd run06
  have hCv : (⟨vp - 32, 2, true⟩ : Chunk) ∈ chunks s2 := keep5 _ hnew1 rfl
  have hCvk : (⟨vp - 32, 2, true⟩ : Chunk) ≠ ⟨kp' - 32, (kc + 31) / 32 + 1, true⟩ := hfresh5 _ hnew1 rfl
  -- the heap, across the run
  have k65 : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a ha => fr6 a (by omega) (.inl (by omega))
  have k43 : ∀ a, a < 2147483648 → μ4.read a = μ3.read a := fun a ha =>
    fr4 a (by omega) (.inl (by omega)) (.inl (by omega))
  have k32 : ∀ a, a < 2147483648 → (a < vp ∨ vp + 1 ≤ a) → μ3.read a = μ2.read a := fun a ha hv =>
    fr3 a (by omega) (.inl (by omega)) hv (.inl (by omega))
  have k2A : ∀ a, a < 2147483648 → OffHdrG (fun h => ∃ d ∈ chunks s1, d.addr = h) a → μ2.read a = μA.read a :=
    fun a ha ho => by rw [fr2 a (by omega) (.inl (by omega)), hkg1 a ho]
  have kA0 : ∀ a, a < 2147483648 → μA.read a = μ.read a := fun a ha => frA a (by omega) (.inl (by omega))
  -- the stack frame, across the run
  have kS : ∀ a, a < 4294967296 → sp - 96 + 56 ≤ a → μ6.read a = μ4.read a := fun a h0 ha => by
    rw [fr6 a h0 (.inr (by omega)), stk5 a h0 (by omega) (.inr (by omega))]
  have mS : ∀ b v, sp - 96 + 64 ≤ b → b + 8 ≤ sp → μA.readN b 8 = Num.encodeLE 8 v → μ6.readN b 8 = Num.encodeLE 8 v :=
    fun b v h1 h2 hv => by
      rw [← hv]
      exact Memory.readN_congr fun j hj => by
        rw [kS _ (by omega) (by omega), fr4 _ (by omega) (.inr (by omega)) (.inr (by omega)),
          k31 _ (by omega) (by omega) (.inr (by omega))]
  refine .inr (.inr ⟨vp, kp', s2, ω6, μ6, _, run06, H6, fun d hd hu => keep5 d (keep1 d hd hu) hu, hCv, hnew5,
    fun d hd hu => ⟨hfresh1 d hd hu, hfresh5 d (keep1 d hd hu) hu⟩, hCvk, by omega, by omega, by omega, by omega,
    r0, r1, r5, r6.trans (q6.trans g6), r7, r8, r9, r10, r11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [← okey]; exact Memory.readN_congr fun j hj => k65 _ (by omega)
  · rw [show ([0] : List UInt8) = [UInt8.ofNat 0] from rfl, ← dval]
    refine Memory.readN_congr fun j hj => ?_
    have hin : InData ⟨vp - 32, 2, true⟩ (vp + j) := ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hap := InData.apart H5.wf hCv hnew5 (Ne.symm hCvk) hin
    unfold InData at hap; dsimp only at hap
    rw [k65 _ (by omega), hg5 _ (data_off H5.wf hb05 hbT5 hCv hin) (by omega), k43 _ (by omega)]
  · rw [← o0]; exact Memory.readN_congr fun j hj => fr6 _ (by omega) (.inr (by omega))
  · rw [← mS24]
    exact Memory.readN_congr fun j hj => by
      rw [fr6 _ (by omega) (.inr (by omega)), stk5 _ (by omega) (by omega) (.inl (by omega))]
  · rw [show sp - 96 = sp - 96 + 0 from rfl]; exact mT
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 88 = sp - 8 by omega]; exact mA0)
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 80 = sp - 16 by omega]; exact mA5)
  · exact mS _ _ (by omega) (by omega) (by rw [show sp - 96 + 72 = sp - 24 by omega]; exact mA6)
  · intro d hd hu a ha
    have hd1 := keep1 d hd hu
    have hd2 := keep5 d hd1 hu
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have ap1 := InData.apart H1.wf hd1 hnew1 (Ne.symm (hfresh1 d hd hu)) ha
    have ap5 := InData.apart H5.wf hd2 hnew5 (Ne.symm (hfresh5 d hd1 hu)) ha
    unfold InData at ap1 ap5; dsimp only at ap1 ap5
    have ha' := ha; unfold InData at ha'
    rw [k65 _ (by omega), hg5 _ (data_off H5.wf hb05 hbT5 hd2 ha) (by omega), k43 _ (by omega),
      k32 _ (by omega) (by omega), k2A _ (by omega) (data_off H1.wf hb01 hbT1 hd1 ha), kA0 _ (by omega)]
  · intro a h0 ha
    rw [kS a h0 (by omega), k4A a h0 ha]
  · intro a ha
    have hg := ha
    unfold Glob at hg
    rw [k65 _ (by omega), hg5 _ (glob_off H5.wf hb05 ha) (by omega), k43 _ (by omega),
      k32 _ (by omega) (by omega), k2A _ (by omega) (glob_off H1.wf hb01 ha), kA0 _ (by omega)]
  · intro a ha
    exact ro2' a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  · intro a ha
    unfold Memory.readable; rw [ro1' (a / pageSize) (.inl (by unfold pageSize; omega))]

open Services.Bootstrap.Decode.DeallocCall in
/-- **From `set`'s return to 8477, any value chunk** (`res_free` for a value buffer that is the data of
    an allocated chunk dv, dv.addr + 32 = vp, with capacity vc ≠ 0 at S + 24), under any host relation: `set`'s return (ω₀ = 1706) to 36456, the
    result word r (at S + 56, S = sp − 96) saved at S + 16, `dealloc` of the key's buffer (the chunk at
    kp − 32) and of the value's (at vp − 32), and the return to 8477 with ω₇ = −1 if r ≠ −1, else the
    octet b at S + 64 (`set`'s error code); ω₁ = sp, ω₅ and ω₆ restored. The context is kept for both
    frees; memory is kept from S up but at S + 16, at the globals, where it is not writable, and in every
    other allocated chunk's data. -/
theorem res_freeG {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (sp vp kp kc r b v5 v6 e vc : Nat) (dv : Chunk) (H : HeapCtxC code pb S0 S1 μ s)
    (hCv : dv ∈ chunks s) (hdu : dv.used = true) (hda : dv.addr + 32 = vp)
    (hCk : (⟨kp - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s)
    (hne : dv ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩) (hkp : 32 ≤ kp) (hvc : vc < 2 ^ 64) (hvc0 : vc ≠ 0)
    (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 1706)
    (h1 : ω[1] = UInt64.ofNat (sp - 96)) (h5 : ω[5] = UInt64.ofNat kp) (h6 : ω[6] = UInt64.ofNat vp)
    (hsp : 2147483648 + 352 ≤ sp) (hS : S0 + 352 ≤ sp ∧ sp ≤ S1)
    (hkc : kc < 2 ^ 64) (hk0 : kc ≠ 0) (hr64 : r < 2 ^ 64) (hb : b < 256) (hv5 : v5 < 2 ^ 64) (hv6 : v6 < 2 ^ 64)
    (mk : μ.readN (sp - 96 + 32) 8 = Num.encodeLE 8 kc) (mr : μ.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r)
    (mb : μ.readN (sp - 96 + 64) 1 = Num.encodeLE 1 b) (mc : μ.readN (sp - 96 + 24) 8 = Num.encodeLE 8 vc)
    (mv : μ.readN (sp - 96) 8 = Num.encodeLE 8 vp) (m0 : μ.readN (sp - 96 + 88) 8 = Num.encodeLE 8 294)
    (m5 : μ.readN (sp - 96 + 80) 8 = Num.encodeLE 8 v5) (m6 : μ.readN (sp - 96 + 72) 8 = Num.encodeLE 8 v6) :
    ∃ ω' μ' n, FreeStepsH p R e ω μ x 8477 ω' μ' x n ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) ∧
      HeapCtxC code pb S0 S1 μ' (free (free s kp) vp) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ dv → d ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩ →
        d ∈ chunks (free (free s kp) vp) ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 16 ∨ sp - 96 + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → μ.writable a = false → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) := by
  have hst := H.st
  have hS1 := H.hS1
  have hbT := H.hbT
  obtain ⟨-, -, nv⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hCv hdu
  have run0 := rs_ret (R := R) (P := P) x ω μ e he h0
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, m16, fr1, rd1, wr1⟩ :=
    rs_d1 (R := R) (P := P) x ω μ (sp - 96) kc r b h1 (by omega) hkc hk0 hr64 hb mk mr mb
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have H1 : HeapCtxC code pb S0 S1 μ1 s :=
    HeapKeep.keepHi H (fun a ha => fr1 a (by omega) (.inl (by omega))) wr1
  obtain ⟨ω2, μ2, run2, H2, -, pg2, ro2, stk2, gl2, keep2, g0, g1, g5, g6⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω1 μ1 s (sp - 96) kp 1708 36482 _ H1 hCk rfl
      (by dsimp only; omega) a0 a1 (a7.trans h5) ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_853]) bs_36482 (by omega) ⟨by omega, by omega⟩
  have k21 : ∀ b n, sp - 96 ≤ b → b + n ≤ 4294967296 → μ2.readN b n = μ1.readN b n := fun b n h1 h2 =>
    Memory.readN_congr fun j hj => stk2 _ (by omega) (by omega)
  have k10 : ∀ b n, sp - 96 ≤ b → b + n ≤ 4294967296 → (b + n ≤ sp - 96 + 16 ∨ sp - 96 + 24 ≤ b) →
      μ1.readN b n = μ.readN b n := fun b n h1 h2 h3 =>
    Memory.readN_congr fun j hj => fr1 _ (by omega) (by omega)
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ :=
    rs_d2 (R := R) (P := P) x ω2 μ2 (sp - 96) vc vp (g1.trans a1) (by omega) hvc hvc0 (by omega)
      (by rw [k21 _ _ (by omega) (by omega), k10 _ _ (by omega) (by omega) (.inr (by omega))]; exact mc)
      (by rw [k21 _ _ (by omega) (by omega), k10 _ _ (by omega) (by omega) (.inl (by omega))]; exact mv)
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
  have hCv2 : dv ∈ chunks (free s kp) := (keep2 _ hCv hdu hne).1
  obtain ⟨ω4, μ4, run4, H4, -, pg4, ro4, stk4, gl4, keep4, d0, d1, d5, d6⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω3 μ2 (free s kp) (sp - 96) vp 1710 36499 _ H2
      hCv2 hdu hda c0 c1 c7 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_854]) bs_36499 (by omega) ⟨by omega, by omega⟩
  have k4 : ∀ b n, sp - 96 ≤ b → b + n ≤ 4294967296 → (b + n ≤ sp - 96 + 16 ∨ sp - 96 + 24 ≤ b) →
      μ4.readN b n = μ.readN b n := fun b n h1 h2 h3 => by
    rw [← k10 _ _ h1 h2 h3, ← k21 _ _ h1 h2]
    exact Memory.readN_congr fun j hj => stk4 _ (by omega) (by omega)
  have m16' : μ4.readN (sp - 96 + 16) 8 = Num.encodeLE 8 r := by
    rw [← m16]
    exact Memory.readN_congr fun j hj => (stk4 _ (by omega) (by omega)).trans (stk2 _ (by omega) (by omega))
  obtain ⟨ω5, run5, e1, e5, e6, e7⟩ :=
    rs_end (R := R) (P := P) x ω4 μ4 (sp - 96) r b v5 v6 (d1.trans c1)
      (d6.trans (c6.trans (g6.trans a6))) (by omega) (by omega) hr64 hv5 hv6 m16'
      (by rw [k4 _ _ (by omega) (by omega) (.inr (by omega))]; exact m0)
      (by rw [k4 _ _ (by omega) (by omega) (.inr (by omega))]; exact m5)
      (by rw [k4 _ _ (by omega) (by omega) (.inr (by omega))]; exact m6)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
  refine ⟨ω5, μ4, _, (((run0.trans run1).trans run2).trans run3).trans (run4.trans run5),
    by rw [e1]; congr 1; omega, e5, e6, e7, H4, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd hu hv hk
    obtain ⟨k1, k2⟩ := keep2 d hd hu hk
    obtain ⟨k3, k4'⟩ := keep4 d k1 hu hv
    refine ⟨k3, fun a ha => ?_⟩
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have := H.hbT
    unfold InData at ha
    rw [k4' a ha, k2 a ha, fr1 a (by omega) (.inl (by omega))]
  · intro a h0 ha hb
    rw [stk4 a h0 (by omega), stk2 a h0 (by omega), fr1 a h0 (by omega)]
  · intro a ha
    unfold Glob at ha
    rw [gl4 a ha, gl2 a ha, fr1 a (by omega) (.inl (by omega))]
  · intro a h0 hw
    have hw1 : μ1.writable a = false := by rw [wr1]; exact hw
    rw [ro4 a (by unfold two32; omega) (by unfold Memory.writable at hw1 ⊢; rw [pg2]; exact hw1),
      ro2 a (by unfold two32; omega) hw1]
    by_cases hs : sp - 96 + 16 ≤ a ∧ a < sp - 96 + 24
    · exact absurd (hst a (by omega) (by omega)) (by rw [hw]; simp)
    · exact fr1 a h0 (by omega)
  · intro a
    rw [show μ4.readable a = μ1.readable a by unfold Memory.readable; rw [pg4, pg2], rd1]


/-- **From `set`'s return to 8477**, under any host relation: `set`'s return (ω₀ = 1706) to 36456, the
    result word r (at S + 56, S = sp − 96) saved at S + 16, `dealloc` of the key's buffer (the chunk at
    kp − 32) and of the value's (at vp − 32), and the return to 8477 with ω₇ = −1 if r ≠ −1, else the
    octet b at S + 64 (`set`'s error code); ω₁ = sp, ω₅ and ω₆ restored. The context is kept for both
    frees; memory is kept from S up but at S + 16, at the globals, where it is not writable, and in every
    other allocated chunk's data. -/
theorem res_free {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (sp vp kp kc r b v5 v6 e : Nat) (H : HeapCtxC code pb S0 S1 μ s)
    (hCv : (⟨vp - 32, 2, true⟩ : Chunk) ∈ chunks s)
    (hCk : (⟨kp - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s)
    (hne : (⟨vp - 32, 2, true⟩ : Chunk) ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩) (hvp : 32 ≤ vp) (hkp : 32 ≤ kp)
    (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 1706)
    (h1 : ω[1] = UInt64.ofNat (sp - 96)) (h5 : ω[5] = UInt64.ofNat kp) (h6 : ω[6] = UInt64.ofNat vp)
    (hsp : 2147483648 + 352 ≤ sp) (hS : S0 + 352 ≤ sp ∧ sp ≤ S1)
    (hkc : kc < 2 ^ 64) (hk0 : kc ≠ 0) (hr64 : r < 2 ^ 64) (hb : b < 256) (hv5 : v5 < 2 ^ 64) (hv6 : v6 < 2 ^ 64)
    (mk : μ.readN (sp - 96 + 32) 8 = Num.encodeLE 8 kc) (mr : μ.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r)
    (mb : μ.readN (sp - 96 + 64) 1 = Num.encodeLE 1 b) (mc : μ.readN (sp - 96 + 24) 8 = Num.encodeLE 8 4)
    (mv : μ.readN (sp - 96) 8 = Num.encodeLE 8 vp) (m0 : μ.readN (sp - 96 + 88) 8 = Num.encodeLE 8 294)
    (m5 : μ.readN (sp - 96 + 80) 8 = Num.encodeLE 8 v5) (m6 : μ.readN (sp - 96 + 72) 8 = Num.encodeLE 8 v6) :
    ∃ ω' μ' n, FreeStepsH p R e ω μ x 8477 ω' μ' x n ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) ∧
      HeapCtxC code pb S0 S1 μ' (free (free s kp) vp) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨vp - 32, 2, true⟩ → d ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩ →
        d ∈ chunks (free (free s kp) vp) ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 16 ∨ sp - 96 + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → μ.writable a = false → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) :=
  res_freeG (R := R) (P := P) code pb S0 S1 x ω μ s sp vp kp kc r b v5 v6 e 4 _ H hCv rfl (by dsimp only; omega)
    hCk hne hkp (by decide) (by decide) he h0 h1 h5 h6 hsp hS hkc hk0 hr64 hb hv5 hv6 mk mr mb mc mv m0 m5 m6

end Services.Bootstrap.Acc.Handlers.ResStore
