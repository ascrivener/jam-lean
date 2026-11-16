import Services.Bootstrap.Acc.Handlers.RecentSlotWrite
import Services.Bootstrap.Decode.DeallocCall

/-!
# `add_recent_work_item`'s slot write as an `Impl` step (8172 → 8326)

`slot_write`: from 8172 with the counter c in ω₅, the run implements spec `addRecent`'s
`store (.recent c) (encodeRecent package item)` (GP v0.8.0 Appendix B, Ω_W) in `Impl`'s call form, with
the package the 32 octets at sp + 512 and ℰ₂(item) the two at sp + 176, and leaves the new counter
((c + 1) mod 2³²) mod 2·𝖢·𝖨 in ω₇'s low 32 bits (quirk Q19):
- `sw_head`, up to `set`'s call (48104), keeps the context: the copy and the callee frame, `alloc` of
  the value's buffer (null: the trap at 32584), the two `extend_from_slice`, the key encoder (whose
  `alloc` may fail: the trap at 34070);
- `set` (`set_call`) is Ω_W of ℰ(`recent c`) with the 34 octets;
- `sw_free`, after it: `dealloc` of both buffers and the return to 8266 with ω₇ = −1 for `Ok`, else
  `set`'s error code; then `Ok` goes on to 8326 (`sw_ok1`, `sw_ok2`) and FULL to the trap at 15361.
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlotWrite

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The octets above sp the slot write may change: the saved statics addresses (sp + 88, 16 octets),
    the copied (package, item) (sp + 1144, 34) and the key value (sp + 1568, 8). -/
def SwOut (sp a : Nat) : Prop :=
  (sp + 88 ≤ a ∧ a < sp + 104) ∨ (sp + 1144 ≤ a ∧ a < sp + 1178) ∨ (sp + 1568 ≤ a ∧ a < sp + 1576)

/-- A global (196616 … 196791) is off every header of a well-formed heap based at 206864 or above. -/
theorem glob_off {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base) {a : Nat} (ha : Glob a) :
    OffHdrG (fun h => ∃ d ∈ chunks s, d.addr = h) a := by
  unfold Glob at ha
  refine ⟨.inl ha, by omega, fun h ⟨d, hd, hda⟩ => ?_⟩
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have := ht.mem_lt d hd; subst hda; omega

/-- An octet of an allocated chunk's data is off every header. -/
theorem data_off {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {d : Chunk} (hd : d ∈ chunks s) {a : Nat} (ha : InData d a) :
    OffHdrG (fun h => ∃ d ∈ chunks s, d.addr = h) a := by
  have hoff := Services.Bootstrap.Alloc.off_hdr_data hwf hb0 hbT hd ha.1 ha.2
  exact ⟨.inr hoff.1, hoff.2.1, hoff.2.2⟩

/-- The two low octets of a word: ℰ₂ of it. -/
theorem readN_2of8 {μ : Memory} {b v : Nat} (h : μ.readN b 8 = Num.encodeLE 8 v) :
    μ.readN b 2 = Num.encodeLE 2 v := by
  have h2 := Services.Bootstrap.Decode.VecU8.readN_split μ b 2 6
  rw [show 2 + 6 = 8 from rfl, h, show 8 = 2 + 6 from rfl, Num.encodeLE_split] at h2
  exact (List.append_inj h2 (by simp [Memory.length_readN, Num.length_encodeLE])).1.symm

variable {X : Type}

/-- **From 8172 to `set`'s call (48104)**, under any `HeapHost` at a cap of at least 2²⁷: either an
    allocation fails (the trap at 32584 for the value's buffer, 34070 for the key's), or the run reaches
    48104 with `set`'s arguments: the key ℰ(`recent c`) (5 octets) in a new chunk at kp, the value
    (the 32 octets at sp + 512, then the two at sp + 176) in a new chunk at vp, out sp − 40; the callee
    frame at sp − 96 (vp, the value's and the key's capacities, ω₀ = 286, c and ω₆ saved); every old
    chunk kept with its data, the globals and read-only data kept, memory from sp up kept off `SwOut`. -/
theorem sw_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs) (μ : Memory) {hb : Nat}
    (st : State) (sp c kc pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 μ st)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat c) (hc : c < 2 ^ 32)
    (hsp : 2147483648 + 352 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 352 ≤ sp) (hS1 : sp + 1632 ≤ S1)
    (mc : μ.readN 68688 8 = Num.encodeLE 8 kc) (hkc : 5 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68688 ≤ a → a < 68696 → μ.readable a = true) :
    (∃ ω' μ' n, FreeStepsH p (env.rel cap) 8172 ω μ x 32584 ω' μ' x n) ∨
    (∃ ω' μ' n, FreeStepsH p (env.rel cap) 8172 ω μ x 34070 ω' μ' x n) ∨
    ∃ vp kp s' ω' μ' n, FreeStepsH p (env.rel cap) 8172 ω μ x 48104 ω' μ' x n ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ d ∈ chunks st, d.used = true → d ∈ chunks s') ∧
      (⟨vp - 32, 3, true⟩ : Chunk) ∈ chunks s' ∧ (⟨kp - 32, (kc + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks st, d.used = true → d ≠ ⟨vp - 32, 3, true⟩ ∧ d ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩) ∧
      (⟨vp - 32, 3, true⟩ : Chunk) ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩ ∧
      65536 ≤ vp ∧ vp + 34 ≤ 2147483648 ∧ 65536 ≤ kp ∧ kp + 5 ≤ 2147483648 ∧
      ω'[0] = UInt64.ofNat 1498 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat vp ∧
      ω'[6] = UInt64.ofNat kp ∧ ω'[7] = UInt64.ofNat (sp - 40) ∧ ω'[8] = UInt64.ofNat kp ∧
      ω'[9] = UInt64.ofNat 5 ∧ ω'[10] = UInt64.ofNat vp ∧ ω'[11] = UInt64.ofNat 34 ∧
      μ'.readN kp 5 = (Key.recent c).encode ∧
      μ'.readN vp 34 = μ.readN (sp + 512) 32 ++ μ.readN (sp + 176) 2 ∧
      μ'.readN (sp - 64) 8 = Num.encodeLE 8 kc ∧ μ'.readN (sp - 80) 8 = Num.encodeLE 8 34 ∧
      μ'.readN (sp - 96) 8 = Num.encodeLE 8 vp ∧ μ'.readN (sp - 8) 8 = Num.encodeLE 8 286 ∧
      μ'.readN (sp - 16) 8 = Num.encodeLE 8 c ∧ μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → ¬ SwOut sp a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.readable a = μ.readable a) := by
  have hSt := H.st
  have hS1' := H.hS1
  have hSb := H.hSb
  have hb0 := H.hb0
  have hbT := H.hbT
  have e8 : ∀ b, μ.readN b 8 = Num.encodeLE 8 (rdN μ b 8) := fun b => readN_enc μ b 8
  have lt8 : ∀ b, rdN μ b 8 < 2 ^ 64 := fun b => decodeLE_readN_lt μ b 8
  -- A: 8172 → 8221
  obtain ⟨ωA, μA, runA, a0, a1, a5, a6, mA0, mA1, mAq0, mAq1, mAq2, mAq3, mAv, frA, rdA, wrA⟩ :=
    sw_pre1 (R := env.rel cap) (P := P) x ω μ sp c _ _ _ _ _ h1 h5 (by omega) (by omega)
      (e8 (sp + 512)) (e8 (sp + 520)) (e8 (sp + 528)) (e8 (sp + 536)) (lt8 _) (lt8 _) (lt8 _) (lt8 _)
      (e8 (sp + 176)) (lt8 _)
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega)) (.inl (by omega))) wrA
  -- B: 8221 → 40494
  obtain ⟨ωB, μB, runB, b0, b1, b5, b6, b7, b8, mB72, mB8, mB16, mB24, frB, rdB, wrB⟩ :=
    sw_pre2 (R := env.rel cap) (P := P) x ωA μA sp a1 ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [wrA]; exact hSt a (by omega) (by omega))
  have HB : HeapCtxC env.code pb S0 S1 μB st :=
    HeapKeep.keepHi HA (fun a ha => frB a (by omega) (.inl (by omega))) wrB
  -- C: `alloc(34, 1)`
  rcases alloc_callG (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ωB μB st (sp - 96) 34 1 pb S0 S1 HB
      b1 b7 b8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨vp, s1, ω1, μ1, ha1, run1, H1, keep1, hnew1, hfresh1, hkg1, e7, stk1, f0, f1, f5, f6⟩ |
    ⟨-, ω1, μ1, run1, e7, -, f0, -, -, -⟩
  case inr =>
    exact .inl ⟨ω1, μ1, _, (((runA.trans runB).trans run1).trans
      (sw_j1 (P := P) x ω1 μ1 (f0.trans b0))).trans (sw_null (P := P) x ω1 μ1 e7)⟩
  simp only [Nat.reduceAdd, Nat.reduceDiv] at hnew1 hfresh1
  have hb01 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew1 rfl
  dsimp only at n1 n2 n3
  have hvp0 : vp ≠ 0 := by omega
  -- D: 40611 → 32414 → 58508
  have run1' := run1.trans (sw_j1 (P := P) x ω1 μ1 (f0.trans b0))
  obtain ⟨ω2, μ2, run2, c0, c1, c5, c6, c7, c8, c9, mV32, mV40, mV48, fr2, rd2, wr2⟩ :=
    sw_v1 (R := env.rel cap) (P := P) x ω1 μ1 (sp - 96) 34 vp (f1.trans b1) (f6.trans b6) e7 hvp0
      (by omega) (by decide) (by omega) (fun a h1 h2 => H1.st a (by omega) (by omega))
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s1 :=
    HeapKeep.keepHi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
  -- E: `extend(sp − 64, sp + 1144, 32)`
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, d1, l1, fr3, rd3, wr3⟩ :=
    Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 96)
      (sp - 64) (sp + 1144) 32 34 vp 0 1492 32441 ⟨by omega, by omega, by omega⟩ c0 c1
      (by rw [c7]; congr 1; omega) (by rw [c8, f5, b5]) c9 (by decide) (by decide)
      (by rw [show sp - 64 = sp - 96 + 32 by omega]; exact mV32)
      (by rw [show sp - 64 + 8 = sp - 96 + 40 by omega]; exact mV40)
      (by rw [show sp - 64 + 16 = sp - 96 + 48 by omega]; exact mV48) (by omega) (.inr (by omega))
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
      (.inr (by omega)) ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_745])
      bs_32441 (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => H2.st a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (fun a h1 h2 => HeapKeep.writableData H2 hnew1 rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
      (fun a h1 h2 => H2.st a (by omega) (by omega))
  have H3 : HeapCtxC env.code pb S0 S1 μ3 s1 :=
    HeapKeep.keepData H2 hnew1 (fun a h1 h2 => fr3 a (by omega) (.inl (by omega))
      (by dsimp only at h2; omega) (.inl (by omega))) (fun a => by rw [wr3])
  -- F: the `u16` to sp − 40, `extend(sp − 64, sp − 40, 2)`
  have mI3 : μ3.readN (sp + 1144 + 32) 2 = Num.encodeLE 2 (rdN μ (sp + 176) 8 % 65536) := by
    rw [encodeLE_mod 2, ← mAv]
    refine Memory.readN_congr fun j hj => ?_
    rw [fr3 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)),
      fr2 _ (by omega) (.inr (by omega)), stk1 _ (by omega) (by omega), frB _ (by omega) (.inr (by omega))]
  obtain ⟨ω4, μ4, run4, h0', h1', h5', h6', h7', h8', h9', m56, fr4, rd4, wr4⟩ :=
    sw_v2 (R := env.rel cap) (P := P) x ω3 μ3 (sp - 96) (sp + 1144) _ g1 (by rw [g5, c5, f5, b5])
      (by omega) (by omega) mI3 (Nat.mod_lt _ (by decide))
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have H4 : HeapCtxC env.code pb S0 S1 μ4 s1 :=
    HeapKeep.keepHi H3 (fun a ha => fr4 a (by omega) (.inl (by omega))) wr4
  have l1' : μ4.readN (sp - 64 + 16) 8 = Num.encodeLE 8 32 := by
    rw [← l1]; exact Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega))
  have k43 : ∀ b, sp - 64 ≤ b → b + 8 ≤ sp - 48 → μ4.readN b 8 = μ2.readN b 8 := fun b hb1 hb2 =>
    Memory.readN_congr fun j hj => by
      rw [fr4 _ (by omega) (.inl (by omega)), fr3 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))]
  have mV32' : μ4.readN (sp - 64) 8 = Num.encodeLE 8 34 := by
    rw [k43 _ (by omega) (by omega), show sp - 64 = sp - 96 + 32 by omega]; exact mV32
  have mV40' : μ4.readN (sp - 64 + 8) 8 = Num.encodeLE 8 vp := by
    rw [k43 _ (by omega) (by omega), show sp - 64 + 8 = sp - 96 + 40 by omega]; exact mV40
  obtain ⟨ω5, μ5, run5, i0, i1, i5, i6, d2, l2, fr5, rd5, wr5⟩ :=
    Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := env.rel cap) x ω4 μ4 (sp - 96)
      (sp - 64) (sp - 40) 2 34 vp 32 1494 32462 ⟨by omega, by omega, by omega⟩ h0' (h1')
      (by rw [h7']; congr 1; omega) (by rw [h8']; congr 1; omega) h9' (by decide) (by decide)
      mV32' mV40' l1' (by omega) (.inr (by omega))
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
      (.inr (by omega)) ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_746])
      bs_32462 (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
      (fun a h1 h2 => H4.st a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
      (fun a h1 h2 => HeapKeep.writableData H4 hnew1 rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
      (fun a h1 h2 => H4.st a (by omega) (by omega))
  have H5 : HeapCtxC env.code pb S0 S1 μ5 s1 :=
    HeapKeep.keepData H4 hnew1 (fun a h1 h2 => fr5 a (by omega) (.inl (by omega))
      (by dsimp only at h2; omega) (.inl (by omega))) (fun a => by rw [wr5])
  -- the value's 34 octets
  have hval : μ5.readN vp 34 = μ.readN (sp + 512) 32 ++ μ.readN (sp + 176) 2 := by
    rw [show 34 = 32 + 2 from rfl, Services.Bootstrap.Decode.VecU8.readN_split]
    congr 1
    · rw [show vp = vp + 0 from rfl, ← Nat.add_zero vp]
      refine (Memory.readN_congr fun j hj => ?_).trans (d1.trans ?_)
      · rw [fr5 _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
          fr4 _ (by omega) (.inl (by omega))]
      · rw [RecentMatch.readN_32, RecentMatch.readN_32 μ, e8 (sp + 512), e8 (sp + 520), e8 (sp + 528),
          e8 (sp + 536), ← mAq0, ← mAq1, ← mAq2, ← mAq3, show sp + 1144 + 8 = sp + 1152 by omega,
          show sp + 1144 + 16 = sp + 1160 by omega, show sp + 1144 + 24 = sp + 1168 by omega]
        have k : ∀ b, sp + 1144 ≤ b → b + 8 ≤ sp + 1176 → μ2.readN b 8 = μA.readN b 8 := fun b hb1 hb2 =>
          Memory.readN_congr fun j hj => by
            rw [fr2 _ (by omega) (.inr (by omega)), stk1 _ (by omega) (by omega),
              frB _ (by omega) (.inr (by omega))]
        rw [k _ (by omega) (by omega), k _ (by omega) (by omega), k _ (by omega) (by omega),
          k _ (by omega) (by omega)]
    · rw [d2, show sp - 40 = sp - 96 + 56 by omega, m56, readN_2of8 (e8 (sp + 176)), encodeLE_mod 2]
  -- G: 32462 → 33843
  have k5 : ∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 48 ∨ sp - 38 ≤ a) → μ5.read a = μ2.read a := by
    intro a h0 ha hb
    rw [fr5 a h0 (.inr ha) (.inr (by omega)) (by omega), fr4 a h0 (by omega),
      fr3 a h0 (.inr ha) (.inr (by omega)) (by omega)]
  have k5A : ∀ a, a < 4294967296 → sp ≤ a → μ5.read a = μA.read a := by
    intro a h0 ha
    rw [k5 a h0 (by omega) (by omega), fr2 a h0 (.inr (by omega)), stk1 a h0 (by omega), frB a h0 (.inr ha)]
  have m24 : μ5.readN (sp - 96 + 24) 8 = Num.encodeLE 8 (sp + 1568) := by
    rw [← mB72, show sp - 96 + 24 = sp - 72 by omega]
    exact Memory.readN_congr fun j hj => by
      rw [k5 _ (by omega) (by omega) (.inl (by omega)), fr2 _ (by omega) (.inl (by omega)),
        stk1 _ (by omega) (by omega)]
  have m32 : μ5.readN (sp - 96 + 32) 8 = Num.encodeLE 8 34 := by
    rw [← mV32]; exact Memory.readN_congr fun j hj => k5 _ (by omega) (by omega) (.inl (by omega))
  have m40 : μ5.readN (sp - 96 + 40) 8 = Num.encodeLE 8 vp := by
    rw [← mV40]; exact Memory.readN_congr fun j hj => k5 _ (by omega) (by omega) (.inl (by omega))
  have m48 : μ5.readN (sp - 96 + 48) 8 = Num.encodeLE 8 34 := by
    rw [show sp - 96 + 48 = sp - 64 + 16 by omega]; exact l2
  obtain ⟨ω6, μ6, run6, j0, j1, j5, j6, j7, j8, m16, m8, fr6, rd6, wr6⟩ :=
    sw_v3 (R := env.rel cap) (P := P) x ω5 μ5 (sp - 96) 34 vp 34 (sp + 1568) i1 (by omega) (by decide)
      (by omega) (by decide) (by omega) m32 m40 m48 m24
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have H6 : HeapCtxC env.code pb S0 S1 μ6 s1 :=
    HeapKeep.keepHi H5 (fun a ha => fr6 a (by omega) (.inl (by omega))) wr6
  have k6A : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μA.read a := fun a h0 ha => by
    rw [fr6 a h0 (.inr (by omega)), k5A a h0 ha]
  -- read-only data, up to the key encoder
  have run06 := (((((((runA.trans runB).trans run1').trans run2).trans run3).trans run4).trans run5).trans run6)
  obtain ⟨ro1, ro2⟩ := HeapHost.keepRO (env := env) H.bd run06
  have kRO : ∀ a, a < 196608 → μ6.read a = μ.read a := fun a ha =>
    ro2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  have rRO : ∀ a, a < 196608 → μ6.readable a = μ.readable a := fun a ha => by
    unfold Memory.readable; rw [ro1 (a / pageSize) (.inl (by unfold pageSize; omega))]
  -- H: the key encoder
  have mt : μ6.readN (sp + 1568) 2 = Num.encodeLE 2 1 := by
    rw [← mA0]; exact Memory.readN_congr fun j hj => k6A _ (by omega) (by omega)
  have mcK : μ6.readN (68680 + 8 * 1) 8 = Num.encodeLE 8 kc := by
    rw [← mc]; exact Memory.readN_congr fun j hj => kRO _ (by omega)
  have mck : μ6.readN (sp + 1572) 4 = Num.encodeLE 4 c := by
    rw [← mA1]; exact Memory.readN_congr fun j hj => k6A _ (by omega) (by omega)
  have hkE : keyEnc μ6 (sp + 1568) 1 = (Key.recent c).encode := by
    simp only [keyEnc, if_true, show sp + 1568 + 4 = sp + 1572 by omega, mck]; rfl
  rcases kb_call (P := P) (hb := hb) env cap hcap1 hcap x ω6 μ6 s1 (sp - 96) (sp + 1568) (sp - 64) 1 kc
      1496 32489 pb S0 S1 H6 j0 j1 (by rw [j7]; congr 1; omega) j8 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) mt mcK
      (fun a h1 h2 => by rw [rRO a (by omega)]; exact hrt a (by omega) (by omega))
      ⟨by rw [keyEnc_length]; simp only [if_true]; omega, hkc.2⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_747]) bs_32489 with
    ⟨kp, s2, ω7, μ7, n7, -, run7, H7, keep7, hnew7, hfresh7, o0, o8, o16, ok7, hg7, stk7, q0, q1, q5, q6⟩ |
    ⟨-, ω7, μ7, n7, run7⟩
  case inr => exact .inr (.inl ⟨ω7, μ7, _, run06.trans run7⟩)
  rw [hkE] at ok7 o16
  have hb07 := H7.hb0
  have hbT7 := H7.hbT
  obtain ⟨n4, n5, n6⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H7.wf hnew7 rfl
  dsimp only at n4 n5 n6
  have hkl : (Key.recent c).encode.length = 5 := by simp [Key.encode, JAM.Codec.fixed, Num.length_encodeLE]
  rw [hkl] at ok7 o16
  -- I: 32489 → 48104
  have m8' : μ7.readN (sp - 96 + 8) 8 = Num.encodeLE 8 34 := by
    rw [← m8]; exact Memory.readN_congr fun j hj => stk7 _ (by omega) (by omega) (.inl (by omega))
  obtain ⟨ω8, μ8, run8, r0, r1, r5, r6, r7, r8, r9, r10, r11, mT, fr8, rd8, wr8⟩ :=
    sw_v4 (R := env.rel cap) (P := P) x ω7 μ7 (sp - 96) vp kp 5 34 (q1.trans j1) (q5.trans j5) (by omega)
      (by omega) (by omega) (by decide) (by decide)
      (by rw [show sp - 96 + 40 = sp - 64 + 8 by omega]; exact o8)
      (by rw [show sp - 96 + 48 = sp - 64 + 16 by omega]; exact o16) m8'
      (fun a h1 h2 => Memory.readable_of_writable (H7.st a (by omega) (by omega)))
      (fun a h1 h2 => H7.st a (by omega) (by omega))
  have H8 : HeapCtxC env.code pb S0 S1 μ8 s2 :=
    HeapKeep.keepHi H7 (fun a ha => fr8 a (by omega) (.inl (by omega))) wr8
  have run08 := (run06.trans run7).trans run8
  obtain ⟨ro1', ro2'⟩ := HeapHost.keepRO (env := env) H.bd run08
  have hCv : (⟨vp - 32, 3, true⟩ : Chunk) ∈ chunks s2 := keep7 _ hnew1 rfl
  have hCvk : (⟨vp - 32, 3, true⟩ : Chunk) ≠ ⟨kp - 32, (kc + 31) / 32 + 1, true⟩ := hfresh7 _ hnew1 rfl
  have hdiv : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- the frame below the stack, across the run
  have k78 : ∀ a, a < 2147483648 → μ8.read a = μ7.read a := fun a ha => fr8 a (by omega) (.inl (by omega))
  have k65 : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a ha => fr6 a (by omega) (.inl (by omega))
  have k52 : ∀ a, a < 2147483648 → (a < vp ∨ vp + 34 ≤ a) → μ5.read a = μ2.read a := fun a ha hv => by
    rw [fr5 a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)), fr4 a (by omega) (.inl (by omega)),
      fr3 a (by omega) (.inl (by omega)) (by omega) (.inl (by omega))]
  have k2B : ∀ a, a < 2147483648 → OffHdrG (fun h => ∃ d ∈ chunks s1, d.addr = h) a → μ2.read a = μB.read a :=
    fun a ha ho => by rw [fr2 a (by omega) (.inl (by omega)), hkg1 a ho]
  have kB0 : ∀ a, a < 2147483648 → μB.read a = μ.read a := fun a ha => by
    rw [frB a (by omega) (.inl (by omega)), frA a (by omega) (.inl (by omega)) (.inl (by omega))]
  -- the stack, across the run
  have kS : ∀ a, a < 4294967296 → sp - 24 ≤ a → μ8.read a = μ1.read a := fun a h0 ha => by
    rw [fr8 a h0 (.inr (by omega)), stk7 a h0 (by omega) (.inr (by omega)), fr6 a h0 (.inr (by omega)),
      k5 a h0 (by omega) (by omega), fr2 a h0 (.inr (by omega))]
  have mS : ∀ b v, sp - 24 ≤ b → b + 8 ≤ sp → μB.readN b 8 = Num.encodeLE 8 v → μ8.readN b 8 = Num.encodeLE 8 v :=
    fun b v h1 h2 hv => by
      rw [← hv]; exact Memory.readN_congr fun j hj => by rw [kS _ (by omega) (by omega), stk1 _ (by omega) (by omega)]
  refine .inr (.inr ⟨vp, kp, s2, ω8, μ8, _, run08, H8, fun d hd hu => keep7 d (keep1 d hd hu) hu, hCv, hnew7,
    fun d hd hu => ⟨hfresh1 d hd hu, hfresh7 d (keep1 d hd hu) hu⟩, hCvk, by omega, by omega, by omega, by omega,
    r0, r1, r5, r6, by rw [r7]; congr 1; omega, r8, r9, r10, r11, ?_, ?_, ?_, ?_, ?_, mS _ _ (by omega) (by omega) mB8,
    mS _ _ (by omega) (by omega) (by rw [mB16, a5, h5, UInt64.toNat_ofNat']; congr 1; omega),
    mS _ _ (by omega) (by omega) (by rw [mB24, a6]), ?_, ?_, ?_, ?_, ?_⟩)
  · rw [← ok7]; exact Memory.readN_congr fun j hj => k78 _ (by omega)
  · rw [← hval]
    refine Memory.readN_congr fun j hj => ?_
    have hin : InData ⟨vp - 32, 3, true⟩ (vp + j) := ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hap := InData.apart H7.wf hCv hnew7 (Ne.symm hCvk) hin
    unfold InData at hap; dsimp only at hap
    rw [k78 _ (by omega), hg7 _ (data_off H7.wf hb07 hbT7 hCv hin) (by omega), k65 _ (by omega)]
  · rw [← o0]; exact Memory.readN_congr fun j hj => fr8 _ (by omega) (.inr (by omega))
  · rw [show sp - 80 = sp - 96 + 16 by omega, ← m16]
    exact Memory.readN_congr fun j hj => by
      rw [fr8 _ (by omega) (.inr (by omega)), stk7 _ (by omega) (by omega) (.inl (by omega))]
  · rw [show sp - 96 = sp - 96 + 0 from rfl]; exact mT
  · intro d hd hu a ha
    have hd1 := keep1 d hd hu
    have hd2 := keep7 d hd1 hu
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have ap1 := InData.apart H1.wf hd1 hnew1 (Ne.symm (hfresh1 d hd hu)) ha
    have ap7 := InData.apart H7.wf hd2 hnew7 (Ne.symm (hfresh7 d hd1 hu)) ha
    unfold InData at ap1 ap7; dsimp only at ap1 ap7
    have ha' := ha; unfold InData at ha'
    rw [k78 _ (by omega), hg7 _ (data_off H7.wf hb07 hbT7 hd2 ha) (by omega), k65 _ (by omega),
      k52 _ (by omega) (by omega), k2B _ (by omega) (data_off H1.wf hb01 hbT1 hd1 ha), kB0 _ (by omega)]
  · intro a h0 ha hO
    unfold SwOut at hO
    rw [fr8 a h0 (.inr (by omega)), stk7 a h0 (by omega) (.inr (by omega)), fr6 a h0 (.inr (by omega)),
      k5A a h0 ha, frA a h0 (by omega) (by omega)]
  · intro a ha
    have hg := ha
    unfold Glob at hg
    rw [k78 _ (by omega), hg7 _ (glob_off H7.wf hb07 ha) (by omega), k65 _ (by omega),
      k52 _ (by omega) (by omega), k2B _ (by omega) (glob_off H1.wf hb01 ha), kB0 _ (by omega)]
  · intro a ha
    exact ro2' a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a ha)
  · intro a ha
    unfold Memory.readable; rw [ro1' (a / pageSize) (.inl (by unfold pageSize; omega))]

end Services.Bootstrap.Acc.Handlers.RecentSlotWrite
