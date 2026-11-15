import Services.Bootstrap.Acc.Handlers.RecentSlotSeg
import Services.Bootstrap.Acc.Handlers.ReadExactText
import Services.Bootstrap.Acc.Handlers.HeapKeep
import Services.Bootstrap.Acc.Wrappers.GetCall
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Spec

/-!
# The ring slot's typed `get` (34377): from `get`'s `Some` to the return

`slotDec` is `addRecent`'s decoder for a ring slot (32 octets, then a 2-octet number; GP v0.8.0
Appendix C's ℰ for the SDK's `(H, u16)`), and `SlotOut` the record 34377 leaves at out: the `u16` 0
(`None`), or the `u16` 1, the 32 octets at out + 2 and the 2 at out + 34 (`Some`).

- `sg_fret`: `dealloc` of the value's buffer (40613, return address 1608), then the return;
- `sg_tailW`: from 34434 with `get`'s value w ≠ [] in a fresh chunk: the reads (`read_exact`, short
  or not), the record at out, `dealloc`, the return. Under any host relation (no host calls).
- `sg_tailE`: the same for the empty value (capacity 0, no `dealloc`).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlot

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `addRecent`'s decoder of a ring slot: 32 octets, then a 2-octet number. -/
def slotDec : Dec (Bytes × Nat) := do return (← Dec.take 32, ← Dec.fixedN 2)

theorem slotDec_long (w : Bytes) (h : 34 ≤ w.length) :
    decode slotDec w = some (w.take 32, Num.decodeLE ((w.drop 32).take 2)) := by
  simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
    Option.bind, show 32 ≤ w.length by omega, show 2 ≤ w.length - 32 by omega]

theorem slotDec_short (w : Bytes) (h : w.length < 34) : decode slotDec w = none := by
  by_cases h32 : 32 ≤ w.length
  · simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
      Option.bind, h32, show ¬ 2 ≤ w.length - 32 by omega]
  · simp [decode, slotDec, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure,
      Option.bind, h32]

/-- **The record 34377 leaves at out**: the `u16` 0 for `None`; for `Some (q, k)` the `u16` 1, q
    at out + 2 and ℰ₂(k) at out + 34. -/
def SlotOut (μ : Memory) (out : Nat) : Option (Bytes × Nat) → Prop
  | none => μ.readN out 2 = Num.encodeLE 2 0
  | some (q, k) => μ.readN out 2 = Num.encodeLE 2 1 ∧ μ.readN (out + 2) 32 = q ∧
      μ.readN (out + 34) 2 = Num.encodeLE 2 k

theorem rdN_of_readN {μ : Memory} {a n v : Nat} (h : μ.readN a n = Num.encodeLE n v) (hv : v < 2 ^ (8 * n)) :
    rdN μ a n = v := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

theorem readN_rdN (μ : Memory) (a n : Nat) : μ.readN a n = Num.encodeLE n (rdN μ a n) := by
  have := encodeLE_decodeLE (μ.readN a n)
  rw [Memory.length_readN] at this
  exact this.symm

open Services.Bootstrap.Decode.DeallocCall in
/-- **40613 … the return**: `dealloc` of the value's buffer (the chunk V at vptr − 32), returning
    to 34623 (1608), then ω₀, ω₅, ω₆ restored from S + 104, + 96, + 88 and the return to t. The
    context is kept for `free s vptr`; memory is kept from S on, at the globals, below 196608 and in
    every other allocated chunk's data. -/
theorem sg_fret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (S vptr r0 v5 v6 t : Nat)
    (V : Chunk) (H : HeapCtxC code pb S0 S1 μ s) (hV : V ∈ chunks s) (hVu : V.used = true)
    (hVa : V.addr + 32 = vptr) (h0 : ω[0] = UInt64.ofNat 1608) (h1 : ω[1] = UInt64.ofNat S)
    (h7 : ω[7] = UInt64.ofNat vptr) (hS : 2147483716 ≤ S ∧ S + 112 < 4294967296) (hSS : S0 + 40 ≤ S ∧ S + 112 ≤ S1)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 254 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ HeapCtxC code pb S0 S1 μ' (free s vptr) ∧
      (∀ a, a < 4294967296 → S ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ V → d ∈ chunks (free s vptr) ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨ω1, μ1, run1, H1, -, -, ro1, stk1, gl1, keep1, g0, g1, -, -⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω μ s S vptr 1608 34623 V H hV hVu hVa h0 h1 h7
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_803]) bs_34623 hS.1
      ⟨hSS.1, by omega⟩
  have kf : ∀ o, S ≤ o → o + 8 ≤ S + 112 → μ1.readN o 8 = μ.readN o 8 := fun o ho ho' =>
    Memory.readN_congr fun j hj => stk1 _ (by omega) (by omega)
  obtain ⟨ω2, run2, e0, e1, e5, e6⟩ := sg_ret (P := P) (R := R) x ω1 μ1 S r0 v5 v6 t (g1.trans h1)
    ⟨by omega, by omega⟩ (by rw [kf _ (by omega) (by omega)]; exact m104) (by rw [kf _ (by omega) (by omega)]; exact m96)
    (by rw [kf _ (by omega) (by omega)]; exact m88) hr0 hv5 hv6 hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (H1.st a (by omega) (by omega)))
  refine ⟨ω2, μ1, (run1.trans run2).mono (by omega), e0, e1, e5, e6, H1, fun a h0 ha => stk1 a h0 ha,
    gl1, fun a ha => ro1 a (by unfold two32; omega) (H.ro a ha), fun d hd hu hne => keep1 d hd hu hne⟩

theorem okMem_read (μ : Memory) (out w0 w1 w2 w3 k a : Nat) (hout : out + 36 < 4294967296) (ha : a < 4294967296)
    (hoff : a < out ∨ out + 36 ≤ a) : (okMem μ out w0 w1 w2 w3 k).read a = μ.read a := by
  unfold okMem
  rw [rd_wr _ _ _ _ 2 (Num.length_encodeLE ..) (by omega) (by omega) ha,
    rd_wr _ _ _ _ 2 (Num.length_encodeLE ..) (by omega) (by omega) ha,
    rd_wr _ _ _ _ 8 (Num.length_encodeLE ..) (by omega) (by omega) ha,
    rd_wr _ _ _ _ 8 (Num.length_encodeLE ..) (by omega) (by omega) ha,
    rd_wr _ _ _ _ 8 (Num.length_encodeLE ..) (by omega) (by omega) ha,
    rd_wr _ _ _ _ 8 (Num.length_encodeLE ..) (by omega) (by omega) ha]

theorem okMem_writable (μ : Memory) (out w0 w1 w2 w3 k a : Nat) :
    (okMem μ out w0 w1 w2 w3 k).writable a = μ.writable a := by
  unfold okMem; simp only [Memory.writable_writeN]

theorem okMem_slot (μ : Memory) (out w0 w1 w2 w3 k : Nat) (hout : out + 36 < 4294967296)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616) (hk : k < 65536) :
    (okMem μ out w0 w1 w2 w3 k).readN out 2 = Num.encodeLE 2 1 ∧
    (okMem μ out w0 w1 w2 w3 k).readN (out + 2) 32 =
      Num.encodeLE 8 w0 ++ Num.encodeLE 8 w1 ++ Num.encodeLE 8 w2 ++ Num.encodeLE 8 w3 ∧
    (okMem μ out w0 w1 w2 w3 k).readN (out + 34) 2 = Num.encodeLE 2 k := by
  refine ⟨?_, ?_, ?_⟩
  · unfold okMem; exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE ..) (by unfold two32; omega)
  · rw [show 32 = 8 + (8 + (8 + 8)) from rfl, Decode.VecU8.readN_split, Decode.VecU8.readN_split,
      Decode.VecU8.readN_split]
    simp only [List.append_assoc]
    unfold okMem
    congr 1
    · post_simp [Nat.mod_eq_of_lt hw0]
    congr 1
    · rw [show out + 2 + 8 = out + 10 by omega]; post_simp [Nat.mod_eq_of_lt hw1]
    congr 1
    · rw [show out + 2 + 8 + 8 = out + 18 by omega]; post_simp [Nat.mod_eq_of_lt hw2]
    · rw [show out + 2 + 8 + 8 + 8 = out + 26 by omega]; post_simp [Nat.mod_eq_of_lt hw3]
  · unfold okMem; post_simp [Nat.mod_eq_of_lt hk]

open Services.Bootstrap.Decode.DeallocCall in
/-- **34434 … the return, `get` gave a value w ≠ []** in a fresh chunk V (at vptr − 32, of
    ⌈|w|/32⌉ + 1 units; the value's `Vec` {|w|, vptr, |w|} at S + 24): the reads, the record
    `SlotOut` of `decode slotDec w` at out, `dealloc` of V and the return to t (the saved r0 at
    S + 104). Under any host relation. The context is kept for `free s vptr`; memory is kept from
    S + 112 on off out … out + 36, at the globals, below 196608 and in every other allocated chunk's
    data. -/
theorem sg_tailW {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (S out vptr r0 v5 v6 t : Nat)
    (w : List UInt8) (H : HeapCtxC code pb S0 S1 μ s)
    (hV : (⟨vptr - 32, (w.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s) (hvp : 32 ≤ vptr)
    (hw0 : w ≠ []) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat out)
    (hS : 2147483648 + 128 ≤ S ∧ S % 8 = 0) (hSS : S0 + 88 ≤ S ∧ S + 112 ≤ S1)
    (hout : S + 112 ≤ out ∧ out + 36 ≤ S1)
    (mc : μ.readN (S + 24) 8 = Num.encodeLE 8 w.length) (mp : μ.readN (S + 32) 8 = Num.encodeLE 8 vptr)
    (ml : μ.readN (S + 40) 8 = Num.encodeLE 8 w.length) (mw : μ.readN vptr w.length = w)
    (m104 : μ.readN (S + 104) 8 = Num.encodeLE 8 r0) (m96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v5)
    (m88 : μ.readN (S + 88) 8 = Num.encodeLE 8 v6)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ' n, FreeStepsH p R 34434 ω μ x t ω' μ' x n ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ SlotOut μ' out (decode slotDec w) ∧
      HeapCtxC code pb S0 S1 μ' (free s vptr) ∧
      (∀ a, a < 4294967296 → S + 112 ≤ a → (a < out ∨ out + 36 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨vptr - 32, (w.length + 31) / 32 + 1, true⟩ →
        d ∈ chunks (free s vptr) ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
  have hst := H.st
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hV rfl
  dsimp only at n1 n2 n3
  have hL0 : 0 < w.length := List.length_pos_iff.mpr hw0
  have hdiv : w.length ≤ 32 * ((w.length + 31) / 32) := by omega
  have hvL : vptr + w.length < 2147483648 := by omega
  have hvr : ∀ a, vptr ≤ a → a < vptr + w.length → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (HeapKeep.writableData H hV rfl (by unfold HeapKeep.InData; dsimp only; omega))
  -- the finish: from 40613 (ω₀ = 1608, ω₇ = vptr), for any memory μX that differs from μ only at
  -- S − 88 … S + 88 and at out … out + 36, with the record at out
  have fin : ∀ ωX μX nX, FreeStepsH p R 34434 ω μ x 40613 ωX μX x nX → ωX[0] = UInt64.ofNat 1608 →
      ωX[1] = UInt64.ofNat S → ωX[7] = UInt64.ofNat vptr →
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S + 88 ≤ a) → (a < out ∨ out + 36 ≤ a) → μX.read a = μ.read a) →
      (∀ a, μX.writable a = μ.writable a) → SlotOut μX out (decode slotDec w) →
      ∃ ω' μ' n, FreeStepsH p R 34434 ω μ x t ω' μ' x n ∧
        ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
        ω'[6] = UInt64.ofNat v6 ∧ SlotOut μ' out (decode slotDec w) ∧
        HeapCtxC code pb S0 S1 μ' (free s vptr) ∧
        (∀ a, a < 4294967296 → S + 112 ≤ a → (a < out ∨ out + 36 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
        (∀ d ∈ chunks s, d.used = true → d ≠ ⟨vptr - 32, (w.length + 31) / 32 + 1, true⟩ →
          d ∈ chunks (free s vptr) ∧ ∀ a, InData d a → μ'.read a = μ.read a) := by
    intro ωX μX nX runX x0 x1 x7 frX wrX slX
    have HX : HeapCtxC code pb S0 S1 μX s :=
      HeapKeep.keepHi H (fun a ha => frX a (by omega) (.inl (by omega)) (.inl (by omega))) wrX
    have kX : ∀ o, S + 88 ≤ o → o + 8 ≤ S + 112 → μX.readN o 8 = μ.readN o 8 := fun o h1 h2 =>
      Memory.readN_congr fun j hj => frX _ (by omega) (.inr (by omega)) (.inl (by omega))
    obtain ⟨ωF, μF, runF, f0, f1, f5, f6, HF, stkF, glF, roF, keepF⟩ :=
      sg_fret (R := R) (P := P) code pb S0 S1 x ωX μX s S vptr r0 v5 v6 t _ HX hV rfl (by dsimp only; omega)
        x0 x1 x7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by rw [kX _ (by omega) (by omega)]; exact m104)
        (by rw [kX _ (by omega) (by omega)]; exact m96) (by rw [kX _ (by omega) (by omega)]; exact m88)
        hr0 hv5 hv6 hret hjt hbt
    have kF : ∀ o n, S ≤ o → o + n ≤ 4294967296 → μF.readN o n = μX.readN o n := fun o n h1 h2 =>
      Memory.readN_congr fun j hj => stkF _ (by omega) (by omega)
    refine ⟨ωF, μF, _, runX.trans runF, f0, f1, f5, f6, ?_, HF, ?_, ?_, ?_, ?_⟩
    · cases hd : decode slotDec w with
      | none => rw [hd] at slX; unfold SlotOut at slX ⊢; rw [kF _ _ (by omega) (by omega)]; exact slX
      | some qk =>
        obtain ⟨q, k⟩ := qk
        rw [hd] at slX; unfold SlotOut at slX ⊢
        rw [kF _ _ (by omega) (by omega), kF _ _ (by omega) (by omega), kF _ _ (by omega) (by omega)]
        exact slX
    · intro a h0 ha hb; rw [stkF a h0 (by omega), frX a h0 (.inr (by omega)) hb]
    · intro a ha; unfold Glob at ha; rw [glF a ha, frX a (by omega) (.inl (by omega)) (.inl (by omega))]
    · intro a ha; rw [roF a ha, frX a (by omega) (.inl (by omega)) (.inl (by omega))]
    · intro d hd hu hne
      obtain ⟨k1, k2⟩ := keepF d hd hu hne
      refine ⟨k1, fun a ha => ?_⟩
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      unfold InData at ha
      rw [k2 a ha, frX a (by omega) (.inl (by omega)) (.inl (by omega))]
  -- 34434 → 58434
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, mS, mS8, mS16, fr1, rd1, wr1⟩ :=
    sg_some (P := P) (R := R) x ω μ S w.length vptr w.length h1 ⟨by omega, by omega⟩ (by omega) (by omega)
      (by omega) (by omega) mc mp ml (fun a h1 h2 => hst a (by omega) (by omega))
  have l2 : (Num.encodeLE 2 0).length = 2 := Num.length_encodeLE ..
  by_cases hA : w.length < 32
  · -- a short first read
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, fr2, rd2, wr2⟩ := re_short (P := P) (R := R) x ω1 μ1 S (S + 8) 32
      w.length 1604 34485 ⟨by omega, by omega⟩ a0 a1 a7 a9 (by decide) ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_801]) bs_34485
      (by rw [show S + 8 + 8 = S + 16 by omega]; exact rdN_of_readN mS16 (show w.length < 18446744073709551616 by omega))
      hA (by omega) (.inr (by omega))
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
    have mp2 : μ2.readN S 8 = Num.encodeLE 8 vptr := by
      rw [← mS]; exact Memory.readN_congr fun j hj => fr2 _ (by omega) (.inr (by omega))
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := sg_shortD (P := P) (R := R) x ω2 μ2 34485 S out 1 w.length vptr
      (.inl rfl) (b1.trans a1) (b5.trans (a5.trans h5)) (b6.trans a6) b7 (by decide) (by decide) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ mp2
      (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr2, wr1]; exact hst a (by omega) (by omega))
    refine fin ω3 _ _ ((run1.trans run2).trans run3) c0 c1 c7 (fun a h0 ha hb => ?_) (fun a => ?_) ?_
    · rw [rd_wr _ _ _ _ 2 l2 (by omega) (by omega) h0, fr2 a h0 (by omega), fr1 a h0 (by omega) (by omega)]
    · rw [Memory.writable_writeN, wr2, wr1]
    · rw [slotDec_short w (by omega)]; unfold SlotOut
      exact Memory.readN_writeN_same _ _ _ _ l2 (by unfold two32; omega)
  -- the first read: 32 octets into S + 56
  have hrS : ∀ a, S - 88 ≤ a → a < S + 112 → μ1.writable a = true := fun a h1 h2 => by
    rw [wr1]; exact hst a (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, cp2, rp2, rl2, fr2, rd2, wr2⟩ := read_exact_text (P := P) (R := R)
    x ω1 μ1 S (S + 8) (S + 56) 32 vptr w.length 1604 34485 ⟨by omega, by omega, hS.2⟩ a0 a1 a7 a8 a9
    ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_801]) bs_34485
    (rdN_of_readN mS8 (show vptr < 18446744073709551616 by omega))
    (by rw [show S + 8 + 8 = S + 16 by omega]; exact rdN_of_readN mS16 (show w.length < 18446744073709551616 by omega))
    (by omega) (.inr (by omega)) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega))
    (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd1]; exact hvr a h1 (by omega)) (fun a h1 h2 => hrS a (by omega) (by omega))
    (fun a h1 h2 => hrS a (by omega) (by omega)) (fun a h1 h2 => hrS a (by omega) (by omega))
  have k1lo : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (.inl (by omega)) (.inl (by omega))
  have hw32 : μ2.readN (S + 56) 32 = w.take 32 := by
    rw [cp2, Memory.readN_congr (μ := μ) (fun j hj => k1lo _ (by omega))]
    obtain ⟨m, hm⟩ : ∃ m, w.length = 32 + m := ⟨w.length - 32, by omega⟩
    rw [← mw, hm, Decode.VecU8.readN_split, List.take_left' (Memory.length_readN ..)]
  -- 34485 → 58434: the words copied to S + 24, the second read of 2 octets
  have hrS2 : ∀ a, S - 88 ≤ a → a < S + 112 → μ2.writable a = true := fun a h1 h2 => by
    rw [wr2]; exact hrS a h1 h2
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, q0, q1, q2, q3, fr3, rd3, wr3⟩ := sg_r2 (P := P) (R := R)
    x ω2 μ2 S (rdN μ2 (S + 56) 8) (rdN μ2 (S + 64) 8) (rdN μ2 (S + 72) 8) (rdN μ2 (S + 80) 8) (b1.trans a1) b7
    ⟨by omega, by omega⟩ (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) (readN_rdN ..) (readN_rdN ..)
    (readN_rdN ..) (readN_rdN ..) (fun a h1 h2 => hrS2 a (by omega) h2)
  have rp3 : rdN μ3 (S + 8) 8 = vptr + 32 := by
    rw [← rp2]; exact rdN_frame fun j hj => fr3 _ (by omega) (.inl (by omega))
  have rl3 : rdN μ3 (S + 8 + 8) 8 = w.length - 32 := by
    rw [← rl2]; exact rdN_frame fun j hj => fr3 _ (by omega) (.inl (by omega))
  have hrS3 : ∀ a, S - 88 ≤ a → a < S + 112 → μ3.writable a = true := fun a h1 h2 => by
    rw [wr3]; exact hrS2 a h1 h2
  have mS3 : μ3.readN S 8 = Num.encodeLE 8 vptr := by
    rw [← mS]; exact Memory.readN_congr fun j hj => by
      rw [fr3 _ (by omega) (.inl (by omega)), fr2 _ (by omega) (.inl (by omega)) (.inr (by omega)) (.inl (by omega))]
  have fr13 : ∀ a, a < 4294967296 → (a < S - 88 ∨ S + 88 ≤ a) → μ3.read a = μ.read a := fun a h0 ha => by
    rw [fr3 a h0 (by omega), fr2 a h0 (by omega) (by omega) (by omega), fr1 a h0 (by omega) (by omega)]
  have wr13 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [wr3, wr2, wr1]
  have rd13 : ∀ a, μ3.readable a = μ.readable a := fun a => by rw [rd3, rd2, rd1]
  by_cases hB : w.length < 34
  · -- a short second read
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, fr4, rd4, wr4⟩ := re_short (P := P) (R := R) x ω3 μ3 S (S + 8) 2
      (w.length - 32) 1606 34531 ⟨by omega, by omega⟩ c0 c1 c7 c9 (by decide) ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_802]) bs_34531 rl3 (by omega) (by omega) (.inr (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hrS3 a (by omega) (by omega)))
      (fun a h1 h2 => hrS3 a (by omega) (by omega))
    have mp4 : μ4.readN S 8 = Num.encodeLE 8 vptr := by
      rw [← mS3]; exact Memory.readN_congr fun j hj => fr4 _ (by omega) (.inr (by omega))
    obtain ⟨ω5, run5, e0, e1, e5, e6, e7⟩ := sg_shortD (P := P) (R := R) x ω4 μ4 34531 S out 1 w.length vptr
      (.inr rfl) (d1.trans c1) (d5.trans (c5.trans (b5.trans (a5.trans h5))))
      (d6.trans (c6.trans (b6.trans a6))) d7 (by decide) (by decide) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ mp4
      (fun a h1 h2 => by rw [rd4]; exact Memory.readable_of_writable (hrS3 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr4, wr13]; exact hst a (by omega) (by omega))
    refine fin ω5 _ _ ((((run1.trans run2).trans run3).trans run4).trans run5) e0 e1 e7
      (fun a h0 ha hb => ?_) (fun a => ?_) ?_
    · rw [rd_wr _ _ _ _ 2 l2 (by omega) (by omega) h0, fr4 a h0 (by omega), fr13 a h0 ha]
    · rw [Memory.writable_writeN, wr4, wr13]
    · rw [slotDec_short w hB]; unfold SlotOut
      exact Memory.readN_writeN_same _ _ _ _ l2 (by unfold two32; omega)
  -- the second read: 2 octets from vptr + 32 into S + 56
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, cp4, rp4, rl4, fr4, rd4, wr4⟩ := read_exact_text (P := P) (R := R)
    x ω3 μ3 S (S + 8) (S + 56) 2 (vptr + 32) (w.length - 32) 1606 34531 ⟨by omega, by omega, hS.2⟩ c0 c1 c7 c8 c9
    ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_802]) bs_34531 rp3 rl3
    (by omega) (.inr (by omega)) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega))
    (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd13]; exact hvr a (by omega) (by omega)) (fun a h1 h2 => hrS3 a (by omega) (by omega))
    (fun a h1 h2 => hrS3 a (by omega) (by omega)) (fun a h1 h2 => hrS3 a (by omega) (by omega))
  have h2l : ((w.drop 32).take 2).length = 2 := by simp; omega
  have hk : Num.decodeLE ((w.drop 32).take 2) < 65536 := by
    have := decodeLE_lt ((w.drop 32).take 2); rw [h2l] at this; simpa using this
  have mk : μ4.readN (S + 56) 2 = Num.encodeLE 2 (Num.decodeLE ((w.drop 32).take 2)) := by
    have e := encodeLE_decodeLE ((w.drop 32).take 2)
    rw [h2l] at e
    rw [e, cp4, Memory.readN_congr (μ := μ) (fun j hj => fr13 _ (by omega) (.inl (by omega)))]
    obtain ⟨m, hm⟩ : ∃ m, w.length = 32 + (2 + m) := ⟨w.length - 34, by omega⟩
    rw [← mw, hm, Decode.VecU8.readN_split, List.drop_left' (Memory.length_readN ..), Decode.VecU8.readN_split,
      List.take_left' (Memory.length_readN ..)]
  have kq : ∀ o, S + 24 ≤ o → o + 8 ≤ S + 56 → μ4.readN o 8 = μ3.readN o 8 := fun o h1 h2 =>
    Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega)) (.inr (by omega)) (.inr (by omega))
  have mp4 : μ4.readN S 8 = Num.encodeLE 8 vptr := by
    rw [← mS3]; exact Memory.readN_congr fun j hj => fr4 _ (by omega) (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
  obtain ⟨ω5, run5, e0, e1, e5, e6, e7⟩ := sg_okD (P := P) (R := R) x ω4 μ4 S out (rdN μ2 (S + 56) 8)
    (rdN μ2 (S + 64) 8) (rdN μ2 (S + 72) 8) (rdN μ2 (S + 80) 8) (Num.decodeLE ((w.drop 32).take 2)) w.length vptr
    (d1.trans c1) (d5.trans (c5.trans (b5.trans (a5.trans h5))))
    (d6.trans (c6.trans (b6.trans a6))) d7 (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) hk
    (by rw [kq _ (by omega) (by omega)]; exact q0) (by rw [kq _ (by omega) (by omega)]; exact q1)
    (by rw [kq _ (by omega) (by omega)]; exact q2) (by rw [kq _ (by omega) (by omega)]; exact q3) mk mp4
    (fun a h1 h2 => by rw [rd4]; exact Memory.readable_of_writable (hrS3 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr4, wr13]; exact hst a (by omega) (by omega))
  obtain ⟨o0, o1, o2⟩ := okMem_slot μ4 out (rdN μ2 (S + 56) 8) (rdN μ2 (S + 64) 8) (rdN μ2 (S + 72) 8)
    (rdN μ2 (S + 80) 8) _ (by omega) (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) (rdN_lt64 ..) hk
  refine fin ω5 _ _ ((((run1.trans run2).trans run3).trans run4).trans run5) e0 e1 e7
    (fun a h0 ha hb => ?_) (fun a => ?_) ?_
  · rw [okMem_read _ _ _ _ _ _ _ _ (by omega) h0 hb, fr4 a h0 (by omega) (by omega) (by omega), fr13 a h0 ha]
  · rw [okMem_writable, wr4, wr13]
  · rw [slotDec_long w (by omega)]; unfold SlotOut
    refine ⟨o0, ?_, o2⟩
    rw [o1, ← readN_rdN, ← readN_rdN, ← readN_rdN, ← readN_rdN, ← hw32,
      show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, Decode.VecU8.readN_split, Decode.VecU8.readN_split,
      Decode.VecU8.readN_split]
    simp only [List.append_assoc, show S + 56 + 8 = S + 64 by omega, show S + 64 + 8 = S + 72 by omega,
      show S + 72 + 8 = S + 80 by omega]

end Services.Bootstrap.Acc.Handlers.RecentSlot
