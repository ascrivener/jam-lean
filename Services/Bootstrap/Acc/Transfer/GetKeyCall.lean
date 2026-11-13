import Services.Bootstrap.Acc.Transfer.GetKey
import Services.Bootstrap.Acc.Wrappers.GetCall
import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.Decode.LoopAPass
import Services.Bootstrap.Acc.Inputs.LoopInd

/-!
# `get` of a copied 14-octet key, composed (40494 → 7237)

`gk_call`: from `alloc(14, 1)` at the helper's entry, the key "transfer-count" copied into a fresh
`Vec` (`extend_from_slice`), `get_call` on it, the copy freed (`dealloc_callG`), and the return to
7237; or an allocation failed (the `heap` abort: null at 3820, or `get`'s at 48047).

Helpers: `HKeepG.data` (the heap off the headers kept keeps every chunk's data), `GetOut.mono` and
`GetOut.base` (transporting `get`'s output), and the three returns' steps (`gk_j1`, `gk_j2`,
`gk_j3`). The key's octets in read-only data are carried through the allocation by `HeapHost.keepRO`.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- `alloc`'s return (40611) to 3820 (ω₀ = 102). -/
theorem gk_j1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 102) : FreeStepsH p R 40611 ω μ x 3820 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- `get`'s returns (47927, 47957, 48102) to 3865 (ω₀ = 106). -/
theorem gk_j2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (e : Nat) (he : e = 47927 ∨ e = 47957 ∨ e = 48102) (h0 : ω[0] = UInt64.ofNat 106) :
    FreeStepsH p R e ω μ x 3865 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl | rfl <;> pvm_go [h0]

/-- The helper's return (3893) to 7237 (ω₀ = 244). -/
theorem gk_j3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 244) : FreeStepsH p R 3893 ω μ x 7237 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

open Picoalloc in
/-- **The heap off the headers kept keeps every chunk's data**: a chunk's data lies off every
    chunk's 16-octet header (the chunks tile the heap). -/
theorem HKeepG.data {μ μ' : Memory} {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (h : HKeepG μ μ' (fun a => ∃ c ∈ chunks s, c.addr = a))
    {c : Chunk} (hc : c ∈ chunks s) {a : Nat} (ha : InDataA c a) : μ'.read a = μ.read a := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hm := ht.mem_lt c hc
  unfold InDataA at ha
  refine h a ⟨.inr (by omega), by omega, fun hh ⟨d, hd, hda⟩ => ?_⟩
  subst hda
  by_cases he : d = c
  · subst he; omega
  · have hmd := ht.mem_lt d hd
    rcases Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht c hc d hd (Ne.symm he) with h | h <;> omega

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall in
/-- `GetOut` survives a change of memory and state that keeps out's 24 octets, the value's octets and
    its chunk. -/
theorem GetOut.mono {μ μ' : Memory} {out : Nat} {s₀ s s' : State} {v : Option (List UInt8)}
    (h : GetOut μ out s₀ s v)
    (hout : ∀ a, out ≤ a → a < out + 24 → μ'.read a = μ.read a)
    (hdat : ∀ c ∈ chunks s, c.used = true → (∀ d ∈ chunks s₀, d.used = true → d ≠ c) →
      ∀ a, InDataA c a → μ'.read a = μ.read a)
    (hch : ∀ c ∈ chunks s, c.used = true → (∀ d ∈ chunks s₀, d.used = true → d ≠ c) → c ∈ chunks s') :
    GetOut μ' out s₀ s' v := by
  have rN : ∀ o, out ≤ o → o + 8 ≤ out + 24 → μ'.readN o 8 = μ.readN o 8 := fun o h1 h2 =>
    PVM.Memory.readN_congr fun j hj => hout _ (by omega) (by omega)
  match v, h with
  | none, h => unfold GetOut at h ⊢; rw [rN out (by omega) (by omega)]; exact h
  | some [], h =>
    unfold GetOut at h ⊢
    obtain ⟨a, b, c⟩ := h
    exact ⟨by rw [rN out (by omega) (by omega)]; exact a, by rw [rN (out + 8) (by omega) (by omega)]; exact b,
      by rw [rN (out + 16) (by omega) (by omega)]; exact c⟩
  | some (b :: w), h =>
    unfold GetOut at h ⊢
    obtain ⟨ptr, o0, o8, o16, od, hc, h32, hfr⟩ := h
    refine ⟨ptr, by rw [rN out (by omega) (by omega)]; exact o0, by rw [rN (out + 8) (by omega) (by omega)]; exact o8,
      by rw [rN (out + 16) (by omega) (by omega)]; exact o16, ?_, hch _ hc rfl hfr, h32, hfr⟩
    have e : μ'.readN ptr (b :: w).length = μ.readN ptr (b :: w).length :=
      PVM.Memory.readN_congr fun j hj => hdat _ hc rfl hfr _ ⟨by dsimp only; omega, by dsimp only; omega⟩
    rw [e]; exact od

open Picoalloc in
/-- `GetOut`'s freshness against a later state gives it against an earlier one. -/
theorem GetOut.base {μ : Memory} {out : Nat} {s₀ s₁ s : State} {v : Option (List UInt8)}
    (hk : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s₁) (h : GetOut μ out s₁ s v) : GetOut μ out s₀ s v := by
  match v, h with
  | none, h => exact h
  | some [], h => exact h
  | some (b :: w), h =>
    obtain ⟨ptr, o0, o8, o16, od, hc, h32, hfr⟩ := h
    exact ⟨ptr, o0, o8, o16, od, hc, h32, fun d hd hu => hfr d (hk d hd hu) hu⟩

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall in
/-- **The helper `get` of a copied 14-octet key, 40494 → 7237**: from `alloc(14, 1)` with the helper's
    frame at s (out at s, return 244 at s + 48, ω₅ / ω₆ at s + 40 / + 32) and the key's 14 octets at
    65956: either the key is copied into a fresh `Vec`, `get` stores `GetOut` at out for the key's value
    v, the copy is freed, and the run returns to 7237 with ω₁ = s + 56, ω₅, ω₆ restored, the
    allocator's context for a state keeping every allocated chunk and its data, and the stack above
    the frame kept off out; or an allocation failed: `alloc` returned null at 3820, or `get`'s at 48047, and the
    run reaches a trap. The context and the stream are kept. -/
theorem gk_call (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) {hb : Nat} (s₀ : State) (s out r5 r6 S0 S1 : Nat)
    (key : List UInt8) (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h0 : ω[0] = UInt64.ofNat 102) (h1 : ω[1] = UInt64.ofNat s) (h7 : ω[7] = UInt64.ofNat 14)
    (h8 : ω[8] = UInt64.ofNat 1) (h5 : ω[5] = UInt64.ofNat 14) (h6 : ω[6] = UInt64.ofNat 65956)
    (hs : 2147483800 + 128 ≤ s ∧ s % 8 = 0) (hSTk : S0 + 300 ≤ s ∧ s + 56 ≤ S1)
    (hout : s + 56 ≤ out ∧ out + 24 ≤ S1)
    (m0 : μ.readN s 8 = Num.encodeLE 8 out) (m48 : μ.readN (s + 48) 8 = Num.encodeLE 8 244)
    (m40 : μ.readN (s + 40) 8 = Num.encodeLE 8 r5) (m32 : μ.readN (s + 32) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hkey : μ.readN 65956 14 = key) (hkr : ∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true)
    (hfit : ∀ w, c.1.self.storage.get? key = some w → w.length + 31 < 68719476736) :
    (∃ s' ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 40494 ω μ (c, f) 7237 ω' μ' (c, f) n ∧
      ω'[1] = UInt64.ofNat (s + 56) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      GetOut μ' out s₀ s' (c.1.self.storage.get? key) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s₀, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → s + 56 ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ e ω' μ' n, (e = 3820 ∨ e = 48047) ∧ FreeStepsH p (KeepCtx (accContractS env)) 40494 ω μ (c, f) e ω' μ' (c, f) n ∧
      ω'[7] = UInt64.ofNat 0 ∧ ∃ t ω'' μ'' m, (t = 3895 ∨ t = 47977) ∧
        FreeStepsH p (KeepCtx (accContractS env)) e ω' μ' (c, f) t ω'' μ'' (c, f) m) := by
  have hst := H.st
  have hS1 := H.hS1
  rcases alloc_callG (p := p) (P := P) (hb := hb) (accHeapHost env) cap hcap1 hcap c ω μ s₀ s 14 1 pb S0 S1 H
      h1 h7 h8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
    ⟨ptr, s1, ω1, μ1, -, run1, H1, keep1, hnew, hfresh, hkg, e7, stk1, f0, f1, f5, f6⟩ |
    ⟨-, ω1, μ1, run1, e7, stk1, f0, f1, f5, f6⟩
  · obtain ⟨-, run1S⟩ := FreeStepsH.growS f run1
    have kro := HeapHost.keepRO (env := accHeapHost env) H.bd run1
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0 := H1.hb0
    have hbT := H1.hbT
    have hst1 := H1.st
    -- read-only data: the key's octets and their readability are kept by the allocation
    have keyR1 : ∀ a, 65956 ≤ a → a < 65970 → μ1.read a = μ.read a := fun a h1 h2 =>
      kro.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a (by omega))
    have keyRd1 : ∀ a, 65956 ≤ a → a < 65970 → μ1.readable a = true := fun a h1 h2 => by
      have hp := kro.1 (a / pageSize) (.inl (by unfold pageSize; omega))
      have := hkr a h1 h2
      unfold Memory.readable at this ⊢; rw [hp]; exact this
    -- 40611 → 3820 → 58508
    have run1' := run1S.trans (gk_j1 (p := p) (P := P) _ ω1 μ1 (f0.trans h0))
    obtain ⟨ω2, μ2, run2, a0, a1, a7, a8, a9, a5, a6, v8, v16, v24, fr2, rd2, wr2⟩ :=
      gk_vec (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω1 μ1 s ptr (f1.trans h1) (f5.trans h5) e7
        (by omega) (by omega) ⟨by omega, by omega⟩ (fun a h1 h2 => hst1 a (by omega) (by omega))
    -- 58508 → 3846: the key copied
    obtain ⟨ω3, μ3, run3, b0, b1, b5, b6, dat, len, frm, rd3, wr3⟩ :=
      Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 s (s + 8) 65956 14 14 ptr 0 104 3846
        ⟨by omega, by omega, hs.2⟩ a0 a1 a7 (a8.trans (f6.trans h6)) a9 (by omega) (by decide) v8 v16 v24 (by omega)
        (.inr (by omega)) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ (.inr (by omega)) (.inr (by omega))
        (.inr (by omega)) (.inr (by omega)) ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_51]) bs_3846
        (fun a h1 h2 => by rw [rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [rd2]; exact keyRd1 a h1 h2)
        (fun a h1 h2 => by rw [wr2]; exact heapC_writable_data H1 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
    -- the memory at 3846
    have keep13 : ∀ a, a < 4294967296 → s ≤ a → (a < s + 8 ∨ s + 32 ≤ a) → μ3.read a = μ.read a := fun a h0 ha hb => by
      rw [frm a h0 (.inr ha) (.inr (by omega)) (by omega), fr2 a h0 hb, stk1 a h0 ha]
    have rN3 : ∀ o, s ≤ o → o + 8 ≤ s + 56 → (o + 8 ≤ s + 8 ∨ s + 32 ≤ o) → μ3.readN o 8 = μ.readN o 8 :=
      fun o h1 h2 h3 => PVM.Memory.readN_congr fun j hj => keep13 _ (by omega) (by omega) (by omega)
    have k23 : ∀ o, s + 8 ≤ o → o + 8 ≤ s + 24 → μ3.readN o 8 = μ2.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => frm _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))
    have hrf3 : ∀ a, s ≤ a → a < s + 56 → μ3.readable a = true := fun a h1 h2 => by
      rw [rd3, rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega))
    obtain ⟨ω4, run4, c0, c1, c7, c8, c9, c6, c5⟩ :=
      gk_get (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω3 μ3 s out 14 ptr 14 b1 ⟨by omega, by omega⟩
        hrf3 (by rw [rN3 s (by omega) (by omega) (.inl (by omega))]; exact m0)
        (by rw [k23 _ (by omega) (by omega)]; exact v8) (by rw [k23 _ (by omega) (by omega)]; exact v16)
        (by rw [show s + 24 = s + 8 + 16 by omega]; exact len) (by omega) (by decide) (by omega) (by decide)
    -- the heap context at 3846: stack writes, then the key's chunk
    have H2 : HeapCtxC env.code pb S0 S1 μ2 s1 :=
      Services.Bootstrap.Acc.HeapCtxC.keep_hi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
    have H3 : HeapCtxC env.code pb S0 S1 μ3 s1 :=
      Services.Bootstrap.Acc.HeapCtxC.keep_data H2 hnew (fun a ha hc => frm a (by omega) (.inl (by omega))
        (by dsimp only at hc; omega) (.inl (by omega))) wr3
    have hkey3 : μ3.readN ptr 14 = key := by
      rw [← hkey, show ptr = ptr + 0 from rfl, dat]
      exact PVM.Memory.readN_congr fun j hj => by rw [fr2 _ (by omega) (.inl (by omega)), keyR1 _ (by omega) (by omega)]
    have runA := (((run1'.trans run2).trans run3).trans run4)
    -- 47857: get
    rcases get_call (p := p) (P := P) (hb := hb) env cap pb hcap1 hcap c f ω4 μ3 s1 s out ptr 14 S0 S1 key H3
        c1 c7 c8 c9 (by decide) (by omega) (by omega) ⟨by omega, hout.2⟩
        (.inr ⟨_, hnew, rfl, fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩⟩) (by omega) hkey3 hfit with
      ⟨e, s3, ω5, μ5, n5, he, run5, g0, g1, g5, g6, gout, H5, keep5, keepd5, fr5⟩ |
      ⟨ω5, μ5, n5, run5, e7', ω'', μ'', run''⟩
    · -- 3865: the copy freed
      have run5' := run5.trans (gk_j2 (p := p) (P := P) _ ω5 μ5 e he (g0.trans c0))
      obtain ⟨ω6, run6, d0, d7, d1⟩ := gk_free (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω5 μ5 14 ptr
        (g5.trans c5) (g6.trans c6) (by decide) (by decide) (by omega)
      have hk5 := keep5 _ hnew rfl
      obtain ⟨ω7, μ7, run7, H7, -, -, -, stk7, -, oth7, -, b1', -, -⟩ :=
        dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ω6 μ5 s3 s ptr
          108 3881 _ H5 hk5 rfl (by dsimp only; omega) d0 (d1.trans g1) d7 ⟨by decide, by decide, by decide⟩
          (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_53]) bs_3881 (by omega) ⟨by omega, by omega⟩
      -- the frame words, from the entry
      have kF : ∀ o, s + 32 ≤ o → o + 8 ≤ s + 56 → μ7.readN o 8 = μ.readN o 8 := fun o h1 h2 =>
        PVM.Memory.readN_congr fun j hj => by
          rw [stk7 _ (by omega) (by omega), fr5 _ (by omega) (by omega) (.inl (by omega)),
            keep13 _ (by omega) (by omega) (.inr (by omega))]
      have hrf7 : ∀ a, s ≤ a → a < s + 56 → μ7.readable a = true := fun a h1 h2 =>
        Memory.readable_of_writable (H7.st a (by omega) (by omega))
      obtain ⟨ω8, run8, i0, i5, i6, i1, -⟩ := gk_ret (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω7 μ7 s
        244 r5 r6 (b1'.trans (d1.trans g1)) ⟨by omega, by omega⟩ hrf7
        (by rw [kF _ (by omega) (by omega)]; exact m48) (by rw [kF _ (by omega) (by omega)]; exact m40)
        (by rw [kF _ (by omega) (by omega)]; exact m32) (by decide) hr5 hr6
      have run9 := gk_j3 (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω8 μ7 i0
      -- chunks other than the key's copy
      have hfr1 : ∀ d ∈ chunks s₀, d.used = true → d ≠ (⟨ptr - 32, (14 + 31) / 32 + 1, true⟩ : Chunk) := hfresh
      refine .inl ⟨Picoalloc.free s3 ptr, ω8, μ7, _,
        (((runA.trans run5').trans run6).trans run7).trans (run8.trans run9), i1, i5, i6, ?_, H7, ?_, ?_, ?_⟩
      · refine GetOut.base (fun d hd hu => keep1 d hd hu) (GetOut.mono gout ?_ ?_ ?_)
        · intro a h1 h2; exact stk7 a (by omega) (by omega)
        · intro d hd hu hf a ha
          have hne : d ≠ ⟨ptr - 32, (14 + 31) / 32 + 1, true⟩ := fun e => hf _ hnew rfl e.symm
          exact (oth7 d hd hu hne).2 a ha
        · intro d hd hu hf
          have hne : d ≠ ⟨ptr - 32, (14 + 31) / 32 + 1, true⟩ := fun e => hf _ hnew rfl e.symm
          exact (oth7 d hd hu hne).1
      · intro d hd hu
        exact (oth7 d (keep5 d (keep1 d hd hu) hu) hu (hfr1 d hd hu)).1
      · intro d hd hu a ha
        have hd1 := keep1 d hd hu
        have hne := hfr1 d hd hu
        rw [(oth7 d (keep5 d hd1 hu) hu hne).2 a ha, keepd5 d hd1 hu a ha]
        have hap := Services.Bootstrap.Decode.LoopA.InData.apart H1.wf hd1 hnew (Ne.symm hne) ha
        unfold Services.Bootstrap.Decode.LoopA.InData at hap
        dsimp only at hap
        have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hd1 hu
        unfold InDataA at ha
        rw [frm a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)), fr2 a (by omega) (.inl (by omega))]
        exact HKeepG.data H1.wf H1.hb0 H1.hbT hkg hd1 ha
      · intro a h0 ha ho
        rw [stk7 a h0 (by omega), fr5 a h0 (by omega) ho]
        exact keep13 a h0 (by omega) (.inr (by omega))
    · exact .inr ⟨48047, ω5, μ5, _, .inr rfl, runA.trans run5, e7', 47977, ω'', μ'', _, .inr rfl, run''⟩
  · obtain ⟨-, run1S⟩ := FreeStepsH.growS f run1
    refine .inr ⟨3820, ω1, μ1, _, .inl rfl, run1S.trans (gk_j1 (p := p) (P := P) _ ω1 μ1 (f0.trans h0)), e7,
      3895, ω1, μ1, _, .inl rfl, gk_null (p := p) (P := P) _ ω1 μ1 e7⟩

end Services.Bootstrap.Acc
