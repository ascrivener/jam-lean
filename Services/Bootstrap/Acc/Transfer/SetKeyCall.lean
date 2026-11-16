import Services.Bootstrap.Acc.Transfer.SetKey
import Services.Bootstrap.Acc.Transfer.GetKeyCall
import Services.Bootstrap.Acc.Wrappers.SetCall

/-!
# `set` of a copied 14-octet key, composed (40494 → 7386)

`sk_call`: from `alloc(14, 1)` at the helper's entry, the key "transfer-count" copied into a fresh
`Vec` (`extend_from_slice`), `set_call` of (key, value) on it, the copy freed (`dealloc_callG`), and
the return to 7386 with ω₇ = 2⁶⁴ − 1 (`Ok`) or 3 (`Err(FULL)`); or `alloc` returned null (the `heap`
abort, the trap at 4002). The run is under `YIn` with y kept: the allocator's and the frees' steps
keep the context (`FreeStepsH.keepY`), `set`'s is Ω_W on x.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- A run whose steps keep the context, from a context with y = a, is a run whose steps leave y ∈ {a, b}. -/
theorem _root_.PVM.FreeStepsH.keepY {Qu : Type} {p : ByteArray} {R : HostRel (AccCtx × Qu)} (a b : Implications)
    {i ω μ x i' ω' μ' x' n} (h : FreeStepsH p (KeepCtx R) i ω μ x i' ω' μ' x' n) (hx : x.1.2 = a) :
    FreeStepsH p (YIn R a b) i ω μ x i' ω' μ' x' n := by
  induction h with
  | refl => exact .refl
  | pad _ ih => exact .pad (ih hx)
  | next hn hc _ ih => exact .next hn hc (ih hx)
  | host hd hb hs hr _ ih =>
    exact .host hd hb hs ⟨hr.1, .inl (by rw [hr.2]; exact hx)⟩ (ih (by rw [hr.2]; exact hx))

/-- `alloc`'s return (40611) to 3896 (ω₀ = 110). -/
theorem sk_j1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 110) : FreeStepsH p R 40611 ω μ x 3896 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- `set`'s returns (48158, 48250, 48235) to 3947 (ω₀ = 114). -/
theorem sk_j2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (e : Nat) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 114) :
    FreeStepsH p R e ω μ x 3947 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl | rfl <;> pvm_go [h0]

/-- The helper's return (4000) to 7386 (ω₀ = 250). -/
theorem sk_j3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 250) : FreeStepsH p R 4000 ω μ x 7386 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- `set`'s reply at out, as the helper reads it back: the word w at out and the octet b at out + 8
    give `if w = 2⁶⁴ − 1 then b else 2⁶⁴ − 1`, which is 3 for FULL and 2⁶⁴ − 1 otherwise. -/
theorem sk_res {μ : Memory} {out r : Nat} (h : SetOut μ out r) :
    (if rdN μ out 8 = 18446744073709551615 then rdN μ (out + 8) 1 else 18446744073709551615) =
      (if r = Result.FULL then 3 else 18446744073709551615) := by
  unfold SetOut at h
  by_cases hF : r = Result.FULL
  · rw [if_pos hF] at h; rw [if_pos hF]
    simp only [rdN, h.1, h.2, Num.decodeLE_encodeLE, Nat.reduceMod, ↓reduceIte]; rfl
  · rw [if_neg hF] at h; rw [if_neg hF]
    by_cases hN : r = Result.NONE
    · rw [if_pos hN] at h; simp only [rdN, h, Num.decodeLE_encodeLE, Nat.reduceMod]; rfl
    · rw [if_neg hN] at h; simp only [rdN, h.1, Num.decodeLE_encodeLE, Nat.reduceMod]; rfl

/-- A word stored by `encodeLE`, read back. -/
theorem rdN_of_readN {μ : Memory} {a v : Nat} (h : μ.readN a 8 = Num.encodeLE 8 v)
    (hv : v < 18446744073709551616) : rdN μ a 8 = v := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hv

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall in
/-- **The helper `set` of a copied 14-octet key, 40494 → 7386**: from `alloc(14, 1)` with the
    helper's frame at s (the value's address vO at s, its length 4 at s + 8, return 250 at s + 56,
    ω₅ / ω₆ at s + 48 / + 40) and the key's 14 octets at 65956: either the key is copied into a fresh
    `Vec`, `set` does Ω_W of (key, value) with value the 4 octets at vO (x's account becomes
    `writeSelf`), the copy is freed, and the run returns to 7386 with ω₇ = 3 if Ω_W replied FULL and
    2⁶⁴ − 1 otherwise, ω₁ = s + 64, ω₅, ω₆ restored, the allocator's context for a state keeping
    every allocated chunk and its data, and the stack above the frame kept; or `alloc` returned null
    (3896) and the run reaches the trap at 4002. y and the stream are kept. -/
theorem sk_call (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) {hb : Nat} (s₀ : State) (s vO r5 r6 S0 S1 : Nat)
    (key value : List UInt8) (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h0 : ω[0] = UInt64.ofNat 110) (h1 : ω[1] = UInt64.ofNat s) (h7 : ω[7] = UInt64.ofNat 14)
    (h8 : ω[8] = UInt64.ofNat 1) (h5 : ω[5] = UInt64.ofNat 65956) (h6 : ω[6] = UInt64.ofNat 14)
    (hs : 2147483800 + 128 ≤ s ∧ s % 8 = 0) (hSTk : S0 + 300 ≤ s ∧ s + 64 ≤ S1)
    (hv : s + 64 ≤ vO ∧ vO + 4 ≤ S1)
    (m0 : μ.readN s 8 = Num.encodeLE 8 vO) (m8 : μ.readN (s + 8) 8 = Num.encodeLE 8 4)
    (m56 : μ.readN (s + 56) 8 = Num.encodeLE 8 250)
    (m48 : μ.readN (s + 48) 8 = Num.encodeLE 8 r5) (m40 : μ.readN (s + 40) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hkey : μ.readN 65956 14 = key) (hkr : ∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true)
    (hval : μ.readN vO 4 = value)
    (ht8 : rdN μ 69072 4 = 4294900408) (ht4 : rdN μ 69056 4 = 4294900402)
    (htr : ∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)
    (hold : ∀ v, c.1.self.storage.get? key = some v → v.length < 2 ^ 63) :
    (∃ s' ω' μ' n, FreeStepsH p (YIn (accContractS env) c.2 c.2) 40494 ω μ (c, f) 7386 ω' μ'
        ((c.1.setSelf (writeSelf c.1.self key value), c.2), f) n ∧
      ω'[7] = UInt64.ofNat (if writeR7 c.1.self key value = Result.FULL then 3 else 18446744073709551615) ∧
      ω'[1] = UInt64.ofNat (s + 64) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s₀, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → s + 64 ≤ a → μ'.read a = μ.read a)) ∨
    (∃ ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 40494 ω μ (c, f) 3896 ω' μ' (c, f) n ∧
      ω'[7] = UInt64.ofNat 0 ∧
      FreeStepsH p (KeepCtx (accContractS env)) 3896 ω' μ' (c, f) 4002 ω' μ' (c, f) 1) := by
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
    -- read-only data (the key, the error table) kept by the allocation
    have roR1 : ∀ a, 65956 ≤ a → a < 69076 → μ1.read a = μ.read a := fun a h1 h2 =>
      kro.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H.ro a (by omega))
    have roRd1 : ∀ a, 65956 ≤ a → a < 69076 → μ1.readable a = μ.readable a := fun a h1 h2 => by
      have hp := kro.1 (a / pageSize) (.inl (by unfold pageSize; omega))
      unfold Memory.readable; rw [hp]
    -- 40611 → 3896 → 58508
    have run1' := run1S.trans (sk_j1 (p := p) (P := P) _ ω1 μ1 (f0.trans h0))
    obtain ⟨ω2, μ2, run2, a0, a1, a7, a8, a9, a5, a6, v16, v24, v32, fr2, rd2, wr2⟩ :=
      sk_vec (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω1 μ1 s ptr (f1.trans h1) (f6.trans h6) e7
        (by omega) (by omega) ⟨by omega, by omega⟩ (fun a h1 h2 => hst1 a (by omega) (by omega))
    -- 58508 → 3922: the key copied
    obtain ⟨ω3, μ3, run3, b0, b1, b5, b6, dat, len, frm, rd3, wr3⟩ :=
      Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 s (s + 16) 65956 14 14 ptr 0 112 3922
        ⟨by omega, by omega, hs.2⟩ a0 a1 a7 (a8.trans (f5.trans h5)) a9 (by omega) (by decide) v16 v24 v32 (by omega)
        (.inr (by omega)) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ (.inr (by omega)) (.inr (by omega))
        (.inr (by omega)) (.inr (by omega)) ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_55]) bs_3922
        (fun a h1 h2 => by rw [rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [rd2, roRd1 a h1 (by omega)]; exact hkr a h1 h2)
        (fun a h1 h2 => by rw [wr2]; exact heapC_writable_data H1 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
        (fun a h1 h2 => by rw [wr2]; exact hst1 a (by omega) (by omega))
    -- the memory at 3922
    have keep13 : ∀ a, a < 4294967296 → s ≤ a → (a < s + 16 ∨ s + 40 ≤ a) → μ3.read a = μ.read a := fun a h0 ha hb => by
      rw [frm a h0 (.inr ha) (.inr (by omega)) (by omega), fr2 a h0 hb, stk1 a h0 ha]
    have lo13 : ∀ a, 65956 ≤ a → a < 69076 → μ3.read a = μ.read a := fun a h1 h2 => by
      rw [frm a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)), fr2 a (by omega) (.inl (by omega)),
        roR1 a h1 h2]
    have rd13 : ∀ a, 65956 ≤ a → a < 69076 → μ3.readable a = μ.readable a := fun a h1 h2 => by
      rw [rd3, rd2, roRd1 a h1 h2]
    have rN3 : ∀ o, s ≤ o → o + 8 ≤ s + 64 → (o + 8 ≤ s + 16 ∨ s + 40 ≤ o) → μ3.readN o 8 = μ.readN o 8 :=
      fun o h1 h2 h3 => PVM.Memory.readN_congr fun j hj => keep13 _ (by omega) (by omega) (by omega)
    have k23 : ∀ o, s + 16 ≤ o → o + 8 ≤ s + 32 → μ3.readN o 8 = μ2.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => frm _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inl (by omega))
    have hrf3 : ∀ a, s ≤ a → a < s + 64 → μ3.readable a = true := fun a h1 h2 => by
      rw [rd3, rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega))
    have hvO : vO < 18446744073709551616 := by omega
    obtain ⟨ω4, run4, c0, c1, c7, c8, c9, c10, c11, c5, c6⟩ :=
      sk_set (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω3 μ3 s 14 ptr 14 vO 4 b1 ⟨by omega, by omega⟩
        hrf3 (by rw [rdN, rN3 s (by omega) (by omega) (.inl (by omega)), m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hvO)
        (by rw [rdN, rN3 (s + 8) (by omega) (by omega) (.inl (by omega)), m8, Num.decodeLE_encodeLE])
        (by rw [rdN, k23 _ (by omega) (by omega), v16, Num.decodeLE_encodeLE])
        (by rw [rdN, k23 _ (by omega) (by omega), v24, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))
        (by rw [rdN, show s + 32 = s + 16 + 16 by omega, len, Num.decodeLE_encodeLE])
    -- the heap context at 3922: stack writes, then the key's chunk
    have H2 : HeapCtxC env.code pb S0 S1 μ2 s1 :=
      Services.Bootstrap.Acc.HeapCtxC.keep_hi H1 (fun a ha => fr2 a (by omega) (.inl (by omega))) wr2
    have H3 : HeapCtxC env.code pb S0 S1 μ3 s1 :=
      Services.Bootstrap.Acc.HeapCtxC.keep_data H2 hnew (fun a ha hc => frm a (by omega) (.inl (by omega))
        (by dsimp only at hc; omega) (.inl (by omega))) wr3
    have hkey3 : μ3.readN ptr 14 = key := by
      rw [← hkey, show ptr = ptr + 0 from rfl, dat]
      exact PVM.Memory.readN_congr fun j hj => by rw [fr2 _ (by omega) (.inl (by omega)), roR1 _ (by omega) (by omega)]
    have hval3 : μ3.readN vO 4 = value := by
      rw [← hval]; exact PVM.Memory.readN_congr fun j hj => keep13 _ (by omega) (by omega) (.inr (by omega))
    have ht83 : rdN μ3 69072 4 = 4294900408 := by
      rw [← ht8]; unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => lo13 _ (by omega) (by omega)
    have ht43 : rdN μ3 69056 4 = 4294900402 := by
      rw [← ht4]; unfold rdN; congr 1; exact PVM.Memory.readN_congr fun j hj => lo13 _ (by omega) (by omega)
    have runA := ((run1'.trans run2).trans run3).trans run4
    -- 48104: set
    obtain ⟨e, ω5, μ5, he, run5, g0, g1, g5, g6, gout, fr5, rd5, wr5⟩ :=
      set_call (p := p) (P := P) env c f ω4 μ3 s (s + 16) ptr 14 vO 4 key value c1 c7 c8 c9 c10 c11
        (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (fun a h1 h2 => by rw [wr3, wr2]; exact hst1 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr3, wr2]; exact hst1 a (by omega) (by omega)) (.inr (by omega))
        (Services.Witness.rangeReadable_of (fun a h1 h2 => by
          rw [rd3, rd2]; exact Memory.readable_of_writable
            (heapC_writable_data H1 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)) (by omega))
        hkey3
        (Services.Witness.rangeReadable_of (fun a h1 h2 => by
          rw [rd3, rd2]; exact Memory.readable_of_writable (hst1 a (by omega) (by omega))) (by omega))
        hval3 (by rw [← hval, Memory.length_readN]) (.inl (by omega)) (.inr (by omega)) ht83 ht43
        (fun a h1 h2 => by rw [rd13 a (by omega) (by omega)]; exact htr a h1 h2) (by omega) hold
    -- the context after set; the rest keeps it
    generalize hc' : ((c.1.setSelf (writeSelf c.1.self key value), c.2) : AccCtx) = c' at run5
    have hc2 : c'.2 = c.2 := by rw [← hc']
    have run5' := run5.trans ((sk_j2 (p := p) (P := P) _ ω5 μ5 e he (g0.trans c0)).keepY c.2 c.2 hc2)
    -- 3947: the result word saved, the copy freed
    have hwf5 : ∀ a, s ≤ a → a < s + 64 → μ5.writable a = true := fun a h1 h2 => by
      rw [wr5, wr3, wr2]; exact hst1 a (by omega) (by omega)
    obtain ⟨ω6, μ6, run6, d0, d1, d7, d8, d9, d5, dw, fr6, rd6, wr6⟩ :=
      sk_free (p := p) (P := P) (R := KeepCtx (accContractS env)) (c', f) ω5 μ5 s 14 ptr (g1)
        (g5.trans c5) (g6.trans c6) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ hwf5
    have H6 : HeapCtxC env.code pb S0 S1 μ6 s1 :=
      Services.Bootstrap.Acc.HeapCtxC.keep_hi
        (Services.Bootstrap.Acc.HeapCtxC.keep_hi H3 (fun a ha => fr5 a (by omega) (.inl (by omega)) (.inl (by omega))) wr5)
        (fun a ha => fr6 a (by omega) (.inl (by omega))) wr6
    obtain ⟨ω7, μ7, run7, H7, -, -, -, stk7, -, oth7, -, b1', b5', -⟩ :=
      dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c', f) ω6 μ6 s1 s ptr
        116 3972 _ H6 hnew rfl (by dsimp only; omega) d0 d1 d7 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_57]) bs_3972 (by omega) ⟨by omega, by omega⟩
    have hrf7 : ∀ a, s ≤ a → a < s + 64 → μ7.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (H7.st a (by omega) (by omega))
    obtain ⟨ω8, run8, k7, k1, k5⟩ := sk_back (p := p) (P := P) (R := KeepCtx (accContractS env)) (c', f) ω7 μ7 s
      (b1'.trans d1) ⟨by omega, by omega⟩ hrf7
    -- the frame words, from the entry
    have kF : ∀ o, s + 40 ≤ o → o + 8 ≤ s + 64 → μ7.readN o 8 = μ.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => by
        rw [stk7 _ (by omega) (by omega), fr6 _ (by omega) (.inr (by omega)),
          fr5 _ (by omega) (.inr (by omega)) (.inr (by omega)), keep13 _ (by omega) (by omega) (.inr (by omega))]
    have hw7 : rdN μ7 (s + 8) 8 = rdN μ5 (s + 16) 8 := by
      rw [← dw]; unfold rdN; congr 1
      exact PVM.Memory.readN_congr fun j hj => stk7 _ (by omega) (by omega)
    obtain ⟨ω9, run9, i7, i0, i5, i6, i1⟩ := sk_ret (p := p) (P := P) (R := KeepCtx (accContractS env)) (c', f) ω8 μ7 s
      (rdN μ7 (s + 8) 8) (rdN μ5 (s + 24) 1) 250 r5 r6 k1 k7 (k5.trans (b5'.trans d5)) (rdN_lt64 _ _)
      (Nat.lt_of_lt_of_le (rdN_lt _ _ 1) (by decide)) ⟨by omega, by omega⟩ hrf7
      (by rw [rdN, kF _ (by omega) (by omega), m56, Num.decodeLE_encodeLE])
      (by rw [rdN, kF _ (by omega) (by omega), m48, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5)
      (by rw [rdN, kF _ (by omega) (by omega), m40, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr6)
    have run10 := sk_j3 (p := p) (P := P) (R := KeepCtx (accContractS env)) (c', f) ω9 μ7 i0
    have runB := (((run6.trans run7).trans run8).trans run9).trans run10
    have hfr1 : ∀ d ∈ chunks s₀, d.used = true → d ≠ (⟨ptr - 32, (14 + 31) / 32 + 1, true⟩ : Chunk) := hfresh
    subst hc'
    refine .inl ⟨Picoalloc.free s1 ptr, ω9, μ7, _,
      ((runA.keepY c.2 c.2 rfl).trans run5').trans (runB.keepY c.2 c.2 rfl), ?_, i1, i5, i6, H7, ?_, ?_, ?_⟩
    · rw [i7, hw7, show s + 24 = s + 16 + 8 by omega, sk_res gout]
    · intro d hd hu
      exact (oth7 d (keep1 d hd hu) hu (hfr1 d hd hu)).1
    · intro d hd hu a ha
      have hd1 := keep1 d hd hu
      have hne := hfr1 d hd hu
      have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hd1 hu
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H1.wf hd1 hnew (Ne.symm hne) ha
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      dsimp only at hap
      unfold InDataA at ha
      rw [(oth7 d hd1 hu hne).2 a ha, fr6 a (by omega) (.inl (by omega)),
        fr5 a (by omega) (.inl (by omega)) (.inl (by omega)),
        frm a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)), fr2 a (by omega) (.inl (by omega))]
      exact HKeepG.data H1.wf H1.hb0 H1.hbT hkg hd1 ha
    · intro a h0 ha
      rw [stk7 a h0 (by omega), fr6 a h0 (.inr (by omega)), fr5 a h0 (.inr (by omega)) (.inr (by omega))]
      exact keep13 a h0 (by omega) (.inr (by omega))
  · obtain ⟨-, run1S⟩ := FreeStepsH.growS f run1
    exact .inr ⟨ω1, μ1, _, run1S.trans (sk_j1 (p := p) (P := P) _ ω1 μ1 (f0.trans h0)), e7,
      sk_null (p := p) (P := P) _ ω1 μ1 e7⟩

end Services.Bootstrap.Acc
