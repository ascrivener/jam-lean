import Services.Bootstrap.Refine.DecodeVec2
import Services.Bootstrap.Refine.DecodeVecC
import Services.Bootstrap.Decode.ReallocCall

/-!
# `Vec<Instruction>::decode`, two batches, the slots' chunks seen

`vec_twoC` is `DecodeVecC.vec_oneC` for 70 < n < 128 instructions: the first batch of 70 (`vec_preG`, the element
loop `loopAFCd_lowF` at d = 0), its end (`w1`), `finish_grow` on the old buffer (`g3x`), `realloc` to n slots
(`ReallocCall.realloc_call`; the first 70 slots copied), back into the element loop (`v2g`), the second batch of
n − 70 (`loopAFCd_lowF` at d = 70) and the return (`v3a`, `v3b`). The slots' chunks of the two batches are disjoint:
the second batch's are fresh against the heap at its start, where the first batch's are allocated. GP v0.8.0
Appendix B.4; `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVec2C

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop Services.Bootstrap.Refine.DecodeVec

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- **`Vec<Instruction>::decode`, two batches, the slots' chunks seen** (482 … 20420): as `vec_oneC`, for
    70 < n < 128 instructions: the output `{n, r, n}` at S + 552 (the n slots in the chunk the `realloc` returned),
    element j satisfying `reps j` with the chunks it allocated (pairwise disjoint, none the buffer's or the
    payload's), the reader past the instructions, the allocator's context for a heap s' keeping every allocated
    chunk of s with its data. Or an allocation fails. -/
theorem vec_twoC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat} (gl : Nat → UInt8)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (S rd P0 Lt v5 v6 : Nat) (es : List (List UInt8)) (reps : Nat → List Chunk → List UInt8 → Memory → Prop)
    (cp : Chunk) (Ns : Nat → Nat)
    (hel : ∀ j (hj : j < es.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd (Ns j) es[j] (reps j))
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (hn : 70 < es.length ∧ es.length < 128) (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hS : S0 + 2104 ≤ S ∧ S + 552 + 24 ≤ rd ∧ rd + 16 ≤ S1 ∧ S % 8 = 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base)
    (hcpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a) (hP0 : 206864 ≤ P0)
    (hLt : es.flatten.length ≤ Lt ∧ Lt < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 922) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (S + 552)) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat es.length)
    (sR0 : μ.readN rd 8 = Num.encodeLE 8 P0) (sR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 Lt)
    (pay : μ.readN P0 es.flatten.length = es.flatten)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (q N : Nat),
      FreeStepsH p (refineContractK cap0 env) 482 ω μ x 20420 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (S + 552) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (S + 552) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (S + 552 + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 552 + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (P0 + es.flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (Lt - es.flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ a, q ≤ a → a < q + 232 * es.length → InData ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ a) ∧
      (∃ csOf : Nat → List Chunk, (∀ j, j < es.length → (∀ c ∈ csOf j, c ∈ chunks s' ∧ c.used = true ∧
        c ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ ∧ c ≠ cp) ∧
        ∀ μ'' : Memory, (∀ c ∈ csOf j, ∀ a, InData c a → μ''.read a = μ'.read a) →
          reps j (csOf j) (μ'.readN (q + 232 * j) 232) μ'') ∧
        ∀ j j', j < es.length → j' < es.length → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j') ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → S + 552 + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ∃ N, Exhausts env cap0 pb p P 482 ω μ x N := by
  obtain ⟨hS0, hSr, hrS, hS8⟩ := hS
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm, hcpu, hcpa⟩ := hcp
  -- the two batches
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, n = 70 + m := ⟨n - 70, by omega⟩
  have hm1 : 1 ≤ m ∧ m < 58 := by omega
  have hl1 : (es.take 70).length = 70 := by simp; omega
  have hl2 : (es.drop 70).length = m := by simp; omega
  have hg1 : ∀ j (hj : j < (es.take 70).length), (es.take 70)[j] = es[j]'(by simp at hj; omega) :=
    fun j hj => List.getElem_take
  have hg2 : ∀ j (hj : j < (es.drop 70).length), (es.drop 70)[j] = es[70 + j]'(by simp at hj; omega) :=
    fun j hj => List.getElem_drop
  have hfl : es.flatten = (es.take 70).flatten ++ (es.drop 70).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  have hfll : (es.take 70).flatten.length + (es.drop 70).flatten.length = es.flatten.length := by
    rw [hfl, List.length_append]
  generalize hf1 : (es.take 70).flatten.length = f1 at hfll
  generalize hf2 : (es.drop 70).flatten.length = f2 at hfll
  have pay1 : μ.readN P0 (es.take 70).flatten.length = (es.take 70).flatten := by
    rw [← readN_take μ P0 es.flatten.length _ (by omega), pay, hfl, List.take_left' rfl]
  have hP1 : ∀ a, P0 ≤ a → a < P0 + (es.take 70).flatten.length → InData cp a :=
    fun a h1 h2 => hcpd a h1 (by omega)
  have hne1 : ∀ j (hj : j < (es.take 70).length), 1 ≤ (es.take 70)[j].length :=
    fun j hj => by rw [hg1 j hj]; exact hne j _
  have hel1 : ∀ j (hj : j < (es.take 70).length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd (Ns j)
      (es.take 70)[j] (reps j) := fun j hj => by rw [hg1 j hj]; exact hel j _
  -- the first batch's start
  rcases vec_preG (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω μ s H S (S + 552) rd P0 Lt v5 v6
      (es.take 70) (fun _ _ _ => True) cp es.length (by rw [hl1]; omega) (by omega) ⟨by omega, by omega⟩ hne1
      ⟨hS0, by omega, hrS, hS8⟩ (by omega) hv5 hv6 ⟨hcpm, hcpu, hcpa⟩ hP1 hP0 ⟨by omega, hLt.2⟩ h0 h1 h5 h6 h7 h8 h9
      sR0 sR8 pay1 tab rt with
    ⟨ω1, μ1, s1, q, N1, run1, inv1, ok1, w0, w8, w16, w544, w536, w528, keep1, fresh1, hi1, hgl1⟩ | hx
  rotate_left
  · exact Or.inr hx
  rw [hl1] at inv1 fresh1 w16
  -- the first batch
  rcases loopAFCd_lowF (p := p) (P := P) env cap0 pb gl (S - 56) rd P0 Lt Ns x (es.take 70) reps 0 q cp _ ok1
      (by rw [hl1]; have := ok1.2.2.2.1; omega) hel1 (es.take 70).length 0 ω1 μ1 s1 (by omega) (by omega)
      (InvAF.toC_zero reps inv1).toD (fun a ha => (hgl1 a ha).trans (hg a ha)) with
    ⟨ω2, μ2, s2, run2, inv2, fr2, low2, b88, w7, csOf1, el1, fr1'⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, Exhausts.pre run1 hx⟩
  have hF : S - 56 + 56 = S := by omega
  have hq64 := ok1.2.2.2.1
  have hqP := ok1.2.1
  obtain ⟨fr2a, fr2b, fr2c, fr2d, fr2e, fr2f⟩ := fr2
  have hst2 := inv2.heap.st
  have l2 : ∀ a l, S ≤ a → a + l ≤ S + 24 → μ2.readN a l = μ1.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => low2 _ (by omega) (by omega))
  -- the first batch's end, `finish_grow` on the old buffer
  obtain ⟨ω3, μ3, run3, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m32, fr3, rd3, wr3⟩ :=
    w1 (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 S 70 m q ⟨by omega, by omega, hS8⟩
      ⟨hm1.1, by omega⟩ (by omega) (by omega) (by rw [inv2.r1, hF]) (by rw [w7, hl1])
      (by rw [l2 _ _ (by omega) (by omega), w8, hN, hm])
      (by rw [l2 _ _ (by omega) (by omega)]; exact w16)
      (by rw [show S + 32 = S - 56 + 88 by omega]; exact b88)
      (by have := inv2.m40; rw [show S - 56 + 96 = S + 40 by omega, hl1] at this; simpa using this)
      (fun a h1 h2 => hst2 a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr4, rd4, wr4⟩ :=
    g3x (p := p) (P := P) (R := refineContractK cap0 env) x ω3 μ3 (S - 40) (S + 296) 70 q (70 + m) 8 14 m (70 + m)
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨by decide, by decide⟩ ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ (by omega)
      (fun a h1 h2 => by rw [wr3]; exact hst2 a (by omega) (by omega))
  have hlow4 : ∀ a, a < 2147483648 → μ4.read a = μ2.read a := fun a h =>
    (fr4 a (by omega) (Or.inl (by omega))).trans (fr3 a (by omega) (Or.inl (by omega)))
  have H4 : HeapCtx env pb S0 S1 μ4 s2 := Decode.GrowOne.ctx_high inv2.heap hlow4 (fun a => by rw [wr4, wr3])
  have hba : s2.base % 8 = 0 := by have := inv2.heap.wf.2.1; omega
  obtain ⟨hcbm, hcbu⟩ := inv2.cbm
  -- `realloc`
  rcases Decode.ReallocCall.realloc_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ4 s2 (S - 40) q 8
      (232 * (70 + m)) pb S0 S1 H4 ⟨_, hcbm, by simp only; omega, rfl⟩ (by omega) (by omega) hba b1 b7 b9 b10
      (by decide) (by decide) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s3, bb, ω5, μ5, hR, run5, e7, H5, dat5, keep5, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp5, stk5, ro5, wr5, e0, e1,
      e5, e6, gl5, base5, frr⟩ |
    ⟨hR, ω5, μ5, run5, e7, -, -, e0, -, -, -, -⟩
  rotate_left
  · have run6 := Decode.VecU8.realloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (by rw [e0, b0])
    exact Or.inr ⟨_, Exhausts.of_realloc (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) e7 hR⟩
  have run6 := Decode.VecU8.realloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (by rw [e0, b0])
  have hcrE : cr = ⟨r - 32, (232 * (70 + m) + 31) / 32 + 1, true⟩ := by
    cases cr; simp only at hcra hcru hcrs ⊢; subst hcru hcrs; congr 1; omega
  subst hcrE
  obtain ⟨hr0, -, hrT⟩ := Decode.VecU8.chunk_in H5.wf hcrm rfl
  simp only at hr0 hrT
  have hb5 := H5.hb0
  have hbT5 := H5.hbT
  have hst5 := H5.st
  obtain ⟨ω6, μ6, run6', c0, c1, c5, c6, cres, cres8, cres16, fr6, rd6, wr6⟩ :=
    Decode.VecU8.g2r (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (S - 40) (S + 296) (232 * (70 + m))
      r 14 607 m (70 + m) ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n8)
      ⟨by decide, by decide, by decide⟩ jte_6 bs_607
      (fun a h1 h2 => Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => hst5 a (by omega) (by omega))
  -- the stack from S up, μ6 against μ3
  have k63 : ∀ a, a < 4294967296 → S ≤ a → (a < S + 296 ∨ S + 320 ≤ a) → μ6.read a = μ3.read a :=
    fun a h0 h1 h2 => (fr6 a h0 h2).trans ((stk5 a h0 (by omega)).trans (fr4 a h0 (Or.inr (by omega))))
  have r63 : ∀ a l, S ≤ a → a + l ≤ 4294967296 → (a + l ≤ S + 296 ∨ S + 320 ≤ a) → μ6.readN a l = μ3.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => k63 _ (by omega) (by omega) (by omega))
  obtain ⟨ω7, μ7, run7, d1, d5, d32, d40, d48, fr7, rd7, wr7⟩ :=
    v2g (p := p) (P := P) (R := refineContractK cap0 env) x ω6 μ6 S (70 + m) m r ⟨by omega, by omega, hS8⟩
      (by omega) ⟨hm1.1, by omega⟩ (by omega) (by rw [c1]; congr 1; omega) c6 cres
      (by rw [show S + 304 = S + 296 + 8 by omega]; exact cres8)
      (by rw [r63 _ _ (by omega) (by omega) (by omega)]; exact m16)
      (by rw [r63 _ _ (by omega) (by omega) (by omega)]; exact m32)
      (fun a h1 h2 => by rw [rd6]; exact Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr6]; exact hst5 a (by omega) (by omega))
  -- memory at 680 against the first batch's end
  have hk73 : ∀ a, a < 4294967296 → S ≤ a → (a < S + 32 ∨ S + 56 ≤ a) → (a < S + 296 ∨ S + 320 ≤ a) →
      μ7.read a = μ3.read a := fun a h0 h1 h2 h3 => (fr7 a h0 h2).trans (k63 a h0 h1 h3)
  have r72 : ∀ a l, S ≤ a → a + l ≤ 4294967296 →
      (S + 24 ≤ a ∧ a + l ≤ S + 32 ∨ S + 56 ≤ a ∧ a + l ≤ S + 296 ∨ S + 320 ≤ a) → μ7.readN a l = μ2.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj =>
      (hk73 _ (by omega) (by omega) (by omega) (by omega)).trans (fr3 _ (by omega) (by omega)))
  have hlow7 : ∀ a, a < 2147483648 → μ7.read a = μ5.read a := fun a h =>
    (fr7 a (by omega) (Or.inl (by omega))).trans (fr6 a (by omega) (Or.inl (by omega)))
  have H7 : HeapCtx env pb S0 S1 μ7 s3 := Decode.GrowOne.ctx_high H5 hlow7 (fun a => by rw [wr7, wr6])
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run6'.trans run7))))))
  obtain ⟨tab7, rtab7⟩ := ExitRun.ro_keep H run17 (a := 67476) (l := 100) (by omega)
  -- the payload's chunk
  have hcp1 := (keep1 cp hcpm hcpu).1
  have hcp2 : cp ∈ chunks s2 := fr2b cp hcp1 hcpu
  have hcpne1 : cp ≠ ⟨q - 32, (232 * 70 + 31) / 32 + 1, true⟩ := fresh1 cp hcpm hcpu
  have ainj2 : ∀ c ∈ chunks s2, ∀ d ∈ chunks s2, c.addr = d.addr → c = d := by
    have ht := inv2.heap.wf.2.2.2.1; unfold TilesOk at ht; exact Tiles.addr_inj ht
  have hcpq : cp.addr + 32 ≠ q := fun e => hcpne1 (ainj2 _ hcp2 _ hcbm (by simp only; omega))
  have hcp3 : cp ∈ chunks s3 := keep5 cp hcp2 hcpu hcpq
  have hcpd7 : ∀ a, InData cp a → μ7.read a = μ.read a := fun a ha => by
    have ha' := ha; unfold InData at ha'
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
    have hbT := H.hbT
    have hdj := Decode.VecU8.data_disj inv2.heap.wf hcp2 hcbm hcpne1 ha
    simp only at hdj
    rw [hlow7 a (by omega), kp5 a ⟨cp, hcp2, hcpu, hcpq, ha⟩, hlow4 a (by omega),
      fr2c cp hcp1 hcpu a ha (by omega), (keep1 cp hcpm hcpu).2 a ha]
  have pay2 : μ7.readN (P0 + f1) (es.drop 70).flatten.length = (es.drop 70).flatten := by
    rw [Memory.readN_congr (fun j hj => hcpd7 _ (hcpd _ (by omega) (by omega))),
      Decode.Loop.readN_sub μ P0 es.flatten.length f1 _ _ pay (by omega), hfl, ← hf1, List.drop_left]
    exact List.take_of_length_le (Nat.le_refl _)
  have hoff1 : off (es.take 70) (es.take 70).length = f1 := by
    rw [← hf1]; simp [off, show min 70 es.length = 70 by omega, List.take_take]
  have hr8 : r % 8 = 0 := by
    have ht := H5.wf.2.2.2.1; unfold TilesOk at ht
    have := Decode.VecKey336.tiles_mod _ _ ht _ hcrm
    simp only at this
    have := H5.wf.2.1
    omega
  have hR1 : realloc (growTo pb) hb s2 q 1 ((232 * (70 + m) + 31) / 32) = some (r, s3, bb) := hR
  have hfr := Decode.VecU8.realloc_fresh inv2.heap.wf ⟨_, hcbm, by simp only; omega, rfl⟩ (by omega) hR1
  have hne2q : ∀ c ∈ chunks s2, c ≠ ⟨q - 32, (232 * 70 + 31) / 32 + 1, true⟩ → c.addr + 32 ≠ q :=
    fun c hc hne e => hne (ainj2 _ hc _ hcbm (by simp only; omega))
  have hncr : ∀ c ∈ chunks s2, c.used = true → c ≠ ⟨q - 32, (232 * 70 + 31) / 32 + 1, true⟩ →
      c ≠ ⟨r - 32, (232 * (70 + m) + 31) / 32 + 1, true⟩ := fun c hc hu hne e =>
    hfr c hc hu (hne2q c hc hne) (by rw [e]; simp only; omega)
  have hflat : 1 ≤ es.flatten.length := by
    have h0 := off_lt es 0 (by omega)
    have h1 := hne 0 (by omega)
    omega
  have hcpcr : cp ≠ ⟨r - 32, (232 * (70 + m) + 31) / 32 + 1, true⟩ := hncr cp hcp2 hcpu hcpne1
  have hapart := PassLoop.chunk_apart H5.wf hcp3 hcrm hcpcr
  simp only at hapart
  have hcpP0 := hcpd P0 (Nat.le_refl _) (by omega)
  unfold InData at hcpP0
  have hcpE : P0 + es.flatten.length ≤ cp.addr + 32 * cp.size := by
    have := hcpd (P0 + es.flatten.length - 1) (by omega) (by omega)
    unfold InData at this; omega
  obtain ⟨hcp0, -, hcpT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
  have hbT0 := H.hbT
  have ok2 : OkFD (S - 56) rd (P0 + f1) (Lt - f1) (es.drop 70) 70 r :=
    ⟨by omega, ⟨by rcases hapart with h | h <;> omega, by omega⟩, hr8, by omega,
      fun j hj => by rw [hg2 j hj]; exact hne _ _, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
  have inv7 : InvAFCd env pb (S - 56) rd (P0 + f1) (Lt - f1) (es.drop 70) (fun j => reps (70 + j)) 70 0 r cp
      ⟨r - 32, (232 * (70 + m) + 31) / 32 + 1, true⟩ ω7 μ7 s3 :=
    ⟨by rw [d1]; congr 1; omega, by rw [hl2, Nat.sub_zero]; exact d5,
      by rw [r72 _ _ (by omega) (by omega) (by omega)]; exact inv2.m24,
      by rw [show S - 56 + 96 = S + 40 by omega, hl2]; exact d40,
      by rw [show S - 56 + 104 = S + 48 by omega]; exact d48,
      by rw [r72 _ _ (by omega) (by omega) (by omega), inv2.m56, hl1],
      by rw [r72 _ _ (by omega) (by omega) (by omega), inv2.rP, hoff1]; simp [off],
      by rw [r72 _ _ (by omega) (by omega) (by omega), inv2.rL, hoff1]; simp [off],
      pay2, tab7.trans tab,
      ⟨fun _ => [], fun j hj => absurd hj (Nat.not_lt_zero _), fun j j' hj => absurd hj (Nat.not_lt_zero _)⟩,
      fun a h1 h2 => H7.st a (by omega) (by omega), fun a h1 h2 => H7.st a (by omega) (by omega),
      fun a h1 h2 => by rw [rtab7 a h1 h2]; exact rt a h1 h2, H7, ⟨hcp3, hcpu⟩,
      fun a h1 h2 => hcpd a (by omega) (by omega), ⟨hcrm, rfl⟩,
      fun a h1 h2 => ⟨by simp only; omega, by simp only; omega⟩⟩
  have hg7 : ∀ a, Glob a → μ7.read a = gl a := fun a ha => by
    have hg' := ha; unfold Glob at hg'
    rw [hlow7 a (by omega), gl5 a ha, hlow4 a (by omega), fr2e a ha, hgl1 a ha, hg a ha]
  have hel2 : ∀ j (hj : j < (es.drop 70).length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd
      (Ns (70 + j)) (es.drop 70)[j] (reps (70 + j)) := fun j hj => by rw [hg2 j hj]; exact hel _ _
  -- the second batch
  rcases loopAFCd_lowFD (p := p) (P := P) env cap0 pb gl (S - 56) rd (P0 + f1) (Lt - f1) (fun j => Ns (70 + j)) x
      (es.drop 70) (fun j => reps (70 + j)) 70 r cp _ ok2 (by omega) hel2 (es.drop 70).length 0 ω7 μ7 s3
      (by omega) (by omega) inv7 hg7 with
    ⟨ω8, μ8, s4, run8, inv8, fr8, low8, b88', w7', csOf2, el2, fresh2⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, Exhausts.pre run17 hx⟩
  obtain ⟨fr8a, fr8b, fr8c, fr8d, fr8e, fr8f⟩ := fr8
  have hst8 := inv8.heap.st
  have hr32 : r - 32 + 32 = r := by omega
  have r87 : ∀ a l, S ≤ a → a + l ≤ S + 24 → μ8.readN a l = μ7.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => low8 _ (by omega) (by omega))
  have r73 : ∀ a l, S ≤ a → a + l ≤ S + 32 → μ7.readN a l = μ3.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => hk73 _ (by omega) (by omega) (by omega) (by omega))
  have r31 : ∀ a l, S ≤ a → a + l ≤ S + 8 → μ3.readN a l = μ2.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => fr3 _ (by omega) (by omega))
  have hoff2 : off (es.drop 70) (es.drop 70).length = (es.drop 70).flatten.length :=
    (fun (l : List (List UInt8)) => (show off l l.length = l.flatten.length by simp [off])) _
  -- the return
  obtain ⟨ω9, μ9, run9, c1', c7', c11', c296', c304', cfr9, crd9, cwr9⟩ := v3a (p := p) (P := P)
    (R := refineContractK cap0 env) x ω8 μ8 S (S + 552) m (70 + m) r (70 + m) ⟨by omega, by omega, hS8⟩
    (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [inv8.r1, hF])
    (by rw [r87 _ _ (by omega) (by omega), r73 _ _ (by omega) (by omega), r31 _ _ (by omega) (by omega),
      l2 _ _ (by omega) (by omega)]; exact w0)
    (by rw [r87 _ _ (by omega) (by omega), r73 _ _ (by omega) (by omega)]; exact m8)
    (by rw [r87 _ _ (by omega) (by omega), r73 _ _ (by omega) (by omega)]; exact m16)
    (by have := inv8.m40; rwa [show S - 56 + 96 = S + 40 by omega, hl2] at this)
    (by have := inv8.m48; rwa [show S - 56 + 104 = S + 48 by omega] at this)
    (by have := inv8.m56; rwa [show S - 56 + 112 = S + 56 by omega, hl2] at this)
    (fun a h1 h2 => hst8 a (by omega) (by omega))
  have hhi : ∀ a, a < 4294967296 → S + 552 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ8.read a = μ.read a :=
    fun a h0 h1 h2 => by
      rw [fr8a a (by omega) h0 h2, hk73 a h0 (by omega) (by omega) (by omega), fr3 a h0 (by omega),
        fr2a a (by omega) h0 h2]
      exact hi1 a h0 (by omega)
  have k98 : ∀ a l, S + 312 ≤ a → a + l ≤ 4294967296 → μ9.readN a l = μ8.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => cfr9 _ (by omega) (by omega))
  have h88 : ∀ a l, S + 528 ≤ a → a + l ≤ S + 552 → μ8.readN a l = μ1.readN a l := fun a l h0 h1 =>
    Memory.readN_congr (fun j hj => by
      rw [fr8a _ (by omega) (by omega) (by omega), hk73 _ (by omega) (by omega) (by omega) (by omega),
        fr3 _ (by omega) (by omega), fr2a _ (by omega) (by omega) (by omega)])
  obtain ⟨ω10, μ10, run10, g1', g5', g6', g0', g8', g16', gfr, grd, gwr⟩ := v3b (p := p) (P := P)
    (R := refineContractK cap0 env) x ω9 μ9 S (S + 552) (70 + m) r (70 + m) v5 v6 ⟨by omega, by omega, hS8⟩
    ⟨by omega, by omega, Or.inr (Nat.le_refl _)⟩ (by omega) (by omega) (by omega) hv5 hv6 c1' c7' c11' c296' c304'
    (by rw [k98 _ _ (by omega) (by omega), h88 _ _ (by omega) (by omega)]; exact w544)
    (by rw [k98 _ _ (by omega) (by omega), h88 _ _ (by omega) (by omega)]; exact w536)
    (by rw [k98 _ _ (by omega) (by omega), h88 _ _ (by omega) (by omega)]; exact w528)
    (fun a h1 h2 => by rw [crd9]; exact Memory.readable_of_writable (hst8 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [cwr9]; exact hst8 a (by omega) (by omega))
  have k108 : ∀ a, a < 4294967296 → (a < S + 296 ∨ S + 312 ≤ a) → (a < S + 552 ∨ S + 576 ≤ a) →
      μ10.read a = μ8.read a := fun a h0 h1 h2 => by rw [gfr a h0 h2, cfr9 a h0 h1]
  have hlow10 : ∀ a, a < 2147483648 → μ10.read a = μ8.read a := fun a h => k108 a (by omega) (by omega) (by omega)
  have H10 : HeapCtx env pb S0 S1 μ10 s4 := Decode.GrowOne.ctx_high inv8.heap hlow10 (fun a => by rw [gwr, cwr9])
  -- the chunks
  have hcrm4 := fr8b _ hcrm rfl
  have hk1 : ∀ c ∈ chunks s2, c.used = true → c ≠ ⟨q - 32, (232 * 70 + 31) / 32 + 1, true⟩ →
      c ∈ chunks s4 ∧ ∀ a, InData c a → μ10.read a = μ2.read a := fun c hc hu hne => by
    have hc3 := keep5 c hc hu (hne2q c hc hne)
    have hc' := hncr c hc hu hne
    refine ⟨fr8b c hc3 hu, fun a ha => ?_⟩
    have ha' := ha; unfold InData at ha'
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in inv2.heap.wf hc hu
    have hdj := Decode.VecU8.data_disj H5.wf hc3 hcrm hc' ha
    simp only at hdj
    rw [hlow10 a (by omega), fr8c c hc3 hu a ha (by omega), hlow7 a (by omega),
      kp5 a ⟨c, hc, hu, hne2q c hc hne, ha⟩, hlow4 a (by omega)]
  -- the first 70 slots, copied by `realloc`
  have hu2 : usable s2 q = (232 * 70 + 31) / 32 := by
    have := Decode.VecU8.usable_of_chunk hcbm
    simp only at this
    rw [show q - 32 + 32 = q by omega] at this
    rw [this]
  rw [hu2, Nat.min_eq_left (by omega)] at dat5
  have slot1 : ∀ j, j < 70 → μ10.readN (r + 232 * j) 232 = μ2.readN (q + 232 * (0 + j)) 232 := fun j hj => by
    have e5 := Decode.VecKey336.readN_sub336 (i := 232 * j) (m := 232)
      (Decode.VecU8.readN_prefix (n := 232 * 70) (by omega) dat5) (by omega)
    rw [Memory.readN_congr (fun i hi => (hlow10 _ (by omega)).trans
      ((fr8c _ hcrm rfl _ ⟨by simp only; omega, by simp only; omega⟩ (by omega)).trans (hlow7 _ (by omega)))), e5,
      Nat.zero_add, Memory.readN_congr (fun i hi => hlow4 _ (by omega))]
  have hcs3 : ∀ c ∈ chunks s2, c.used = true → c ≠ ⟨q - 32, (232 * 70 + 31) / 32 + 1, true⟩ → c ∈ chunks s3 :=
    fun c hc hu hne => keep5 c hc hu (hne2q c hc hne)
  rw [hN, hm]
  refine Or.inl ⟨ω10, μ10, s4, r, _, run17.trans (run8.trans (run9.trans run10)), g1', g5', g6', g0', g8', g16', ?_, ?_,
    H10, hcrm4, fun a h1 h2 => ⟨by simp only; omega, by simp only; omega⟩,
    ⟨fun j => if j < 70 then csOf1 j else csOf2 (j - 70), fun j hj => ?_, fun j j' hj hj' hne c hc => ?_⟩,
    fun c hc hu => ?_, fun d hd hu => hncr d (fr2b d (keep1 d hd hu).1 hu) hu (fresh1 d hd hu),
    fun a h0 h1 h2 => ?_, fun a ha => ?_⟩
  · rw [Memory.readN_congr (fun j hj => k108 _ (by omega) (by omega) (by omega))]
    have := inv8.rP; rw [hoff2, hf2] at this
    rw [show P0 + es.flatten.length = P0 + f1 + f2 by omega]; exact this
  · rw [Memory.readN_congr (fun j hj => k108 _ (by omega) (by omega) (by omega))]
    have := inv8.rL; rw [hoff2, hf2] at this
    rw [show Lt - es.flatten.length = Lt - f1 - f2 by omega]; exact this
  · by_cases h70 : j < 70
    · simp only [h70, ↓reduceIte]
      obtain ⟨hcs, hrep⟩ := el1.1 j (by rw [hl1]; exact h70)
      refine ⟨fun c hc => ?_, fun μ'' hag => ?_⟩
      · obtain ⟨hc2, hcu, hcb, hcp'⟩ := hcs c hc
        exact ⟨(hk1 c hc2 hcu hcb).1, hcu, hncr c hc2 hcu hcb, hcp'⟩
      · rw [slot1 j h70]
        exact hrep μ'' (fun c hc a ha =>
          (hag c hc a ha).trans ((hk1 c (hcs c hc).1 (hcs c hc).2.1 (hcs c hc).2.2.1).2 a ha))
    · simp only [h70, ↓reduceIte]
      obtain ⟨hcs, hrep⟩ := el2.1 (j - 70) (by rw [hl2]; omega)
      refine ⟨fun c hc => hcs c hc, fun μ'' hag => ?_⟩
      have := hrep μ'' (fun c hc a ha => by
        obtain ⟨hc4, hcu, -⟩ := hcs c hc
        obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in inv8.heap.wf hc4 hcu
        have hbT8 := inv8.heap.hbT
        have ha' := ha; unfold InData at ha'
        rw [hag c hc a ha, hlow10 a (by omega)])
      simp only at this
      rw [show 70 + (j - 70) = j by omega] at this
      rw [Memory.readN_congr (fun i hi => hlow10 _ (by omega))]; exact this
  · by_cases h70 : j < 70 <;> by_cases h70' : j' < 70 <;> simp only [h70, h70', ↓reduceIte] at hc ⊢
    · exact el1.2 j j' (by rw [hl1]; exact h70) (by rw [hl1]; exact h70') hne c hc
    · intro hc'
      obtain ⟨hc2, hcu, hcb, -⟩ := (el1.1 j (by rw [hl1]; exact h70)).1 c hc
      exact fresh2 (j' - 70) (Nat.zero_le _) (by rw [hl2]; omega) c hc' c (hcs3 c hc2 hcu hcb) hcu rfl
    · intro hc'
      obtain ⟨hc2, hcu, hcb, -⟩ := (el1.1 j' (by rw [hl1]; exact h70')).1 c hc'
      exact fresh2 (j - 70) (Nat.zero_le _) (by rw [hl2]; omega) c hc c (hcs3 c hc2 hcu hcb) hcu rfl
    · exact el2.2 (j - 70) (j' - 70) (by rw [hl2]; omega) (by rw [hl2]; omega) (by omega) c hc
  · obtain ⟨hc1, hd1⟩ := keep1 c hc hu
    have hcb := fresh1 c hc hu
    have hc2 := fr2b c hc1 hu
    obtain ⟨hc4, hd4⟩ := hk1 c hc2 hu hcb
    refine ⟨hc4, fun a ha => ?_⟩
    have ha' := ha; unfold InData at ha'
    have hdj := Decode.VecU8.data_disj inv2.heap.wf hc2 hcbm hcb ha
    simp only at hdj
    rw [hd4 a ha, fr2c c hc1 hu a ha (by omega), hd1 a ha]
  · rw [k108 a h0 (by omega) (by omega)]; exact hhi a h0 (by omega) h2
  · have hg' := ha; unfold Glob at hg'
    rw [hlow10 a (by omega), fr8e a ha, hg7 a ha]; exact (hg a ha).symm

/-- **`Vec<Instruction>::decode`, the slots' chunks seen, 1 ≤ n < 128**: `vec_oneC` for n ≤ 70, `vec_twoC`
    above. -/
theorem vec_anyC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat} (gl : Nat → UInt8)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (S rd P0 Lt v5 v6 : Nat) (es : List (List UInt8)) (reps : Nat → List Chunk → List UInt8 → Memory → Prop)
    (cp : Chunk) (Ns : Nat → Nat)
    (hel : ∀ j (hj : j < es.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd (Ns j) es[j] (reps j))
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (hn : 1 ≤ es.length ∧ es.length < 128) (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hS : S0 + 2104 ≤ S ∧ S + 552 + 24 ≤ rd ∧ rd + 16 ≤ S1 ∧ S % 8 = 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base)
    (hcpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a) (hP0 : 206864 ≤ P0)
    (hLt : es.flatten.length ≤ Lt ∧ Lt < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 922) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (S + 552)) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat es.length)
    (sR0 : μ.readN rd 8 = Num.encodeLE 8 P0) (sR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 Lt)
    (pay : μ.readN P0 es.flatten.length = es.flatten)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (q N : Nat),
      FreeStepsH p (refineContractK cap0 env) 482 ω μ x 20420 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (S + 552) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (S + 552) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (S + 552 + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 552 + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (P0 + es.flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (Lt - es.flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ a, q ≤ a → a < q + 232 * es.length → InData ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ a) ∧
      (∃ csOf : Nat → List Chunk, (∀ j, j < es.length → (∀ c ∈ csOf j, c ∈ chunks s' ∧ c.used = true ∧
        c ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ ∧ c ≠ cp) ∧
        ∀ μ'' : Memory, (∀ c ∈ csOf j, ∀ a, InData c a → μ''.read a = μ'.read a) →
          reps j (csOf j) (μ'.readN (q + 232 * j) 232) μ'') ∧
        ∀ j j', j < es.length → j' < es.length → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j') ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → S + 552 + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ∃ N, Exhausts env cap0 pb p P 482 ω μ x N := by
  by_cases h70 : es.length ≤ 70
  · exact DecodeVecC.vec_oneC (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω μ s H S rd P0 Lt v5 v6 es reps
      cp Ns hel hg ⟨hn.1, h70⟩ hne hS hv5 hv6 hcp hcpd hP0 hLt h0 h1 h5 h6 h7 h8 h9 sR0 sR8 pay tab rt
  · exact vec_twoC (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω μ s H S rd P0 Lt v5 v6 es reps
      cp Ns hel hg ⟨by omega, hn.2⟩ hne hS hv5 hv6 hcp hcpd hP0 hLt h0 h1 h5 h6 h7 h8 h9 sR0 sR8 pay tab rt

end Services.Bootstrap.Refine.DecodeVec2C
