import Services.Bootstrap.Encode.EncMH

/-!
# Refine's output encoder over `EncOkMH` elements, with no capacity hypothesis

`EncMD.loopMD`, `restMD` and `encode_okMD_big` for elements given as `EncOkMH` (growth allowed): the
encoder's writer `{cap, buf, len}` at M + 24 starts as an allocated chunk of the allocator state, and
each append may grow it (`BufH`, bound M + 56). Every stage either goes on or reaches a failed allocator
call (`ExhaustsW`). The only size hypothesis left is `hbig`: twice the whole output (ℰ(n), the n
encodings and the 2-octet `work_item_index`) within `capBound`, an obligation of the top level.

* `LayLMH`: `LayLMD` with the instructions in an allocated chunk other than the buffer (`arr`), the
  elements `EncOkMH 232`, their heap octets kept by the appends (`hsrc`, `SafeR`), and `rep` depending on
  memory only through those octets (`rcong`).
* `WMH` / `stepMH` / `FinMH` / `loopMH`: the element loop; `restMH`: from the prefix's return to the
  encoder's; `encode_okMH_big`: the encoder (30073) for 0 < n < 2^32 elements.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.GrowOne
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Encode.Top Services.Bootstrap.Encode.Loop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The encoder's layout, for `EncOkMH` elements** (see the module doc), at memory μ0 and allocator
    state s0. -/
structure LayLMH (env : RefineHost.Env) (K pb S0 S1 : Nat) (P : Program) (p : ByteArray)
    (M E n buf cap : Nat) (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Memory → Prop)
    (src : Nat → Nat → Nat → Prop) (s0 : State) (μ0 : Memory) : Prop where
  fr : FrH S0 S1 232 M (M + 24)
  hM80 : M + 80 ≤ S1
  arr : HeapSrc s0 buf E (232 * n)
  cpos : 0 < cap
  cb : cap ≤ capBound
  H : HeapCtx env pb S0 S1 μ0 s0
  chunk : ∃ c ∈ chunks s0, c.used = true ∧ c.addr + 32 = buf ∧ cap ≤ 32 * (c.size - 1)
  ok : ∀ j, j < n → EncOkMH env K pb p P 232 (enc j) (rep j) (src j)
  rep0 : ∀ j, j < n → rep j (μ0.readN (E + 232 * j) 232) μ0
  rcong : ∀ j, j < n → ∀ (bs : List UInt8) (μ μ' : Memory),
    (∀ q m, src j q m → μ'.readN q m = μ.readN q m) → rep j bs μ → rep j bs μ'
  hsrc : ∀ j, j < n → ∀ q m, src j q m → SafeR s0 buf (M + 56) S1 (M + 24) q m
  tab : μ0.readN 67376 100 = table
  rtab : ∀ a, 67376 ≤ a → a < 67476 → μ0.readable a = true

/-- **The encoder at 30145, about to encode element k**, after `pre` (ℰ(n)): the octets
    `pre ++ enc 0 ++ … ++ enc (k − 1)` appended since μ0. -/
structure WMH (env : RefineHost.Env) (pb S0 S1 M E n buf : Nat) (s0 : State) (μ0 : Memory)
    (pre : List UInt8) (enc : Nat → List UInt8) (k : Nat) (ω : Regs) (μ : Memory) : Prop where
  h0 : ω[0] = UInt64.ofNat 1418
  h1 : ω[1] = UInt64.ofNat M
  h5 : ω[5] = UInt64.ofNat (E + 232 * k)
  h6 : ω[6] = UInt64.ofNat (232 * (n - k))
  h7 : ω[7] = UInt64.ofNat (E + 232 * k)
  h8 : ω[8] = UInt64.ofNat (M + 24)
  s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232)
  lowfr : ∀ a, M ≤ a → a < M + 16 → μ.read a = μ0.read a
  buf : ∃ cap ptr s, BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s0 μ0 (pre ++ out enc k) cap ptr s μ

/-- **At the call appending `work_item_index`**, all n elements encoded. -/
structure FinMH (env : RefineHost.Env) (pb S0 S1 M n buf Wi : Nat) (s0 : State) (μ0 : Memory)
    (pre : List UInt8) (enc : Nat → List UInt8) (ω : Regs) (μ : Memory) : Prop where
  h0 : ω[0] = UInt64.ofNat 1420
  h1 : ω[1] = UInt64.ofNat M
  h7 : ω[7] = UInt64.ofNat (M + 24)
  h8 : ω[8] = UInt64.ofNat (M + 52)
  h9 : ω[9] = UInt64.ofNat 2
  w52 : μ.readN (M + 52) 2 = μ0.readN (Wi + 24) 2
  lowfr : ∀ a, M ≤ a → a < M + 16 → μ.read a = μ0.read a
  buf : ∃ cap ptr s, BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s0 μ0 (pre ++ out enc n) cap ptr s μ

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {K pb S0 S1 : Nat} {M E n buf cap : Nat} {enc : Nat → List UInt8}
  {rep : Nat → List UInt8 → Memory → Prop} {src : Nat → Nat → Nat → Prop} {s0 : State}

/-- **One element, with growth**: from `WMH k` (k < n) at 30145, element k is encoded and the encoder is
    at 30215, or a failed allocator call. -/
theorem stepMH (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) {pre : List UInt8}
    (L : LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s0 μ0)
    (hbig : 2 * (pre.length + off enc n) ≤ capBound) (k : Nat) (hk : k < n)
    (st : WMH env pb S0 S1 M E n buf s0 μ0 pre enc k ω μ) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x 30215 ω' μ' x (encGas (enc k)) ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[6] = UInt64.ofNat (232 * (n - k)) ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      (∀ a, M ≤ a → a < M + 16 → μ'.read a = μ0.read a) ∧
      ∃ cap ptr s, BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s0 μ0 (pre ++ out enc (k + 1)) cap ptr s μ') ∨
    ExhaustsW env K pb p P 30145 ω μ x (encGas (enc k)) := by
  obtain ⟨cap1, ptr1, s1, W⟩ := st.buf
  obtain ⟨e, he, heu, hne, hE1, hE2⟩ := L.arr
  obtain ⟨g1, g2, -⟩ := W.others e he heu hne
  have hei := chunk_in L.H.wf he heu
  have := L.H.hb0; have := L.H.hbT
  have hon : off enc (k + 1) ≤ off enc n := by
    have h := off_le enc (k + 1) (n - (k + 1)); rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
  rw [off_succ] at hon
  have hlen : (pre ++ out enc k).length = pre.length + off enc k := by simp [length_out]
  have hslot0 : SafeR s0 buf (M + 56) S1 (M + 24) (E + 232 * k) 232 :=
    Or.inr ⟨e, he, heu, hne, by omega, by omega⟩
  have La : LayDH env pb S0 S1 P 232 M (E + 232 * k) (M + 24) cap1 ptr1 (0 + (pre ++ out enc k).length) 1418
      30215 s1 μ :=
    { fr := L.fr, hS := by omega, hS' := by omega, slot := Or.inr ⟨e, g1, heu, g2, by omega, by omega⟩,
      vc := W.vc, vp := W.vp, vl := W.vl, hlc := W.room, cpos := W.cpos, cb := W.cb, H := W.H,
      chunk := W.chunk, hret := ⟨by decide, by decide, by decide⟩, hjt := jte_708, hbt := bs_30215 }
  have hrep : rep k (μ.readN (E + 232 * k) 232) μ := by
    rw [W.readN_safe hslot0]
    exact L.rcong k hk _ μ0 μ (fun q m h => W.readN_safe (L.hsrc k hk q m h)) (L.rep0 k hk)
  rcases L.ok k hk x ω μ s1 S0 S1 M (E + 232 * k) (M + 24) cap1 ptr1 _ 1418 30215 st.h0 st.h1 st.h7 st.h8 hrep La
      (by rw [hlen]; omega)
      (by rw [Memory.readN_congr (fun j hj => W.low _ (by omega))]; exact L.tab)
      (fun a h1 h2 => by rw [(W.acc a (Or.inl (by omega))).1]; exact L.rtab a h1 h2)
      (fun q m h => (W.safe (L.hsrc k hk q m h)).mono (by omega)) with
    ⟨ω1, μ1, run1, -, e1, -, e6, cap2, ptr2, s2, W2⟩ | hx
  · have W3 := (W.trans (W2.mono (B' := M + 56) (by omega))).cast
      (by rw [out_succ, List.append_assoc])
    have k1 : ∀ a, M ≤ a → a < M + 24 → μ1.read a = μ.read a := fun a h1 h2 =>
      W2.hi a (by have := L.fr.hvS1; have := L.H.hS1; omega) h1 (Or.inl h2)
    refine Or.inl ⟨ω1, μ1, run1, e1, e6.trans st.h6, ?_, fun a h1 h2 => (k1 a h1 (by omega)).trans (st.lowfr a h1 h2),
      cap2, ptr2, s2, W3⟩
    rw [Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact st.s16
  · exact Or.inr hx

/-- **The element loop, with growth**: from `WMH k` with m = n − k > 0 elements left, the encoder encodes
    them all and reaches the call appending `work_item_index` (`FinMH`), or a failed allocator call. -/
theorem loopMH (x : RefineCtx) {pre : List UInt8} {Wi : Nat} (μ0 : Memory)
    (L : LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s0 μ0)
    (hbig : 2 * (pre.length + off enc n) ≤ capBound)
    (s8 : μ0.readN (M + 8) 8 = Num.encodeLE 8 Wi)
    (hWi : Wi + 26 ≤ 4294967296) (hWiM : Wi + 16 ≤ M ∨ M + 80 ≤ Wi)
    (hWs : SafeR s0 buf (M + 56) S1 (M + 24) (Wi + 24) 2) :
    ∀ m k (ω : Regs) (μ : Memory), k + m = n → 0 < m → WMH env pb S0 S1 M E n buf s0 μ0 pre enc k ω μ →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x 58508 ω' μ' x
          (4100 * m + (2000 + growGas) * (off enc n - off enc k)) ∧
        FinMH env pb S0 S1 M n buf Wi s0 μ0 pre enc ω' μ') ∨
      ExhaustsW env K pb p P 30145 ω μ x (4100 * m + (2000 + growGas) * (off enc n - off enc k)) := by
  have hM := L.fr.hF2; have hM8 := L.fr.hF8; have hvS := L.fr.hvS1; have hS1 := L.H.hS1; have h80 := L.hM80
  have hFS0 := L.fr.hFS0
  have hst := L.H.st
  intro m
  induction m with
  | zero => intro k ω μ _ h; omega
  | succ m ih =>
    intro k ω μ hkm _ st
    have hk : k < n := by omega
    have hon : off enc (k + 1) ≤ off enc n := by
      have h := off_le enc (k + 1) (n - (k + 1)); rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
    have hos := off_succ enc k
    rcases stepMH (p := p) (P := P) x ω μ μ0 L hbig k hk st with
      ⟨ω1, μ1, run1, a1, a6, a16, alow, cap1, ptr1, s1, W1⟩ | hx
    rotate_left
    · exact Or.inr (hx.mono (by unfold encGas growGas; omega))
    have wst : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := W1.H.st
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- the last element: on to `work_item_index`
      have hkn : k + 1 = n := by omega
      obtain ⟨ω2, μ2, run2, b0, b1, b7, b8, b9, b52, bfr, brd, bwr⟩ := tC (p := p) (P := P)
        (R := refineContractK K env) x ω1 μ1 30215 M Wi (Or.inl ⟨rfl, by rw [a6, show n - k = 1 by omega]⟩)
        (by omega) hWi (by omega) a1
        (by rw [Memory.readN_congr (fun j hj => alow _ (by omega) (by omega))]; exact s8)
        (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
        (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe hWs) a h1 h2)
        (fun a h1 h2 => wst a (by omega) (by omega))
      have W2 := W1.frame (M + 52) (M + 54) (by omega) (by omega) (Or.inr (by omega)) bfr brd bwr
      rw [hkn] at W2
      refine Or.inl ⟨ω2, μ2, (run1.trans run2).mono (by unfold encGas growGas; rw [← hkn, hos]; omega),
        ⟨b0, b1, b7, b8, b9, by rw [b52, W1.readN_safe hWs], fun a h1 h2 => ?_, ⟨_, _, _, W2⟩⟩⟩
      rw [bfr a (by omega) (by omega)]; exact alow a h1 h2
    · -- more elements: on to the next one
      obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b16, bfr, brd, bwr⟩ := tB (p := p) (P := P)
        (R := refineContractK K env) x ω1 μ1 M (E + 232 * k + 232) (232 * (n - (k + 1))) (by omega)
        (by obtain ⟨e, he, heu, -, -, h2⟩ := L.arr; have := chunk_in L.H.wf he heu; have := L.H.hbT; omega)
        ⟨by omega, by omega⟩ a1 (by rw [a6]; congr 1; omega) a16
        (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
        (fun a h1 h2 => wst a (by omega) (by omega))
      have W2 := W1.frame (M + 16) (M + 24) (by omega) (by omega) (Or.inl (by omega)) bfr brd bwr
      have st2 : WMH env pb S0 S1 M E n buf s0 μ0 pre enc (k + 1) ω2 μ2 :=
        { h0 := b0, h1 := b1, h5 := by rw [b5, show E + 232 * k + 232 = E + 232 * (k + 1) by omega], h6 := b6,
          h7 := by rw [b7, show E + 232 * k + 232 = E + 232 * (k + 1) by omega],
          h8 := b8, s16 := by rw [b16, show E + 232 * k + 232 + 232 = E + 232 * (k + 1) + 232 by omega],
          lowfr := fun a h1 h2 => by rw [bfr a (by omega) (by omega)]; exact alow a h1 h2,
          buf := ⟨_, _, _, W2⟩ }
      rcases ih (k + 1) ω2 μ2 (by omega) hm st2 with ⟨ω3, μ3, run3, fin⟩ | hx
      · exact Or.inl ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by unfold encGas growGas; omega), fin⟩
      · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas growGas; omega))

/-- **The encoder after the length prefix, with growth** (30122): from the writer `BufH pre` at M + 24,
    the encoder encodes the n > 0 elements, appends the 2-octet `work_item_index`, stores the result
    `{cap', ptr', |pre| + off + 2}` at O and returns to `ret`; or a failed allocator call. -/
theorem restMH (x : RefineCtx) (ω : Regs) (μ0 μ2 : Memory) {pre : List UInt8} {Wi cap2 ptr2 : Nat}
    {s2 : State} (L : LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s0 μ0)
    (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (hbig : 2 * (pre.length + off enc n + 2) ≤ capBound)
    (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 4294967296)
    (b1 : ω[1] = UInt64.ofNat M) (b5 : ω[5] = UInt64.ofNat E) (b6 : ω[6] = UInt64.ofNat (232 * n))
    (W : BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s0 μ0 pre cap2 ptr2 s2 μ2)
    (lowfr : ∀ a, M ≤ a → a < M + 24 → μ2.read a = μ0.read a)
    (s0' : μ0.readN M 8 = Num.encodeLE 8 O) (s8 : μ0.readN (M + 8) 8 = Num.encodeLE 8 Wi)
    (s16 : μ0.readN (M + 16) 8 = Num.encodeLE 8 n)
    (sr : μ0.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ0.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ0.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hWi : Wi + 26 ≤ 4294967296) (hWiM : Wi + 16 ≤ M ∨ M + 80 ≤ Wi)
    (hWs : SafeR s0 buf (M + 56) S1 (M + 24) (Wi + 24) 2)
    (hO : S0 ≤ O ∧ O + 24 ≤ S1) (hOM : O + 24 ≤ M + 56 ∨ M + 80 ≤ O) :
    (∃ cap' ptr' s' ω' μ5 μ', FreeStepsH p (refineContractK K env) 30122 ω μ2 x t ω' μ' x
        (4100 * n + (2000 + growGas) * off enc n + 400 + growGas) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap' ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 ptr' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (pre.length + off enc n + 2) ∧
      BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s0 μ0 (pre ++ out enc n ++ μ0.readN (Wi + 24) 2) cap' ptr' s' μ5 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ5.read a) ∧
      (∀ a, μ'.readable a = μ5.readable a) ∧ (∀ a, μ'.writable a = μ5.writable a)) ∨
    ExhaustsW env K pb p P 30122 ω μ2 x (4100 * n + (2000 + growGas) * off enc n + 400 + growGas) := by
  have hM := L.fr.hF2; have hM8 := L.fr.hF8; have hvS := L.fr.hvS1; have hS1 := L.H.hS1; have h80 := L.hM80
  have hFS0 := L.fr.hFS0
  have hon := off_le enc 0 n; simp only [Nat.zero_add] at hon
  -- the first element
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c16, cfr, crd, cwr⟩ := tA (p := p) (P := P)
    (R := refineContractK K env) x ω μ2 M E n (by omega)
    (by obtain ⟨e, he, heu, -, -, h2⟩ := L.arr; have := chunk_in L.H.wf he heu; have := L.H.hbT; omega)
    ⟨hn.1, by omega⟩ b1 b5
    (by rw [Memory.readN_congr (fun j hj => lowfr _ (by omega) (by omega))]; exact s16)
    (fun a h1 h2 => Memory.readable_of_writable (W.H.st a (by omega) (by omega)))
    (fun a h1 h2 => W.H.st a (by omega) (by omega))
  have W3 := W.frame (M + 16) (M + 24) (by omega) (by omega) (Or.inl (by omega)) cfr crd cwr
  have st0 : WMH env pb S0 S1 M E n buf s0 μ0 pre enc 0 ω3 μ3 :=
    { h0 := c0, h1 := c1, h5 := by rw [c5, b5]; simp, h6 := by rw [c6, b6]; simp,
      h7 := by simpa using c7, h8 := c8, s16 := by simpa using c16,
      lowfr := fun a h1 h2 => by rw [cfr a (by omega) (by omega)]; exact lowfr a h1 (by omega),
      buf := ⟨_, _, _, W3.cast (by simp [out])⟩ }
  -- the elements
  rcases loopMH (p := p) (P := P) x μ0 L (by omega) s8 hWi hWiM hWs n 0 ω3 μ3 (by omega) hn.1 st0 with
    ⟨ω4, μ4, run4, fin⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run3 hx).mono (by unfold growGas; simp only [Nat.sub_zero, off] at *; omega))
  obtain ⟨cap4, ptr4, s4, W4⟩ := fin.buf
  have hl4 : (pre ++ out enc n).length = pre.length + off enc n := by simp [length_out]
  -- `work_item_index`
  rcases extendH env K hK1 hK x ω4 μ4 W4 M (M + 52) 2 1420 30250 ⟨by omega, by omega, hM8⟩ (by omega) (by omega)
      L.fr.hS1 fin.h0 fin.h1 fin.h7 fin.h8 fin.h9 ⟨by decide, by decide, by decide⟩ jte_709 bs_30250
      (by rw [hl4]; omega) (Or.inr (Or.inl ⟨by omega, by omega, Or.inr (by omega)⟩)) with
    ⟨cap5, ptr5, s5, ω5, μ5, run5, e0, e1, e5, e6, W5, k5⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run3.trans run4) hx).mono
      (by unfold stepGas growGas; simp only [off, Nat.sub_zero] at *; omega))
  rw [fin.w52] at W5
  have hl5 : 0 + (pre ++ out enc n ++ μ0.readN (Wi + 24) 2).length = pre.length + off enc n + 2 := by
    simp [length_out, Memory.readN]; omega
  have k5M : ∀ a, M + 56 ≤ a → a < M + 80 → μ5.read a = μ0.read a := fun a h1 h2 =>
    W5.hi a (by omega) h1 (Or.inr (by omega))
  have k5lo : ∀ a, M ≤ a → a < M + 16 → μ5.read a = μ0.read a := fun a h1 h2 =>
    (k5 a (by omega) h1 (Or.inl (by omega))).trans (fin.lowfr a h1 h2)
  -- the result, and the return
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fc, fp, fl, ffr, frd, fwr⟩ := t5 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 M O cap5 ptr5 (pre.length + off enc n + 2) ret t r5 r6 (by omega)
    (by omega) hOM e1
    (by rw [Memory.readN_congr (fun j hj => k5lo _ (by omega) (by omega))]; exact s0')
    W5.vc W5.vp (by rw [← hl5]; exact W5.vl)
    (by rw [Memory.readN_congr (fun j hj => k5M _ (by omega) (by omega))]; exact sr)
    (by rw [Memory.readN_congr (fun j hj => k5M _ (by omega) (by omega))]; exact s5)
    (by rw [Memory.readN_congr (fun j hj => k5M _ (by omega) (by omega))]; exact s6)
    (by have := W5.cb; unfold capBound at this; omega) (by have := W5.buf_lt; omega) (by omega) hr5 hr6 hret hjt hbt
    (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
    (fun a h1 h2 => W5.H.st a (by omega) (by omega))
  exact Or.inl ⟨cap5, ptr5, s5, ω6, μ5, μ6,
    (run3.trans (run4.trans (run5.trans run6))).mono
      (by unfold stepGas growGas; simp only [off, Nat.sub_zero] at *; omega),
    f0, f1, f5, f6, fc, fp, fl, W5, ffr, frd, fwr⟩

end

/-- `LayLMH` survives writes to the encoder's frame [M + 24, M + 56) that keep the access. -/
theorem LayLMH.congr {env : RefineHost.Env} {K pb S0 S1 : Nat} {P : Program} {p : ByteArray}
    {M E n buf cap : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Nat → Prop} {s0 : State} {μ0 μ1 : Memory}
    (L : LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s0 μ0)
    (hk : ∀ a, a < 4294967296 → (a < M + 24 ∨ M + 56 ≤ a) → μ1.read a = μ0.read a)
    (hrd : ∀ a, μ1.readable a = μ0.readable a) (hwr : ∀ a, μ1.writable a = μ0.writable a) :
    LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s0 μ1 := by
  have hM := L.fr.hF2
  have kl : ∀ a, a < 2147483648 → μ1.read a = μ0.read a := fun a h => hk a (by omega) (Or.inl (by omega))
  refine { L with H := ctx_high L.H kl hwr, rep0 := fun j hj => ?_,
    tab := by rw [Memory.readN_congr (fun j hj => kl _ (by omega))]; exact L.tab,
    rtab := fun a h1 h2 => by rw [hrd]; exact L.rtab a h1 h2 }
  obtain ⟨e, he, heu, -, h1, h2⟩ := L.arr
  have := chunk_in L.H.wf he heu; have := L.H.hbT
  rw [Memory.readN_congr (fun j' hj' => kl _ (by omega))]
  refine L.rcong j hj _ μ0 μ1 (fun q m hs => ?_) (L.rep0 j hj)
  have hs' := L.hsrc j hj q m hs
  rcases hs' with ⟨b1, b2, b3⟩ | ⟨e', he', heu', -, b1, b2⟩
  · exact Memory.readN_congr (fun j' hj' => hk _ (by have := L.H.hS1; omega) (Or.inr (by omega)))
  · have := chunk_in L.H.wf he' heu'
    exact Memory.readN_congr (fun j' hj' => kl _ (by omega))

/-- The gas of the encoder with growth. -/
def bigGasH (n off : Nat) : Nat :=
  4100 * n + (2000 + growGas) * off + 2500 + growGas * ((Blob.encodeNat n).length + 1)

/-- **Refine's output encoder, for `EncOkMH` elements, with growth** (30073): for 0 < n < 2^32 instructions
    at E (in an allocated chunk), each encoding to `enc j` by `EncOkMH 232`, and the writer's buffer `buf`
    an allocated chunk of capacity cap (no room assumed; twice the output within `capBound`), either the
    encoder writes ℰ(n) (GP v0.8.0 Appendix C), the n encodings and the work item's 2-octet
    `work_item_index` into the (possibly regrown) buffer, stores the result `{cap', ptr', |output|}` at O
    and returns to `ret`, the memory μ5 before the store being `BufH` from the entry memory for that
    output (the buffer an allocated chunk of the final allocator state, the context kept, the other
    allocated chunks and memory at or above M + 56 kept but for the writer); or the run reaches a failed
    allocator call (`ExhaustsW`). -/
theorem encode_okMH_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 M E n buf cap Wi : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Nat → Prop} {s : State}
    (L : LayLMH env K pb S0 S1 P p M E n buf cap enc rep src s μ) (O ret t r5 r6 : Nat)
    (hn : 0 < n ∧ n < 4294967296)
    (hbig : 2 * ((Blob.encodeNat n).length + off enc n + 2) ≤ capBound)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h6 : ω[6] = UInt64.ofNat (232 * n))
    (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 Wi)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n) (sE : μ.readN (Wi + 8) 8 = Num.encodeLE 8 E)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hWi : Wi + 26 ≤ 4294967296) (hWiM : Wi + 16 ≤ M ∨ M + 80 ≤ Wi)
    (rWi : ∀ a, Wi + 8 ≤ a → a < Wi + 16 → μ.readable a = true)
    (hWs : SafeR s buf (M + 56) S1 (M + 24) (Wi + 24) 2)
    (hO : S0 ≤ O ∧ O + 24 ≤ S1) (hOM : O + 24 ≤ M + 56 ∨ M + 80 ≤ O) :
    (∃ cap' ptr' s' ω' μ5 μ', FreeStepsH p (refineContractK K env) 30073 ω μ x t ω' μ' x (bigGasH n (off enc n)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap' ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 ptr' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 ((Blob.encodeNat n).length + off enc n + 2) ∧
      BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s μ (Blob.encodeNat n ++ out enc n ++ μ.readN (Wi + 24) 2)
        cap' ptr' s' μ5 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ5.read a) ∧
      (∀ a, μ'.readable a = μ5.readable a) ∧ (∀ a, μ'.writable a = μ5.writable a)) ∨
    ExhaustsW env K pb p P 30073 ω μ x (bigGasH n (off enc n)) := by
  have hM := L.fr.hF2; have hM8 := L.fr.hF8; have hvS := L.fr.hvS1; have hS1 := L.H.hS1; have h80 := L.hM80
  have hFS0 := L.fr.hFS0
  have hst := L.H.st
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := L.chunk
  have hci := chunk_in L.H.wf hc hcu
  have hb0 := L.H.hb0; have hbT := L.H.hbT
  have cb := L.cb; unfold capBound at cb
  obtain ⟨e, he, heu, -, hE1, hE2⟩ := L.arr
  have hei := chunk_in L.H.wf he heu
  -- the prologue and the count
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, ac, ap, al, a52, afr, ard, awr⟩ := t1 (p := p) (P := P)
    (R := refineContractK K env) x ω μ M buf cap Wi E n (by omega) ⟨by omega, by omega⟩ (by omega) hn.2 h1 h5 h7
    s8 s16 (by omega) (by omega) sE (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega))) rWi
    (fun a h1 h2 => hst a (by omega) (by omega))
  have L1 := L.congr afr ard awr
  have W1 : BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s μ1 [] cap buf s μ1 :=
    BufH.init (by omega) ac ap al (by omega) L.cpos L.cb L1.H ⟨c, hc, hcu, hcp, hcc⟩
  -- the length prefix
  rcases prefix_anyH K hK1 hK x ω1 μ1 W1 M (M + 52) 1416 30122 E (232 * n) n ⟨by omega, by omega, hM8⟩
      (by omega) (by omega) L.fr.hS1 a0 a1 a5 (by rw [a6, h6]) a7 a8 (by omega) (by omega) (by omega)
      (Or.inr (by omega)) a52 (fun a h1 h2 => Memory.readable_of_writable (L1.H.st a (by omega) (by omega)))
      ⟨by decide, by decide, by decide⟩ jte_707 bs_30122 (by simp; omega) with
    ⟨cap2, ptr2, s2, ω2, μ2, run2, b0, b1, b5, b6, W2, k2⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run1 hx).mono (by unfold prefixGas bigGasH growGas; omega))
  have kM : ∀ a, a < 4294967296 → (a < M + 24 ∨ M + 56 ≤ a) → M ≤ a → μ2.read a = μ.read a := fun a h0 h1 h2 =>
    (k2 a h0 h2 (by omega)).trans (afr a h0 h1)
  rcases restMH (p := p) (P := P) x ω2 μ1 μ2 L1 hK1 hK (by simp; omega) O ret t r5 r6 hn b1 b5 b6
      (W2.cast (by simp)) (fun a h1 h2 => k2 a (by omega) h1 (Or.inl h2))
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact s8)
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact s16)
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact sr)
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; exact s6)
      hr5 hr6 hret hjt hbt hWi hWiM hWs hO hOM with
    ⟨cap', ptr', s', ω', μ5, μ', run3, f0, f1, f5, f6, fc, fp, fl, W5, ffr, frd, fwr⟩ | hx
  · -- the memory before t1 (μ) and after it (μ1) agree outside [M + 24, M + 56)
    have hw : (Blob.encodeNat n ++ out enc n ++ μ1.readN (Wi + 24) 2) =
        Blob.encodeNat n ++ out enc n ++ μ.readN (Wi + 24) 2 := by
      rw [Memory.readN_congr (fun j hj => afr _ ?_ ?_)]
      · rcases hWs with ⟨b1, b2, b3⟩ | ⟨e', he', heu', -, b1, b2⟩
        · omega
        · have := chunk_in L.H.wf he' heu'; omega
      · rcases hWs with ⟨b1, b2, b3⟩ | ⟨e', he', heu', -, b1, b2⟩
        · omega
        · have := chunk_in L.H.wf he' heu'; omega
    have kl : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h => afr a (by omega) (Or.inl (by omega))
    have W6 : BufH env pb S0 S1 (M + 56) (M + 24) 0 buf s μ (Blob.encodeNat n ++ out enc n ++ μ.readN (Wi + 24) 2)
        cap' ptr' s' μ5 :=
      { W5.cast hw with
        out := by rw [← hw, W5.out]; simp [Memory.readN]
        others := fun e he heu hne => by
          obtain ⟨g1, g2, g3⟩ := W5.others e he heu hne
          refine ⟨g1, g2, fun a ha => ?_⟩
          have := chunk_in L.H.wf he heu
          unfold InData at ha
          rw [g3 a ⟨ha.1, ha.2⟩, kl a (by omega)]
        acc := fun a ha => by rw [← ard, ← awr]; exact W5.acc a ha
        low := fun a ha => by rw [W5.low a ha, kl a (by omega)]
        glob := fun a ha => by have hg := ha; unfold Glob at hg; rw [W5.glob a ha, kl a (by omega)]
        hi := fun a h0 h1 h2 => by rw [W5.hi a h0 h1 h2, afr a h0 (Or.inr h1)] }
    exact Or.inl ⟨cap', ptr', s', ω', μ5, μ', (run1.trans (run2.trans run3)).mono
      (by unfold prefixGas bigGasH growGas; omega), f0, f1, f5, f6, fc, fp, by simpa using fl, W6, ffr, frd, fwr⟩
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold prefixGas bigGasH growGas; omega))

end Services.Bootstrap.Encode.GrowH
