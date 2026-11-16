import Services.Bootstrap.Refine.ExitEnc
import Services.Bootstrap.Encode.EncMHLoop

/-!
# Refine's exit: the output encoded, with growth

`ExitEnc.enc_run` with `Encode.GrowH.encode_okMH_big` for the encoder: the elements are `EncOkMH 232` (an element may
read heap octets outside its slot, `src`, and its encoding may be longer than 232 octets), and the writer's buffer of
232 n + 6 octets may be regrown on the way. The size bounds `hcapB` (the first buffer within `capBound`) and `hbig`
(twice the output within `capBound`) are internal to T1 until the big-`realloc` path is proved (`ReallocBig`).
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.ExitEncH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc Services.Bootstrap.Encode.WriterGrow
  Services.Bootstrap.Encode.GrowH Services.Bootstrap.Refine.ExitEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The writer's failed allocator calls (`ExhaustsW`) are `ExhaustsX`. -/
theorem ExhaustsX.ofW {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat} {ω : Regs}
    {μ : Memory} {x : RefineCtx} {n : Nat} (h : ExhaustsW env cap pb p P i ω μ x n) :
    PassLoop.ExhaustsX env cap pb p i ω μ x n := by
  obtain ⟨ω', μ', j, run, e7, ha⟩ := h
  refine ⟨ω', μ', x, j, run, Or.inl ⟨?_, e7⟩⟩
  rcases ha with (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩ <;> decide

/-- An allocated chunk has a positive size. -/
theorem size_pos {s : State} (hwf : WF s) {d : Chunk} (hd : d ∈ chunks s) : 0 < d.size := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  exact (ht.mem_lt d hd).2.2

/-- An allocated chunk's data lies below 2^31. -/
theorem data_lo' {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State} (H : HeapCtx env pb S0 S1 μ s)
    {d : Chunk} (hd : d ∈ chunks s) (hu : d.used = true) {a : Nat} (ha : InData d a) : a < 2147483648 := by
  have := Decode.VecU8.chunk_in H.wf hd hu
  have := H.hbT
  unfold InData at ha
  omega

/-- **The output encoded, with growth** (6209 … 6295): `ExitEnc.enc_run` for `EncOkMH 232` elements (slot j satisfying
    `rep j` in memory, which depends on memory only through the octets `src j`, lying in allocated chunks). The encoder
    leaves `{cap', buf, |ℰ|}` at M + 272, the octets ℰ(n) ++ out enc n ++ ℰ₂(w mod 2^16) at buf, the data of an allocated
    chunk `cb` (of capacity ≥ |ℰ|) that no allocated chunk of s is; every allocated chunk of s stays with its data.
    Internal size bounds: `hcapB`, `hbig`. Or an allocation fails (`ExhaustsX`). -/
theorem enc_runH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [Services.Bootstrap.CodeA.HasCodeA p P]
    (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) {pb S0 S1 : Nat} (H : HeapCtx env pb S0 S1 μ s) (M cap E n w : Nat) (c : Chunk)
    (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Memory → Prop) (src : Nat → Nat → Nat → Prop)
    (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484384 ≤ M ∧ M % 8 = 0) (hn : 0 < n ∧ n ≤ 16777216) (hS1' : S1 + 16 < 4294967296)
    (hcapB : 232 * n + 6 ≤ capBound) (hbig : 2 * ((Blob.encodeNat n).length + off enc n + 2) ≤ capBound)
    (hcap : cap < 18446744073709551616) (hw64 : w < 18446744073709551616)
    (hc : c ∈ chunks s ∧ c.used = true ∧ c.addr + 32 ≤ E ∧ E + 232 * n ≤ c.addr + 32 * c.size)
    (h1 : ω[1] = UInt64.ofNat M)
    (s248 : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (s256 : μ.readN (M + 256) 8 = Num.encodeLE 8 E)
    (s264 : μ.readN (M + 264) 8 = Num.encodeLE 8 n) (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w)
    (hok : ∀ j, j < n → EncOkMH env cap0 pb p P 232 (enc j) (rep j) (src j))
    (hrep : ∀ j, j < n → rep j (μ.readN (E + 232 * j) 232) μ)
    (hrc : ∀ j, j < n → ∀ (bs : List UInt8) (μ μ' : Memory),
      (∀ q m, src j q m → μ'.readN q m = μ.readN q m) → rep j bs μ → rep j bs μ')
    (hsrc : ∀ j, j < n → ∀ q m, src j q m →
      ∃ e ∈ chunks s, e.used = true ∧ e.addr + 32 ≤ q ∧ q + m ≤ e.addr + 32 * e.size)
    (tab : μ.readN 67376 100 = table) (rtab : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    (∃ s' ω' μ' cap' buf N, FreeStepsH p (refineContractK cap0 env) 6209 ω μ x 6295 ω' μ' x N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 cap' ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (M + 288) 8 = Num.encodeLE 8 ((Blob.encodeNat n).length + off enc n + 2) ∧
      μ'.readN buf ((Blob.encodeNat n).length + off enc n + 2) =
        Blob.encodeNat n ++ out enc n ++ Num.encodeLE 2 (w % 65536) ∧
      (∃ cb ∈ chunks s', cb.used = true ∧ cb.addr + 32 = buf ∧
        (Blob.encodeNat n).length + off enc n + 2 ≤ 32 * (cb.size - 1) ∧
        ∀ d ∈ chunks s, d.used = true → d ≠ cb) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 194 ≤ a) → (a < M + 272 ∨ M + 296 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 E ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 n) ∨
    ∃ N, PassLoop.ExhaustsX env cap0 pb p 6209 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  obtain ⟨hcs, hcu, hcE0, hcE1⟩ := hc
  have hS1 := H.hS1
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcs hcu
  have wst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a168, a176, a184, a192, a80, a72, a64, a8', a16, a24, afr, ard,
      awr⟩ := en1 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M cap E n w ⟨by omega, by omega, hM8⟩
    hcap (by omega) (by omega) hw64 h1 s248 s256 s264 s80
    (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega)))
    (fun a h1 h2 => wst a (by omega) (by omega)) (fun a h1 h2 => wst a (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s :=
    Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (by omega) (by omega)) awr
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω1 μ1 s (M - 80) (232 * n + 6) 1 pb S0 S1
      H1 a1 a7 a8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨buf, s2, ω2, μ2, ha, run2, H2, keep2, hnew, fresh2, hk2, b7, stk2, b0, b1, b5, b6⟩ | ⟨hna, ω2, μ2, run2, b7, -⟩
  rotate_left
  · exact Or.inr ⟨_, ω2, μ2, x, 40611, run1.trans run2, Or.inl ⟨by decide, b7⟩⟩
  -- `alloc`'s return into the encoder
  have run3 := alloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω2 μ2 (b0.trans a0)
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
  simp only at hq0 hqT
  have hb0' := H2.hb0
  have hbT' := H2.hbT
  have hcs2 := keep2 c hcs hcu
  have hcne := fresh2 c hcs hcu
  have hap := PassLoop.chunk_apart H2.wf hcs2 hnew hcne
  simp only at hap
  -- what the runs so far keep
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd (run1.trans run2)
  have dat : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ2.read a = μ.read a := fun d hd hu a ha => by
    obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
    have hd2 := keep2 d hd hu
    unfold InData at ha
    rw [hk2.hkeep a (Alloc.off_hdr_data H2.wf H2.hb0 H2.hbT hd2 ha.1 ha.2),
      afr a (by omega) (by omega) (by omega)]
  have stk : ∀ a, a < 4294967296 → M - 80 ≤ a → μ2.read a = μ1.read a := fun a h0 h1 => stk2 a h0 h1
  -- an allocated chunk of s is not the new buffer's: its data starts elsewhere
  have apart : ∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ buf := fun e he heu => by
    have hsz := size_pos H.wf he
    have hap' := PassLoop.chunk_apart H2.wf (keep2 e he heu) hnew (fresh2 e he heu)
    simp only at hap'
    omega
  have L : LayLMH env cap0 pb S0 S1 P p (M - 80) E n buf (232 * n + 6) enc rep src s2 μ2 :=
    { fr := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      hM80 := by omega
      arr := ⟨c, hcs2, hcu, by omega, by omega, by omega⟩
      cpos := by omega
      cb := hcapB
      H := H2
      chunk := ⟨_, hnew, rfl, by simp; omega, by simp; omega⟩
      ok := hok
      rep0 := fun j hj => by
        refine hrc j hj _ μ μ2 (fun q m h => ?_) ?_
        · obtain ⟨e, he, heu, h1, h2⟩ := hsrc j hj q m h
          exact Memory.readN_congr (fun i hi => dat e he heu _ ⟨by omega, by omega⟩)
        · rw [Memory.readN_congr (fun i hi => dat c hcs hcu _ ⟨by omega, by omega⟩)]; exact hrep j hj
      rcong := hrc
      hsrc := fun j hj q m h => by
        obtain ⟨e, he, heu, h1, h2⟩ := hsrc j hj q m h
        exact Or.inr ⟨e, keep2 e he heu, heu, apart e he heu, h1, h2⟩
      tab := by
        rw [Memory.readN_congr (fun i hi => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
          (H.ro _ (by omega)))]; exact tab
      rtab := fun a h1 h2 => by
        unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]; exact rtab a h1 h2 }
  rcases encode_okMH_big (p := p) (P := P) env cap0 hcap1 hcap0 x ω2 μ2 L (M + 272) 204 6295 ω[5].toNat ω[6].toNat
      ⟨hn.1, by omega⟩ hbig
      (by rw [b1, a1]) (by rw [b5, a5]) (by rw [b6, a6]) b7
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a80)
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a72)
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a64)
      (by rw [show M + 168 + 8 = M + 176 by omega,
        Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a176)
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a8')
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a16)
      (by rw [Memory.readN_congr (fun i hi => stk _ (by omega) (by omega))]; exact a24)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) ⟨by decide, by decide, by decide⟩ jte_101 bs_6295
      (by omega) (Or.inr (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      (Or.inl ⟨by omega, by omega, Or.inr (by omega)⟩) ⟨by omega, by omega⟩ (Or.inr (by omega)) with
    ⟨cap', ptr', s', ω4, μ5, μ4, run4, d0, d1, d5, d6, dO, dO8, dO16, W, dfr, drd, dwr⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.ofW (ExhaustsW.pre ((run1.trans run2).trans run3) hx)⟩
  have hpre : (Blob.encodeNat n ++ out enc n ++ μ2.readN (M + 168 + 24) 2) =
      Blob.encodeNat n ++ out enc n ++ Num.encodeLE 2 (w % 65536) := by
    rw [show M + 168 + 24 = M + 192 by omega, Memory.readN_congr (fun i hi => stk _ (by omega) (by omega)), a192]
  have hlenp : (Blob.encodeNat n ++ out enc n ++ Num.encodeLE 2 (w % 65536)).length =
      (Blob.encodeNat n).length + off enc n + 2 := by
    simp [length_out, Num.encodeLE]; omega
  rw [hpre] at W
  obtain ⟨hp0, hp1⟩ := W.buf_lt
  have hroom := W.room
  rw [hlenp] at hroom
  have W4 : ∀ a, a < 4294967296 → (a < M + 272 ∨ M + 296 ≤ a) → μ4.read a = μ5.read a := fun a h0 h => dfr a h0 h
  have H4 : HeapCtx env pb S0 S1 μ4 s' := Decode.GrowOne.ctx_high W.H (fun a ha => W4 a (by omega) (Or.inl (by omega)))
    (fun a => dwr a)
  have hi5 : ∀ a, a < 4294967296 → M - 24 ≤ a → μ5.read a = μ2.read a := fun a h0 h =>
    W.hi a h0 (by omega) (Or.inr (by omega))
  obtain ⟨cb, hcb, hcbu, hcba, hcbc⟩ := W.chunk
  refine Or.inl ⟨s', ω4, μ4, cap', ptr', _, (run1.trans run2).trans (run3.trans run4), H4,
    by rw [d1]; congr 1; omega, dO, dO8, dO16, ?_, ⟨cb, hcb, hcbu, hcba, ?_, fun d hd hu => ?_⟩,
    fun a h0 h1 h2 h3 => ?_, fun d hd hu => ?_, ?_, ?_, ?_⟩
  · have e := W.out
    rw [Nat.zero_add, show μ2.readN buf 0 = [] by simp [Memory.readN], List.nil_append] at e
    rw [← hlenp, Memory.readN_congr (fun i hi => W4 _ (by omega) (Or.inl (by omega)))]
    exact e
  · omega
  · intro e
    subst e
    exact (W.others d (keep2 d hd hu) hu (apart d hd hu)).2.1 hcba
  · rw [W4 a h0 h3, hi5 a h0 (by omega), stk a h0 (by omega), afr a h0 (Or.inr h1) h2]
  · obtain ⟨hd', -, kd'⟩ := W.others d (keep2 d hd hu) hu (apart d hd hu)
    refine ⟨hd', fun a ha => ?_⟩
    have hdl := data_lo' H hd hu ha
    rw [W4 a (by omega) (Or.inl (by omega)), kd' a ha, dat d hd hu a ha]
  · rw [show μ4.readN (M + 168) 8 = μ1.readN (M + 168) 8 from Memory.readN_congr (fun i hi => by
      rw [W4 _ (by omega) (Or.inl (by omega)), hi5 _ (by omega) (by omega), stk _ (by omega) (by omega)])]
    exact a168
  · rw [show μ4.readN (M + 176) 8 = μ1.readN (M + 176) 8 from Memory.readN_congr (fun i hi => by
      rw [W4 _ (by omega) (Or.inl (by omega)), hi5 _ (by omega) (by omega), stk _ (by omega) (by omega)])]
    exact a176
  · rw [show μ4.readN (M + 184) 8 = μ1.readN (M + 184) 8 from Memory.readN_congr (fun i hi => by
      rw [W4 _ (by omega) (Or.inl (by omega)), hi5 _ (by omega) (by omega), stk _ (by omega) (by omega)])]
    exact a184

end Services.Bootstrap.Refine.ExitEncH
