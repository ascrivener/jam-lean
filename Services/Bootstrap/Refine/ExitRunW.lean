import Services.Bootstrap.Refine.ExitRun
import Services.Bootstrap.Refine.ExitEncH
import Services.Bootstrap.Refine.FinW

/-!
# Refine's exit, whole, with every heap element

`ExitRunH.exit_runH` over the wider `DropVecW.HeapElW`: `ExitRun.exit_run` where an output element may own heap memory: the encoder is `ExitEncH.enc_runH` (elements
`EncOkMH 232`, reading heap octets `src`, the writer regrown as needed), and the drop is `FinW.fin_runW` (an element is
of a variant whose drop does nothing, or a heap element owning the chunks `own j`, `HeapElW`). The
output's slots are described at the loop's end state directly, the output buffer being at Eo (from M + 256). The owned
chunks and the heap octets read are chunks the loop keeps (`Kp`, not the input's chunk `ce`).
Internal hypotheses (until `ReallocBig`): `hcapB`, `hbig`; and the frame bounds `2147484384 ≤ M`, `S1 + 16 < 2^32`.
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.ExitRunW

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B Services.Bootstrap.CodeT1C
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.ExitRun Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Refine's exit, with heap elements** (5042 … t): `ExitRun.exit_run` where output slot j (at Eo + 232 j) satisfies
    `rep j` (with memory) for the encoder (`EncOkMH 232` to `enc j`) and `DR j` for the `Debug` line, both depending on
    memory only through the octets `src j` (in chunks the loop keeps), and is of a variant whose drop does nothing or a
    heap element (`HeapElW`) owning `own j` (kept chunks, disjoint between slots). Refine returns ℰ(`BootstrapWorkOutput`) as in
    `exit_run`, or an allocation fails. -/
theorem exit_runW {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] [HasCodeT1C p P]
    [Services.Bootstrap.CodeA.HasCodeA p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb : Nat}
    {pb S0 S1 M E n capI : Nat} {ce : Chunk} {μ0 : Memory} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop}
    (DR : Nat → List UInt8 → Memory → Prop) (enc : Nat → List UInt8) (rep : Nat → List UInt8 → Memory → Prop)
    (src : Nat → Nat → Nat → Prop) (own : Nat → Chunk → Prop)
    {ro : List UInt8} (dbg : DebugLineOk p cap0 env pb S0 S1 ro DR)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (hro : RoData.RoIs ro μ) (L : LayP S0 S1 M E n ce) (hn : 0 < n)
    (hM' : 2147484384 ≤ M) (hS1' : S1 + 16 < 4294967296)
    (hcapB : 232 * n + 6 ≤ capBound) (hbig : 2 * ((Blob.encodeNat n).length + off enc n + 2) ≤ capBound)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 n ω μ s) (hcapI : 232 * capI < 18446744073709551616)
    (Eo : Nat) (hEo64 : Eo < 18446744073709551616) (hEo : μ.readN (M + 256) 8 = Num.encodeLE 8 Eo)
    (hDR : ∀ j, j < n → DR j (μ.readN (Eo + 232 * j) 232) μ)
    (hrep : ∀ j, j < n → rep j (μ.readN (Eo + 232 * j) 232) μ)
    (hok : ∀ j, j < n → EncOkMH env cap0 pb p P 232 (enc j) (rep j) (src j))
    (hrc : ∀ j, j < n → ∀ (bs : List UInt8) (μ μ' : Memory),
      (∀ q m, src j q m → μ'.readN q m = μ.readN q m) → rep j bs μ → rep j bs μ')
    (hDRc : ∀ j, j < n → ∀ (bs : List UInt8) (μ μ' : Memory),
      (∀ q m, src j q m → μ'.readN q m = μ.readN q m) → DR j bs μ → DR j bs μ')
    (hsrc : ∀ j, j < n → ∀ q m, src j q m → ∃ e, Kp e ∧ e ≠ ce ∧ e.addr + 32 ≤ q ∧ q + m ≤ e.addr + 32 * e.size)
    (hownK : ∀ j d, j < n → own j d → Kp d ∧ d ≠ ce)
    (hown : ∀ j j' d, j < n → j' < n → j ≠ j' → own j d → own j' d → False)
    (hV : ∀ j, j < n → (∃ t, DropOut.NoDrop t ∧ μ.readN (Eo + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨
      HeapElW μ s (Eo + 232 * j) (own j))
    (w c' q ret r5 r6 t : Nat) (cq : Chunk) (hw64 : w < 18446744073709551616)
    (s80 : μ0.readN (M + 80) 8 = Num.encodeLE 8 w)
    (s88 : μ0.readN (M + 88) 8 = Num.encodeLE 8 c') (s112 : μ0.readN (M + 112) 8 = Num.encodeLE 8 q)
    (s624 : μ0.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ0.readN (M + 616) 8 = Num.encodeLE 8 r5)
    (s608 : μ0.readN (M + 608) 8 = Num.encodeLE 8 r6)
    (hq' : c' < 18446744073709551616) (hcq : c' ≠ 0 → Kp cq ∧ cq.addr + 32 = q ∧ cq ≠ ce)
    (hocq : c' ≠ 0 → ∀ j, j < n → ¬ own j cq)
    (hret : Fin.RetTo P ret t) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (tab : μ.readN 67376 100 = table) (rtab : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 5042 ω μ x t ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = UInt64.ofNat buf ∧
      ω'[8] = UInt64.ofNat ((Blob.encodeNat n).length + off enc n + 2) ∧
      μ'.readN buf ((Blob.encodeNat n).length + off enc n + 2) =
        Blob.encodeNat n ++ out enc n ++ Num.encodeLE 2 (w % 65536) ∧
      ((∀ a, buf ≤ a → a < buf + ((Blob.encodeNat n).length + off enc n + 2) → μ'.readable a = true) ∧
        buf + ((Blob.encodeNat n).length + off enc n + 2) < 2147483648)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5042 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn' := L.hn
  obtain ⟨hE0, hE1⟩ := L.hE
  have hEtop := L.hEtop
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  have hpE : Eo = ptr := by rw [← rd8 (by omega) vp, rd8 hEo64 hEo]
  subst hpE
  obtain ⟨co, hco, hcoa, hcou, hcos, hcoe, hcok⟩ := hold.resolve_left (fun h => by omega)
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in st.H.wf hco hcou
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have hcs : 232 * cap + 32 ≤ 32 * co.size := by rw [hcos]; omega
  -- 1. the loop's end
  obtain ⟨ω1, run1, a1, -, -⟩ := Exit.ex0 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M (E + 232 * n)
    (by omega) (by omega) st.h1 st.cur42 st.en
    (fun a h1 h2 => Memory.readable_of_writable (st.H.st a (by omega) (by omega)))
  -- 2. the input's `IntoIter` dropped
  obtain ⟨ω2, μ2, s2, run2, H2, -, -, b1, -, -, bfr, bkeep⟩ := Exit.drop (p := p) (P := P)
    (R := refineContractK cap0 env) env x ω1 μ s M (ce.addr + 32) (E + 232 * n) capI ce st.H
    ⟨by omega, by omega, by omega, hM8⟩ (by omega) (by omega) hcapI (fun _ => ⟨st.hce.1, st.hce.2, rfl⟩)
    (a1.trans st.h1) st.i0 st.i8 st.i16 st.i24
  have co2 := bkeep co hco hcou (fun _ => hcoe)
  -- 3. the `Debug` line's setup
  obtain ⟨ω3, μ3, run3, c0, c1, -, -, c7, c8, c9, c272, c280, cfr, crd, cwr⟩ := Exit.ex1 (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 M ⟨by omega, by omega, hM8⟩ b1
    (fun a h1 h2 => H2.st a (by omega) (by omega))
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := Decode.GrowOne.ctx_high H2 (fun a ha => cfr a (by omega) (by omega)) cwr
  have k3 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 272 ∨ M + 288 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => by rw [cfr a h0 h2, bfr a h0 h1]
  have sl3 : ∀ a, InData co a → μ3.read a = μ.read a := fun a ha => by
    unfold InData at ha
    rw [cfr a (by omega) (by omega), co2.2 a ha]
  -- the kept chunks, through the first three pieces
  have kd3 : ∀ d, Kp d → d ≠ ce → d ∈ chunks s2 ∧ d.used = true ∧ ∀ a, InData d a → μ3.read a = μ.read a :=
    fun d hK hne => by
      obtain ⟨hd, hu, -⟩ := st.kp d hK
      obtain ⟨hd2, kd2⟩ := bkeep d hd hu (fun _ => hne)
      obtain ⟨-, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hd hu
      refine ⟨hd2, hu, fun a ha => ?_⟩
      unfold InData at ha
      rw [cfr a (by omega) (by omega), kd2 a ⟨ha.1, ha.2⟩]
  have src3 : ∀ j, j < n → ∀ q m, src j q m → μ3.readN q m = μ.readN q m := fun j hj q m h => by
    obtain ⟨e, hK, hne, h1, h2⟩ := hsrc j hj q m h
    exact Memory.readN_congr (fun i hi => (kd3 e hK hne).2.2 _ ⟨by omega, by omega⟩)
  have pre3 := run1.trans (run2.trans run3)
  -- 4. the `Debug` line
  rcases dbg x ω3 μ3 s2 M cap Eo n H3 (RoData.RoIs.keep st.H pre3 hro) (by omega) (by omega) hM8 c0 c1 c7 c8 c9 c272
      c280
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vc)
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vp)
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega))]; exact vl)
      (fun j hj => by
        rw [Memory.readN_congr (fun i hi => sl3 _ ⟨by omega, by omega⟩)]
        exact hDRc j hj _ μ μ3 (src3 j hj) (hDR j hj))
      (Or.inr ⟨co, co2.1, hcou, fun k hk => ⟨by omega, by omega⟩⟩) with
    ⟨ω4, μ4, s4, N4, run4, H4, d1, dfr, dkeep⟩ | ⟨N4, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre pre3 hx⟩
  have co4 := dkeep co co2.1 hcou
  have k4 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 192 ≤ a) → (a < M + 272 ∨ M + 288 ≤ a) →
      μ4.read a = μ.read a := fun a h0 h1 h2 h3 => by rw [dfr a h0 h1 h2, k3 a h0 h1 h3]
  have sl4 : ∀ a, InData co a → μ4.read a = μ.read a := fun a ha => by rw [co4.2 a ha, sl3 a ha]
  have kd4 : ∀ d, Kp d → d ≠ ce → d ∈ chunks s4 ∧ d.used = true ∧ ∀ a, InData d a → μ4.read a = μ.read a :=
    fun d hK hne => by
      obtain ⟨hd3, hu, kd⟩ := kd3 d hK hne
      obtain ⟨hd4, kd4⟩ := dkeep d hd3 hu
      exact ⟨hd4, hu, fun a ha => by rw [kd4 a ha, kd a ha]⟩
  have src4 : ∀ j, j < n → ∀ q m, src j q m → μ4.readN q m = μ.readN q m := fun j hj q m h => by
    obtain ⟨e, hK, hne, h1, h2⟩ := hsrc j hj q m h
    exact Memory.readN_congr (fun i hi => (kd4 e hK hne).2.2 _ ⟨by omega, by omega⟩)
  have pre4 := pre3.trans run4
  obtain ⟨tab4, rtab4⟩ := ro_keep st.H pre4 (a := 67376) (l := 100) (by omega)
  -- 5. the output encoded
  rcases ExitEncH.enc_runH (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ4 s4 H4 M cap Eo n w co enc rep src
      ⟨by omega, by omega, hM', hM8⟩ ⟨hn, hn'⟩ hS1' hcapB hbig (by omega) hw64
      ⟨co4.1, hcou, by omega, by omega⟩ (d1.trans c1)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vc)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vp)
      (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega))]; exact vl)
      (by rw [show μ4.readN (M + 80) 8 = μ0.readN (M + 80) 8 from Memory.readN_congr (fun j hj => by
        rw [k4 _ (by omega) (by omega) (by omega) (by omega), st.fr _ (by omega)])]; exact s80)
      hok
      (fun j hj => by
        rw [Memory.readN_congr (fun i hi => sl4 _ ⟨by omega, by omega⟩)]
        exact hrc j hj _ μ μ4 (src4 j hj) (hrep j hj))
      hrc
      (fun j hj q m h => by
        obtain ⟨e, hK, hne, h1, h2⟩ := hsrc j hj q m h
        obtain ⟨he, heu, -⟩ := kd4 e hK hne
        exact ⟨e, he, heu, h1, h2⟩)
      (by rw [tab4]; exact tab) (fun a h1 h2 => by rw [rtab4 a h1 h2]; exact rtab a h1 h2) with
    ⟨s5, ω5, μ5, cap5, buf, N5, run5, H5, e1, e272, e280, e288, ebuf, ⟨cb, hcb, hcbu, hcba, hcbs, hcbn⟩, efr, ekeep,
      e168, e176, e184⟩ | ⟨N5, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre pre4 hx⟩
  have co5 := ekeep co co4.1 hcou
  have k5 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 194 ≤ a) → (a < M + 272 ∨ M + 296 ≤ a) →
      μ5.read a = μ.read a := fun a h0 h1 h2 h3 => by
    rw [efr a h0 h1 h2 h3, k4 a h0 h1 (by omega) (by omega)]
  have f5 : ∀ a l, (M + 80 ≤ a ∧ a + l ≤ M + 96) ∨ (M + 112 ≤ a ∧ a + l ≤ M + 120) ∨
      (M + 608 ≤ a ∧ a + l ≤ M + 632) →
      μ5.readN a l = μ0.readN a l := fun a l h => Memory.readN_congr (fun j hj => by
    rw [k5 _ (by omega) (by omega) (by omega) (by omega), st.fr _ (by omega)])
  have sl5 : ∀ a, InData co a → μ5.read a = μ.read a := fun a ha => by rw [co5.2 a ha, sl4 a ha]
  have kd5 : ∀ d, Kp d → d ≠ ce → d ∈ chunks s5 ∧ d.used = true ∧ ∀ a, InData d a → μ5.read a = μ.read a :=
    fun d hK hne => by
      obtain ⟨hd4, hu, kd⟩ := kd4 d hK hne
      obtain ⟨hd5, kd5⟩ := ekeep d hd4 hu
      exact ⟨hd5, hu, fun a ha => by rw [kd5 a ha, kd a ha]⟩
  have pre5 := pre4.trans run5
  have hl4 := ExitEnc.encodeNat_len_le4 n (by omega)
  have hbT5 := H5.hbT
  have hb05 := H5.hb0
  obtain ⟨dtab5, rdtab5⟩ := ro_keep st.H pre5 (a := 67760) (l := 96) (by omega)
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H5.wf hcb hcbu
  have hlen5 := hcbs
  -- the owned chunks are kept chunks, none of them `co`
  have hoco : ∀ j, j < n → ¬ own j co := fun j hj ho => hcok (hownK j co hj ho).1
  -- 6. the epilogue
  obtain ⟨ω6, μ6, s6, N6, run6, H6, f0, f1, f5', f6, f7, f8, ffr, fkeep⟩ := FinW.fin_runW (p := p) (P := P)
    (R := refineContractK cap0 env) env x ω5 μ5 s5 H5 M cap Eo n c' q buf ((Blob.encodeNat n).length + off enc n + 2)
    ret r5 r6 t co cq own
    ⟨by omega, by omega, by omega, hM8⟩ hn hkc ⟨co5.1, hcou, by omega, by omega⟩ (by omega)
    (fun h => by
      obtain ⟨hK, hqa, hqce⟩ := hcq h
      obtain ⟨hq5, hqu, -⟩ := kd5 cq hK hqce
      exact ⟨hq5, hqu, hqa, fun e => hcok (e ▸ hK)⟩)
    hq' hown hoco hocq (by omega) (by omega) e1
    e168 e176 e184 (by rw [f5 _ _ (by omega)]; exact s88) (by rw [f5 _ _ (by omega)]; exact s112) e280 e288
    (by rw [f5 _ _ (by omega)]; exact s624) (by rw [f5 _ _ (by omega)]; exact s616)
    (by rw [f5 _ _ (by omega)]; exact s608) hret hr5 hr6
    (fun j hj => by
      rcases hV j hj with ⟨tj, htj, hD⟩ | hvv
      · refine Or.inl ⟨tj, htj, ?_⟩
        rw [Memory.readN_congr (fun i hi => sl5 _ ⟨by omega, by omega⟩)]; exact hD
      · exact Or.inr (hvv.congr (cb := co) (fun a h1 h2 => ⟨by omega, by omega⟩) sl5
          (fun d hd hu ho => by
            obtain ⟨hK, hne⟩ := hownK j d hj ho
            obtain ⟨hd5, -, kd⟩ := kd5 d hK hne
            exact ⟨hd5, kd⟩)))
    (by rw [dtab5]; exact dtab) (fun a h1 h2 => by rw [rdtab5 a h1 h2]; exact rdtab a h1 h2)
  -- the encoded output, kept by the epilogue
  have hcbco : cb ≠ co := fun e => hcbn co co4.1 hcou e.symm
  have hcbcq : c' ≠ 0 → cb ≠ cq := fun h e => by
    obtain ⟨hK, -, hqce⟩ := hcq h
    obtain ⟨hq4, hqu, -⟩ := kd4 cq hK hqce
    exact hcbn cq hq4 hqu e.symm
  have hcbo : ∀ j, j < n → ¬ own j cb := fun j hj ho => by
    obtain ⟨hK, hne⟩ := hownK j cb hj ho
    obtain ⟨hd4, hu, -⟩ := kd4 cb hK hne
    exact hcbn cb hd4 hu rfl
  obtain ⟨nm, nk⟩ := fkeep cb hcb hcbu hcbco hcbcq hcbo
  refine Or.inl ⟨ω6, μ6, s6, _, buf, pre5.trans run6, H6, f0, f1, f5', f6, f7, f8, ?_, ⟨fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H6 nm hcbu ⟨by omega, by omega⟩), by omega⟩⟩
  rw [Memory.readN_congr (fun i hi => nk _ ⟨by omega, by omega⟩)]
  exact ebuf

end Services.Bootstrap.Refine.ExitRunW
