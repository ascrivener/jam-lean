import Services.Bootstrap.Refine.RunT
import Services.Bootstrap.Refine.TopG

/-!
# T1c: refine from the arguments' decode to the halt

`from4680T` is `TopG.from4680G` with `RunT.run_t` (T1c's instructions: all but `Import` and `RandomStorageRefine`)
at any gas cap K ≥ 2^27, and the output ℰ(`BootstrapWorkOutput { outT (lookupOf env) is, I }`) (`output_eqT`). GP
v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code), Appendix C (ℰ); `Spec.refine`.
-/

namespace Services.Bootstrap.Refine.TopT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.CodeR Services.Bootstrap.CodeT1B Services.Bootstrap.CodeT1C
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Alloc
  Services.Bootstrap.Refine.RunMixed Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.SlotT
  Services.Bootstrap.Refine.SpecRunT

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The binary's output is ℰ(`BootstrapWorkOutput { is.map f, item }`)** for any instruction map f. -/
theorem output_eqT (is : List Spec.Instr) (item : Nat) (hi : item < 65536) (f : Spec.Instr → Spec.Instr) :
    PVM.Blob.encodeNat is.length ++ Encode.Loop.out (fun j => (f (is.getD j .panic)).encode) is.length ++
      PVM.Num.encodeLE 2 (item % 65536) = Spec.encodeOutput (is.map f) item := by
  unfold Spec.encodeOutput Spec.vec Encode.Loop.out
  rw [SpecRun.map_range_getD is (fun x => (f x).encode), List.length_map, Nat.mod_eq_of_lt hi]
  simp [List.map_map, Codec.nat, Codec.fixed, Function.comp_def]

/-- **T1c: refine from 4680 to the halt** (`from4680G` with `run_t`, at gas cap K): the payload
    y = ℰ(`Instructions { is, salt }`) ⌢ rest with 1 ≤ |is| ≤ 2^24 well-formed instructions, none `Import` or
    `RandomStorageRefine`, |y| < 2^24; the global words 𝖢 = 341 and 𝖰 = 80 at 196616 / 196680: the run reaches the
    halting `jump_ind` at 6373 with ω₇, ω₈ the octets ℰ(`BootstrapWorkOutput { outT (lookupOf env) is, I }`); or an
    allocation fails. Hypotheses as `run_t`'s (Fmt summaries, the drop table's entry 8, preimages < 2^63 octets and
    the eager `Lookup`'s gas bound). -/
theorem from4680T {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] [HasCodeR p P]
    [HasCodeT1B p P] [HasCodeT1C p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (C : Spec.Consts)
    (hmax : C.maxValCount ≤ 1023) (hQ : C.authQueueLen = 80)
    {ro : List UInt8} (line : Prologue.ArgsLineOk p K env 1044430 S0 S1 ro)
    (fmt : ExportSeg.ExportFmtOk p K env 1044430 S0 S1 ro)
    (lfmt : LookupFmt.LookupFmtOk p K env 1044430 S0 S1 ro) (htab : (ro.drop 32).take 4 = Lookup.dropEntry8)
    (dbg : ExitRun.DebugLineOk p K env 1044430 S0 S1 ro (fun _ => DRt C 0))
    (hlenL : ∀ sv h d, LookupStep.lookupOf env sv h = some d → d.length < 9223372036854775808)
    (hgas : ∀ sv h d, LookupStep.lookupOf env sv h = some d →
      Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ K)
    (is : List Spec.Instr) (salt rest : List UInt8) (hsalt : salt.length = 32)
    (hn : 1 ≤ is.length ∧ is.length ≤ 16777216) (hwf : ∀ x ∈ is, x.WF C) (hni : ∀ x ∈ is, NoImpRsr x)
    (Y I S q : Nat) (y : List UInt8) (hy : y = Spec.encodePayload is salt ++ rest) (hYl : y.length = Y)
    (hY : Y < 16777216) (hI : I < 65536) (hS : S < 4294967296)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env 1044430 S0 S1 μ s) (hro : RoData.RoIs ro μ)
    (h1 : ω[1] = UInt64.ofNat 4278058376)
    (s168 : μ.readN 4278058544 8 = Num.encodeLE 8 Y) (s176 : μ.readN 4278058552 8 = Num.encodeLE 8 q)
    (s184 : μ.readN 4278058560 8 = Num.encodeLE 8 Y) (s224 : μ.readN 4278058600 4 = Num.encodeLE 4 I)
    (s228 : μ.readN 4278058604 4 = Num.encodeLE 4 S) (hpay : μ.readN q Y = y) (cp : Chunk)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base ∧ cp.addr + 32 = q ∧
      ∀ a, q ≤ a → a < q + Y → InData cp a)
    (s624 : μ.readN (4278058376 + 624) 8 = Num.encodeLE 8 4294901760)
    (s616 : μ.readN (4278058376 + 616) 8 = Num.encodeLE 8 0)
    (s608 : μ.readN (4278058376 + 608) 8 = Num.encodeLE 8 0)
    (gD : μ.readN 196616 2 = Num.encodeLE 2 341) (gA : μ.readN 196680 8 = Num.encodeLE 8 80)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = Encode.Enc.table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (rltab : ∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (N buf len : Nat),
      FreeStepsH p (refineContractK K env) 4680 ω μ ((∅, []) : RefineCtx) 6373 ω' μ'
        (expTo env is ((∅, []) : RefineCtx) is.length) N ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧
      μ'.readN buf len = Spec.encodeOutput (is.map (outT (LookupStep.lookupOf env))) I ∧
      ((∀ a, buf ≤ a → a < buf + len → μ'.readable a = true) ∧ buf + len < 2147483648)) ∨
    ∃ N, ExhaustsX env K 1044430 p 4680 ω μ ((∅, []) : RefineCtx) N := by
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm, hcpu, hcpb, hcpq, hcpd⟩ := hcp
  obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
  have hbT := H.hbT
  -- the payload
  have hflat : y = Blob.encodeNat is.length ++ ((is.map Spec.Instr.encode).flatten ++ salt ++ rest) := by
    rw [hy]; unfold Spec.encodePayload Spec.vec; simp [Codec.nat]
  generalize hℓ : (Blob.encodeNat is.length).length = ℓ
  have hYv : Y = ℓ + (is.map Spec.Instr.encode).flatten.length + 32 + rest.length := by
    rw [← hYl, hflat]; simp [hsalt, hℓ]; omega
  have hq1 : q + Y < 2147483648 := by
    have := hcpd (q + Y - 1) (by omega) (by omega); unfold InData at this; omega
  have hlenI : ∀ x ∈ is, x.encode.length ≤ 16777216 := fun x hx => by
    have := MixedKinds.len_le_flatten (List.mem_map.mpr ⟨_, hx, rfl⟩ : x.encode ∈ is.map Spec.Instr.encode)
    omega
  -- the log line
  rcases Prologue.tail4680 (p := p) (P := P) env K line ((∅, []) : RefineCtx) ω μ s H hro 4278058376 Y q Y I S
      ⟨by decide, by decide, by decide⟩ (by omega) (by omega) (by omega) (by omega) hS h1 s168 s176 s184 s224 s228 with
    ⟨ω2, μ2, s2, N2, run2, H2, e1, e6, m80, m88, m112, fr2, keep2, gl2, base2⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨N, hx⟩
  obtain ⟨hcp2, hcpd2⟩ := keep2 cp hcpm hcpu
  have pay2 : μ2.readN q Y = y := by
    rw [Memory.readN_congr (fun j hj => hcpd2 _ (hcpd _ (by omega) (by omega)))]; exact hpay
  have r2 : ∀ a l, 4278058376 + 288 ≤ a → a + l ≤ 4294967296 → μ2.readN a l = μ.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega) (by omega))
  obtain ⟨tk1, tk2⟩ := ExitRun.ro_keep H run2 (a := 67476) (l := 100) (by omega)
  obtain ⟨tk3, tk4⟩ := ExitRun.ro_keep H run2 (a := 67376) (l := 100) (by omega)
  obtain ⟨tk5, tk6⟩ := ExitRun.ro_keep H run2 (a := 67760) (l := 96) (by omega)
  obtain ⟨-, tk8⟩ := ExitRun.ro_keep H run2 (a := 65568) (l := 4) (by omega)
  have gD2 : (List.range 2).map (fun k => μ2.read (196616 + k)) = Num.encodeLE 2 341 := by
    rw [← gD]; exact Memory.readN_congr (fun j hj => gl2 _ ⟨by omega, by omega⟩)
  have gA2 : (List.range 8).map (fun k => μ2.read (196680 + k)) = Num.encodeLE 8 80 := by
    rw [← gA]; exact Memory.readN_congr (fun j hj => gl2 _ ⟨by omega, by omega⟩)
  -- the payload's octets
  have rsub : ∀ o l, o + l ≤ Y → μ2.readN (q + o) l = (y.drop o).take l :=
    fun o l h => Decode.Loop.readN_sub μ2 q Y o l y pay2 h
  have senc : μ2.readN q (Blob.encodeNat is.length).length = Blob.encodeNat is.length := by
    have := rsub 0 ℓ (by omega)
    rw [hflat, Nat.add_zero, List.drop_zero, ← hℓ, List.take_left] at this
    exact this
  have pay : μ2.readN (q + (Blob.encodeNat is.length).length) (is.map Spec.Instr.encode).flatten.length =
      (is.map Spec.Instr.encode).flatten := by
    rw [hℓ, rsub ℓ _ (by omega), hflat, ← hℓ, List.drop_left, List.append_assoc, List.take_left]
  have ssalt : μ2.readN (q + (Blob.encodeNat is.length).length + (is.map Spec.Instr.encode).flatten.length) 32 =
      salt := by
    rw [hℓ, Nat.add_assoc, rsub _ _ (by omega), hflat, ← hℓ, ← List.drop_drop, List.drop_left, List.append_assoc,
      List.drop_left, List.take_left' hsalt]
  rcases RunT.run_t (p := p) (P := P) (hb := 0) env K hK1 hK (fun a => μ2.read a) gD2 gA2 C hmax hQ is hwf hni
      hlenI hlenL hgas fmt lfmt htab dbg ((∅, []) : RefineCtx) ω2 μ2 s2 H2 (RoData.RoIs.keep H run2 hro)
      4278058376 q Y (ω2[5]).toNat salt cp hn ⟨by decide, by decide, by decide⟩ (UInt64.toNat_lt _)
      ⟨hcp2, hcpu, by rw [base2]; exact hcpb⟩ hcpq (fun a h1 h2 => hcpd a h1 h2) ⟨by omega, by omega⟩
      (fun _ _ => rfl) e1 UInt64.ofNat_toNat.symm e6 m112 senc pay ssalt I Y 4294901760 0 0 6373 (by omega) m80 m88
      (by rw [r2 _ _ (by omega) (by omega)]; exact s624) (by rw [r2 _ _ (by omega) (by omega)]; exact s616)
      (by rw [r2 _ _ (by omega) (by omega)]; exact s608) (by omega) (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
      (by rw [tk1]; exact tab) (fun a h1 h2 => by rw [tk2 a h1 h2]; exact rt a h1 h2)
      (by rw [tk3]; exact tab2) (fun a h1 h2 => by rw [tk4 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [tk5]; exact dtab) (fun a h1 h2 => by rw [tk6 a h1 h2]; exact rdtab a h1 h2)
      (fun a h1 h2 => by rw [tk8 a h1 h2]; exact rltab a h1 h2) with
    ⟨ω3, μ3, s3, N3, buf, run3, H3, f0, f1, f5, f6, f7, f8, fo, frd⟩ | ⟨N, hx3⟩
  · refine Or.inl ⟨ω3, μ3, _, buf, _, run2.trans run3, f0, f7, f8, ?_, frd⟩
    rw [fo, output_eqT is I hI]
  · exact Or.inr ⟨_, ExhaustsX.pre run2 hx3⟩

/-- Readability below 196608 (the read-only region) survives a refine run to a state with the allocator's
    context. -/
theorem rd_kept0 {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory}
    {s : State} {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} (H : HeapCtx env pb S0 S1 μ' s)
    (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n) (b : Nat) (hb : b < 196608) :
    μ'.readable b = μ.readable b := by
  obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
  unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]

/-- The eager `Lookup`'s gas bound holds at the cap 2^62 for every preimage shorter than 2^63 octets
    (GP v0.8.0 Appendix B.7, Ω_L: 𝗀 = C_H + ⌈C_HL · |d| / 1024⌉ with C_H = 1125, C_HL = 264). -/
theorem gas_cap62 (l : Nat) (h : l < 9223372036854775808) :
    Constants.CgasHconst + memGas Constants.CgasHlinear l ≤ 4611686018427387904 := by
  unfold memGas Constants.CgasHconst Constants.CgasHlinear; omega

/-- **T1c: refine from Y's state to the halt** (pc 0 … 6373, gas cap K = 2^62): `refine_coreG` with
    `from4680T`. The arguments' parse (`ArgsAll.refine_args`, which also gives 𝖢 = 341 and 𝖰 = 80 at
    196616 / 196680 from the parameter chain under `env.fetch.params = Params.full`) and `from4680T`. The
    eager `Lookup`'s gas bound follows from K = 2^62 and preimages shorter than 2^63 octets (`hlenL`);
    the lookup table's octets 65568 … 65572 are readable since the start-up memory's read-only data is. -/
theorem refine_coreT {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] [HasCodeR p P]
    [HasCodeT1B p P] [HasCodeT1C p P]
    (env : RefineHost.Env) (C : Spec.Consts) (henv : heapBounds env.code = (48, 1044430))
    (hpar : env.fetch.params = Params.full) (hmax : C.maxValCount ≤ 1023) (hQ : C.authQueueLen = 80)
    {ro : List UInt8} (line : Prologue.ArgsLineOk p 4611686018427387904 env 1044430 S0 S1 ro)
    (fmt : ExportSeg.ExportFmtOk p 4611686018427387904 env 1044430 S0 S1 ro)
    (lfmt : LookupFmt.LookupFmtOk p 4611686018427387904 env 1044430 S0 S1 ro)
    (htab : (ro.drop 32).take 4 = Lookup.dropEntry8)
    (dbg : ExitRun.DebugLineOk p 4611686018427387904 env 1044430 S0 S1 ro (fun _ => DRt C 0))
    (hlenL : ∀ sv h d, LookupStep.lookupOf env sv h = some d → d.length < 9223372036854775808)
    (is : List Spec.Instr) (salt rest : List UInt8) (hsalt : salt.length = 32)
    (hn : 1 ≤ is.length ∧ is.length ≤ 16777216) (hwf : ∀ x ∈ is, x.WF C) (hni : ∀ x ∈ is, NoImpRsr x)
    (μ : Memory) (hμ : Prefix.StartMem μ) (hz : Prefix.StartMemZ μ) (hro : RoData.RoIs ro μ) (cc I S : Nat)
    (h y : List UInt8)
    (hc : cc < 65536) (hI : I < 65536) (hS : S < 4294967296) (hh : h.length = 32)
    (hy : y = Spec.encodePayload is salt ++ rest) (hY : y.length < 16777216) (L : Nat)
    (hLdef : (Blob.encodeNat cc).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
      (Blob.encodeNat y.length).length + y.length + 32 = L) (hL : L < 16777217)
    (hmem : μ.readN 4278124544 L = Blob.encodeNat cc ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat y.length ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + L → μ.readable j = true)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = Encode.Enc.table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (N buf len : Nat),
      FreeStepsH p (refineContractK 4611686018427387904 env) 0 (Prefix.initRegs L) μ ((∅, []) : RefineCtx) 6373
        ω' μ' (expTo env is ((∅, []) : RefineCtx) is.length) N ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧
      μ'.readN buf len = Spec.encodeOutput (is.map (outT (LookupStep.lookupOf env))) I ∧
      ((∀ a, buf ≤ a → a < buf + len → μ'.readable a = true) ∧ buf + len < 2147483648)) ∨
    ∃ N, ExhaustsX env 4611686018427387904 1044430 p 0 (Prefix.initRegs L) μ ((∅, []) : RefineCtx) N := by
  have hYl : 1 ≤ y.length := by
    rw [hy]; unfold Spec.encodePayload Spec.vec; simp only [List.length_append]
    have := MixedKinds.encodeNat_pos is.length
    simp only [Codec.nat] at *; omega
  rcases ArgsAll.refine_args p P env 4611686018427387904 (by decide) (by decide) henv hpar μ hμ hz cc I S h hc hI
      hS y.length hYl hY y rfl hh L hLdef hL hmem hrd with
    ⟨q, s', ω1, μ1, N1, run1, a0, a1, a5, a6, b168, b176, b184, -, b224, b228, -, bpay, H1, hq, hbase,
      ⟨cp, hcpm, hcpu, hcpb, hcpq, hcpd⟩, tk, -, b624, b616, b608, -, -, -, gD, gA⟩ | hx
  rotate_left
  · exact Or.inr hx
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := tk
  rcases from4680T (p := p) (P := P) env 4611686018427387904 (by decide) (by decide) C hmax hQ line fmt lfmt htab
      dbg hlenL (fun sv hh d hd => gas_cap62 _ (hlenL sv hh d hd)) is salt rest hsalt hn hwf hni y.length I S q y hy
      rfl hY hI hS ω1 μ1 s' H1 (RoData.RoIs.keep0 H1 run1 hro) a1 b168 b176 b184 b224 b228 bpay cp
      ⟨hcpm, hcpu, hcpb, hcpq, hcpd⟩ b624 b616 b608 gD gA
      (by rw [t1]; exact tab) (fun a h1 h2 => by rw [t2 a h1 h2]; exact rt a h1 h2)
      (by rw [t3]; exact tab2) (fun a h1 h2 => by rw [t4 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [t5]; exact dtab) (fun a h1 h2 => by rw [t6 a h1 h2]; exact rdtab a h1 h2)
      (fun a h1 h2 => by rw [rd_kept0 H1 run1 a (by omega)]; exact hμ.ro a (by omega) (by omega)) with
    ⟨ω2, μ2, N2, buf, len, run2, e0, e7, e8, eo, erd⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨ω2, μ2, _, buf, len, run1.trans run2, e0, e7, e8, eo, erd⟩
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩

end Services.Bootstrap.Refine.TopT
