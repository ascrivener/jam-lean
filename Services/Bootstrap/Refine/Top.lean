import Services.Bootstrap.Refine.MixedKinds
import Services.Bootstrap.Refine.SpecRun
import Services.Bootstrap.Refine.Prologue

/-!
# Refine from the arguments' decode to the halt, for the milestone's payloads

`from4680`: from the state the arguments' parse leaves at 4680 (refine's frame M = 4278058376, the decoded
arguments at M + 168, the payload y = ℰ(`Instructions { is, salt }`) ⌢ rest in the heap's first chunk), the
service id's log line (`Prologue.tail4680`), the instructions' decode, transform and output (`RunMixed.run_mixed`
with `MixedKinds.mixed_kinds`) reach the halting `jump_ind` at 6373 with ω₇, ω₈ the octets
ℰ(`BootstrapWorkOutput { outI is, i }`) and the host context the segments exported in order; or an allocation
fails. Hypotheses: the three fmt summaries (`ArgsLineOk`, `ExportFmtOk`, `DebugLineOk` for `DRm`). GP v0.8.0
Appendix B.4 (Ψ_R running bootstrap's code); `Spec.refine`.
-/

namespace Services.Bootstrap.Refine.Top

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Alloc
  Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.RunMixed Services.Bootstrap.Refine.PassLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The `Debug` line's slot property for the milestone: the slot of some well-formed instruction refine passes
    through (`kindRep`). -/
def DRm (C : Spec.Consts) (_j : Nat) (bs : List UInt8) (_μ : Memory) : Prop :=
  ∃ x, MFixed x ∧ x.WF C ∧ kindRep x bs

theorem DebugLineOk.mono {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat}
    {DR DR' : Nat → List UInt8 → Memory → Prop} (h : ExitRun.DebugLineOk p cap0 env pb S0 S1 DR)
    (hD : ∀ j bs μ, DR' j bs μ → DR j bs μ) : ExitRun.DebugLineOk p cap0 env pb S0 S1 DR' :=
  fun x ω μ s M c E n H a b d e f g i k l m o q r t u => h x ω μ s M c E n H a b d e f g i k l m o q r
    (fun j hj => hD j _ _ (t j hj)) u

theorem outI_mfixed {x : Spec.Instr} (hx : MFixed x ∨ ∃ ds, x = .exportSegs ds) : MFixed (outI x) := by
  rcases hx with hm | ⟨ds, rfl⟩
  · rw [show outI x = x by unfold outI; rw [MixedKinds.segsOf_fixed' hm]]; exact hm
  · show MFixed (.exported ds.length); trivial

theorem outI_wf {C : Spec.Consts} {x : Spec.Instr} (hx : MFixed x ∨ ∃ ds, x = .exportSegs ds) (hw : x.WF C)
    (hn : x.encode.length < 18446744073709551616) : (outI x).WF C := by
  rcases hx with hm | ⟨ds, rfl⟩
  · rw [show outI x = x by unfold outI; rw [MixedKinds.segsOf_fixed' hm]]; exact hw
  · show Spec.fits 8 ds.length
    rw [encode_exportSegs] at hn
    simp only [List.length_cons, List.length_append] at hn
    have := MixedKinds.encs_len ds
    unfold Spec.fits; omega

/-- **Refine from 4680 to the halt, the milestone's payloads**: from the arguments decoded at refine's frame
    M = 4278058376 (the payload's `Vec<u8>` {Y, q, Y} at M + 168, the item index I and the service id S as 32-bit
    words at M + 224, M + 228, the halt address and two zero words saved at M + 624, M + 616, M + 608), the payload
    y = ℰ(`Instructions { is, salt }`) ⌢ rest at q, in the heap's first chunk, with 1 ≤ |is| < 128 well-formed
    instructions each passed through or `ExportSegs`: the run reaches the halting `jump_ind` at 6373 with ω₇, ω₈
    the octets ℰ(`BootstrapWorkOutput { outI is, I }`), readable, and the host context the segments exported
    in order (`expTo`); or an allocation fails. -/
theorem from4680 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (C : Spec.Consts)
    (line : Prologue.ArgsLineOk p 134217728 env 1044430 S0 S1)
    (fmt : ExportSeg.ExportFmtOk p 134217728 env 1044430 S0 S1)
    (dbg : ExitRun.DebugLineOk p 134217728 env 1044430 S0 S1 (DRm C))
    (is : List Spec.Instr) (salt rest : List UInt8) (hsalt : salt.length = 32)
    (hn : 1 ≤ is.length ∧ is.length < 128) (hwf : ∀ x ∈ is, x.WF C)
    (hk : ∀ x ∈ is, MFixed x ∨ ∃ ds, x = .exportSegs ds)
    (Y I S q : Nat) (y : List UInt8) (hy : y = Spec.encodePayload is salt ++ rest) (hYl : y.length = Y)
    (hY : Y < 16777216) (hI : I < 65536) (hS : S < 4294967296)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env 1044430 S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat 4278058376)
    (s168 : μ.readN 4278058544 8 = Num.encodeLE 8 Y) (s176 : μ.readN 4278058552 8 = Num.encodeLE 8 q)
    (s184 : μ.readN 4278058560 8 = Num.encodeLE 8 Y) (s224 : μ.readN 4278058600 4 = Num.encodeLE 4 I)
    (s228 : μ.readN 4278058604 4 = Num.encodeLE 4 S) (hpay : μ.readN q Y = y) (cp : Chunk)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base ∧ cp.addr + 32 = q ∧
      ∀ a, q ≤ a → a < q + Y → InData cp a)
    (s624 : μ.readN (4278058376 + 624) 8 = Num.encodeLE 8 4294901760)
    (s616 : μ.readN (4278058376 + 616) 8 = Num.encodeLE 8 0)
    (s608 : μ.readN (4278058376 + 608) 8 = Num.encodeLE 8 0)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = Encode.Enc.table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (N buf len : Nat),
      FreeStepsH p (refineContractK 134217728 env) 4680 ω μ ((∅, []) : RefineCtx) 6373 ω' μ'
        (expTo env is ((∅, []) : RefineCtx) is.length) N ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat len ∧
      μ'.readN buf len = Spec.encodeOutput (is.map outI) I ∧ (∀ a, buf ≤ a → a < buf + len → μ'.readable a = true)) ∨
    ∃ N, ExhaustsX env 134217728 1044430 p 4680 ω μ ((∅, []) : RefineCtx) N := by
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm, hcpu, hcpb, hcpq, hcpd⟩ := hcp
  obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
  have hbT := H.hbT
  -- the payload
  have hnat : Codec.nat is.length = [UInt8.ofNat is.length] :=
    Services.Bootstrap.Encode.PrefixBig.encodeNat_small _ ⟨by omega, hn.2⟩
  have hflat : y = UInt8.ofNat is.length :: ((is.map Spec.Instr.encode).flatten ++ salt ++ rest) := by
    rw [hy]; unfold Spec.encodePayload Spec.vec; rw [hnat]; simp
  have hYv : Y = 1 + (is.map Spec.Instr.encode).flatten.length + 32 + rest.length := by
    rw [← hYl, hflat]; simp [hsalt]; omega
  have hq1 : q + Y < 2147483648 := by
    have := hcpd (q + Y - 1) (by omega) (by omega); unfold InData at this; omega
  -- the log line
  rcases Prologue.tail4680 (p := p) (P := P) env 134217728 line ((∅, []) : RefineCtx) ω μ s H 4278058376 Y q Y I S
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
  -- the instructions' kinds
  obtain ⟨ts, hkk⟩ := MixedKinds.mixed_kinds (p := p) (P := P) C is hwf hk (by omega)
  have hx : ∀ j, (is.getD j .panic ∈ is ∨ is.getD j .panic = .panic) := fun j => by
    by_cases hj : j < is.length
    · left; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    · right; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have dbg' : ExitRun.DebugLineOk p 134217728 env 1044430 S0 S1
      (fun j bs _ => kindRep (outI (is.getD j .panic)) bs) := DebugLineOk.mono dbg (fun j bs μ hb => by
    rcases hx j with hm | hp
    · have hk' := hk _ hm
      have hl := MixedKinds.len_le_flatten
        (List.mem_map.mpr ⟨_, hm, rfl⟩ : (is.getD j .panic).encode ∈ is.map Spec.Instr.encode)
      exact ⟨_, outI_mfixed hk', outI_wf hk' (hwf _ hm) (by omega), hb⟩
    · rw [hp] at hb
      exact ⟨.panic, trivial, trivial, hb⟩)
  -- the payload's octets
  have rsub : ∀ o l, o + l ≤ Y → μ2.readN (q + o) l = (y.drop o).take l :=
    fun o l h => Decode.Loop.readN_sub μ2 q Y o l y pay2 h
  have sb : μ2.read q = UInt8.ofNat is.length := by
    have := rsub 0 1 (by omega)
    rw [hflat] at this
    simpa [Memory.readN] using this
  have pay : μ2.readN (q + 1) (is.map Spec.Instr.encode).flatten.length = (is.map Spec.Instr.encode).flatten := by
    rw [rsub 1 _ (by omega), hflat]; simp
  have ssalt : μ2.readN (q + 1 + (is.map Spec.Instr.encode).flatten.length) 32 = salt := by
    rw [Nat.add_assoc, rsub _ _ (by omega), hflat, Nat.add_comm 1, List.drop_succ_cons, List.append_assoc,
      List.drop_left, List.take_left' hsalt]
  rcases RunMixed.run_mixed (p := p) (P := P) (hb := 0) env 134217728 (by decide) (by decide) (fun a => μ2.read a) is
      (fun j => kindRep (outI (is.getD j .panic))) ts hkk fmt dbg' ((∅, []) : RefineCtx) ω2 μ2 s2 H2
      4278058376 q Y (ω2[5]).toNat salt cp hn ⟨by decide, by decide, by decide⟩ (UInt64.toNat_lt _)
      ⟨hcp2, hcpu, by rw [base2]; exact hcpb⟩ hcpq (fun a h1 h2 => hcpd a h1 h2) ⟨by omega, by omega⟩
      (fun _ _ => rfl) e1 UInt64.ofNat_toNat.symm e6 m112 sb pay ssalt I Y 4294901760 0 0 6373 (by omega) m80 m88
      (by rw [r2 _ _ (by omega) (by omega)]; exact s624) (by rw [r2 _ _ (by omega) (by omega)]; exact s616)
      (by rw [r2 _ _ (by omega) (by omega)]; exact s608) (by omega) (Or.inr ⟨rfl, rfl⟩) (by decide) (by decide)
      (by rw [tk1]; exact tab) (fun a h1 h2 => by rw [tk2 a h1 h2]; exact rt a h1 h2)
      (by rw [tk3]; exact tab2) (fun a h1 h2 => by rw [tk4 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [tk5]; exact dtab) (fun a h1 h2 => by rw [tk6 a h1 h2]; exact rdtab a h1 h2) with
    ⟨ω3, μ3, s3, N3, buf, run3, H3, f0, f1, f5, f6, f7, f8, fo, frd⟩ | ⟨N, hx3⟩
  · refine Or.inl ⟨ω3, μ3, _, buf, _, run2.trans run3, f0, f7, f8, ?_, frd⟩
    rw [fo, SpecRun.output_eq is I hn hI]
  · exact Or.inr ⟨_, ExhaustsX.pre run2 hx3⟩

end Services.Bootstrap.Refine.Top
