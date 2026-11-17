import Services.Bootstrap.Refine.RunFixed
import Services.Bootstrap.Refine.RunMixed
import Services.Bootstrap.Refine.DecodeCG
import Services.Bootstrap.Refine.ExportOkOf
import Services.Bootstrap.Decode.ExportEmpty

/-!
# Refine from the payload to its return, any number of instructions

`run_mixedG` is `run_mixed` for 1 ≤ n ≤ 2²⁴ (part A of full M1): the decode over every batch (`DecodeC.decode_allC`), the
transform loop and the exit encoder for that n (`Body.body`, `ExitEnc.enc_run`). Each instruction is one the milestone
passes through (a `Kinds.FixedKind`) or `ExportSegs ds`. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code), B.7
(export), Appendix C (ℰ); `Spec.refineInstr`.
-/

namespace Services.Bootstrap.Refine.RunMixed

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Alloc Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LoopAll Services.Bootstrap.Refine.Kinds
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.Enc Services.Bootstrap.Refine.ExportOkOf

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Refine from the payload, fixed-width instructions passed through and `Export`, any n ≤ 2²⁴**: `run_mixed`
    for 1 ≤ n ≤ 2²⁴ instructions, the payload's length prefix ℰ(n) of any width (`DecodeC.decode_allC`) and the
    output ℰ(n) ⌢ the encodings ⌢ ℰ₂(w mod 2^16). As `RunFixed.run_fixed`, each instruction j either a `FixedKind` with its slot property `Rs j` (passed
    through), or `ExportSegs ds` (its `Rs j` that of `Exported |ds|`, ≤ 2²⁶ segments of < 2³⁰ octets): refine
    returns ℰ(`BootstrapWorkOutput`) of the instructions `outI`, the host context the segments exported in
    order (`expTo`). Hypotheses: `ExportFmtOk` and `DebugLineOk`. -/
theorem run_mixedG {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [Services.Bootstrap.CodeA.HasCodeA p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {hb pb : Nat} (gl : Nat → UInt8)
    (is : List Spec.Instr) (Rs : Nat → List UInt8 → Prop) (ts : Nat → Nat)
    (hk : ∀ j, j < is.length → FixedKind p P (encOut is j) (Rs j) (ts j) ∧
      (segsOf (is.getD j .panic) = none ∨ ∃ ds, segsOf (is.getD j .panic) = some ds ∧
        (∀ bs, bs.take 8 = Num.encodeLE 8 9223372036854775827 → (bs.drop 8).take 8 = Num.encodeLE 8 ds.length →
          Rs j bs) ∧ 24 * ds.length < 1073741760 ∧ ∀ d ∈ ds, d.length < 1073741760))
    {ro : List UInt8} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1 ro)
    (dbg : ExitRun.DebugLineOk p cap0 env pb S0 S1 ro (fun j bs _ => Rs j bs))
    (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s) (hro : RoData.RoIs ro μ)
    (M q Ly r5 : Nat) (salt : List UInt8) (cp : Chunk)
    (hn : 1 ≤ is.length ∧ is.length ≤ 16777216) (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ M % 8 = 0)
    (hr5 : r5 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base) (hcpq : cp.addr + 32 = q)
    (hcpd : ∀ a, q ≤ a → a < q + Ly → InData cp a)
    (hLy : (Blob.encodeNat is.length).length + (is.map Spec.Instr.encode).flatten.length + 32 ≤ Ly ∧ Ly < 4294967296)
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat r5) (h6 : ω[6] = UInt64.ofNat Ly)
    (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q)
    (senc : μ.readN q (Blob.encodeNat is.length).length = Blob.encodeNat is.length)
    (pay : μ.readN (q + (Blob.encodeNat is.length).length) (is.map Spec.Instr.encode).flatten.length = (is.map Spec.Instr.encode).flatten)
    (ssalt : μ.readN (q + (Blob.encodeNat is.length).length + (is.map Spec.Instr.encode).flatten.length) 32 = salt)
    (w c' ret r5' r6' t : Nat) (hw64 : w < 18446744073709551616)
    (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w) (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c')
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5')
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6')
    (hc' : c' < 18446744073709551616)
    (hret : Fin.RetTo P ret t) (hr5' : r5' < 18446744073709551616)
    (hr6' : r6' < 18446744073709551616)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 4792 ω μ x t ω' μ' (expTo env is x is.length) N ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5' ∧
      ω'[6] = UInt64.ofNat r6' ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat ((Blob.encodeNat is.length).length + off (encOut is) is.length + 2) ∧
      μ'.readN buf ((Blob.encodeNat is.length).length + off (encOut is) is.length + 2) =
        Blob.encodeNat is.length ++ out (encOut is) is.length ++ Num.encodeLE 2 (w % 65536) ∧
      ((∀ a, buf ≤ a → a < buf + ((Blob.encodeNat is.length).length + off (encOut is) is.length + 2) → μ'.readable a = true) ∧
        buf + ((Blob.encodeNat is.length).length + off (encOut is) is.length + 2) < 2147483648)) ∨
    ∃ N, ExhaustsX env cap0 pb p 4792 ω μ x N := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  have hgd : ∀ j (hj : j < is.length), is.getD j .panic = is[j] := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hes : ∀ j (hj : j < (is.map Spec.Instr.encode).length),
      (is.map Spec.Instr.encode)[j] = (is.getD j .panic).encode := fun j hj => by
    rw [List.getElem_map, hgd j (by simpa using hj)]
  have hL : Lay (M - 744) (M + 272) := ⟨by omega, by omega, by omega, by omega⟩
  have hnone : ∀ j, segsOf (is.getD j .panic) = none → encOut is j = (is.getD j .panic).encode :=
    fun j h => by unfold encOut outI; rw [h]
  have hrn : ∀ j, segsOf (is.getD j .panic) = none → repsM Rs is j = fun _ bs _ => Rs j bs :=
    fun j h => by unfold repsM; rw [h]
  have hne : ∀ j (hj : j < (is.map Spec.Instr.encode).length), 1 ≤ (is.map Spec.Instr.encode)[j].length := by
    intro j hj
    rw [hes j hj]
    simp only [List.length_map] at hj
    rcases (hk j hj).2 with h | ⟨ds, hds, -⟩
    · rw [← hnone j h]; exact (hk j hj).1.ne
    · rw [segsOf_some hds, encode_exportSegs]; simp
  have hel : ∀ j (hj : j < (is.map Spec.Instr.encode).length),
      Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (M - 744) (M + 272) (NsM is j) (is.map Spec.Instr.encode)[j]
        (repsM Rs is j) := by
    intro j hj
    rw [hes j hj]
    simp only [List.length_map] at hj
    rcases (hk j hj).2 with h | ⟨ds, hds, -, hb1, hb2⟩
    · rw [hrn j h, show NsM is j = 4000 by unfold NsM; rw [h], ← hnone j h]
      exact ElemOkAF.toAFC (ElemOkAF.of_elemOkF hL ((hk j hj).1.dec _ _ hL))
    · rw [segsOf_some hds]
      rcases ds with _ | ⟨d0, ds'⟩
      · rw [show repsM Rs is j = fun _ bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧
            (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧ (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧
            (bs.drop 24).take 8 = Num.encodeLE 8 0 by unfold repsM; rw [hds],
          show NsM is j = 4000 by unfold NsM; rw [hds]]
        exact ElemOkAF.toAFC (Decode.ExportEmpty.export_empty_elem _ _ hL)
      · rw [show repsM Rs is j = Decode.VecVecOwn.VecVecRepC (9223372036854775807 + 10) (d0 :: ds') by
            unfold repsM; rw [hds],
          show NsM is j = 9 * (Decode.VecVecU8.encs (d0 :: ds')).flatten.length + 70300 * (d0 :: ds').length + 41200 by
            unfold NsM; rw [hds], encode_exportSegs]
        exact Decode.VecVecOwn.export_elem_bigC env cap0 pb hcap1 hcap0 gl _ _ hL (d0 :: ds')
          ⟨by simp, hb1⟩ hb2
  rcases DecodeC.decode_allC (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω μ s H M q Ly r5
      (is.map Spec.Instr.encode) salt (repsM Rs is) cp (NsM is) hel hg (by simp only [List.length_map]; omega)
      (by simp only [List.length_map]; omega) hne
      ⟨by omega, by omega, hM8⟩ hr5 hcp hcpd (by simpa using hLy) h1 h5 h6 s112 (by simpa using senc)
      (by simpa using pay) (by simpa using ssalt) tab rt with
    ⟨ω1, μ1, s1, E, N1, run1, b1, -, -, b168, b176, b184, -, -, -, H1, hcb, hcbd, ⟨csOf, hcs, hdisj⟩, keep1, fresh1,
      hi1, -⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.of hx⟩
  simp only [List.length_map] at b168 b184 hcb hcbd hcs hdisj fresh1
  obtain ⟨n, hN⟩ : ∃ n, is.length = n := ⟨_, rfl⟩
  rw [hN] at hn b168 b184 hcb hcbd hcs hdisj fresh1 hk ⊢
  have hb1 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨hE0, -, hET⟩ := Decode.VecU8.chunk_in H1.wf hcb rfl
  simp only at hE0 hET
  have hE32 : E - 32 + 32 = E := by omega
  have m1 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → (a + l ≤ M + 168 ∨ M + 224 ≤ a) → (a + l ≤ M + 272 ∨ M + 288 ≤ a) →
      μ1.readN a l = μ.readN a l :=
    fun a l h0 h1 h2 h3 => Memory.readN_congr (fun j hj => hi1 _ (by omega) (by omega) (by omega) (by omega))
  obtain ⟨tab1, rtab1⟩ := ExitRun.ro_keep H run1 (a := 67376) (l := 100) (by omega)
  obtain ⟨dtab1, rdtab1⟩ := ExitRun.ro_keep H run1 (a := 67760) (l := 96) (by omega)
  have hcp1 : cp ∈ chunks s1 := (keep1 cp hcp.1 hcp.2.1).1
  have ainj : ∀ c ∈ chunks s1, ∀ d ∈ chunks s1, c.addr = d.addr → c = d := by
    have ht := H1.wf.2.2.2.1
    unfold TilesOk at ht
    exact Tiles.addr_inj ht
  -- the chunks to keep before instruction k: the payload's and those of the instructions from k on
  let Kp : Nat → Chunk → Prop := fun k d => d = cp ∨ ∃ j, k ≤ j ∧ j < n ∧ d ∈ csOf j
  have hkp0 : ∀ d, Kp 0 d → d ∈ chunks s1 ∧ d.used = true := by
    rintro d (hd | ⟨j, -, hj, hd⟩)
    · rw [hd]; exact ⟨hcp1, hcp.2.1⟩
    · exact ⟨((hcs j hj).1 d hd).1, ((hcs j hj).1 d hd).2.1⟩
  have hmono : ∀ k d, Kp (k + 1) d → Kp k d := by
    rintro k d (h | ⟨j, h1, h2, h3⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, by omega, h2, h3⟩
  have slot : ∀ k, k < n → repsM Rs is k (csOf k) (μ1.readN (E + 232 * k) 232) μ1 :=
    fun k hk' => (hcs k hk').2 μ1 (fun _ _ _ _ => rfl)
  have rsub : ∀ j o l, o + l ≤ 232 → μ1.readN (E + 232 * j + o) l = ((μ1.readN (E + 232 * j) 232).drop o).take l :=
    fun j o l h => Decode.Loop.readN_sub μ1 _ 232 o l _ rfl h
  have elem : ∀ k, k < n →
      PassOk μ1 ((⟨E - 32, (232 * n + 31) / 32 + 1, true⟩ : Chunk).addr + 32) k (Kp k) (Kp (k + 1)) Rs
        (expTo env is x k) (expTo env is x (k + 1)) ∨
      ExportOk env μ1 ((⟨E - 32, (232 * n + 31) / 32 + 1, true⟩ : Chunk).addr + 32) k
        ⟨E - 32, (232 * n + 31) / 32 + 1, true⟩ (Kp k) (Kp (k + 1)) Rs (expTo env is x k) (expTo env is x (k + 1)) := by
    intro k hk'
    simp only [hE32]
    have hxs := expTo_succ env is x (k := k) (by omega)
    rcases (hk k hk').2 with h | ⟨ds, hds, hR, hb1, hb2⟩
    · have sl : Rs k (μ1.readN (E + 232 * k) 232) := by have := slot k hk'; rw [hrn k h] at this; exact this
      refine Or.inl ⟨ts k, ?_, ?_, sl, hmono k, by rw [hxs]; unfold instrCtx; rw [h]⟩
      · unfold rdN; rw [rsub k 44 1 (by omega)]; exact (hk k hk').1.pass _ sl
      · rw [← readN_take μ1 _ 232 8 (by omega)]; exact (hk k hk').1.tag _ sl
    · have sl := slot k hk'
      rcases ds with _ | ⟨d0, ds'⟩
      · simp only [repsM, hds] at sl
        exact Or.inr (export_ok_empty sl (hmono k) hR
          (by rw [hxs]; unfold instrCtx; rw [hds]; rfl))
      · simp only [repsM, hds] at sl
        refine Or.inr (export_ok_big sl hb1 hb2 (fun c hc => ⟨Or.inr ⟨k, Nat.le_refl _, hk', hc⟩,
          ((hcs k hk').1 c hc).2.2.1⟩) ?_ hR (by rw [hxs]; unfold instrCtx; rw [hds]))
        rintro d (hd | ⟨j, hj1, hj2, hdj⟩)
        · rw [hd]; exact ⟨Or.inl rfl, fun h => ((hcs k hk').1 _ h).2.2.2 rfl, fun c hc e =>
            ((hcs k hk').1 c hc).2.2.2 (ainj c ((hcs k hk').1 c hc).1 _ hcp1 e.symm)⟩
        · refine ⟨Or.inr ⟨j, by omega, hj2, hdj⟩, hdisj j k hj2 hk' (by omega) d hdj, fun c hc e => ?_⟩
          have := ainj d ((hcs j hj2).1 d hdj).1 c ((hcs k hk').1 c hc).1 e
          exact hdisj j k hj2 hk' (by omega) d hdj (this ▸ hc)
  rcases Body.body (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt (fun j bs _ => Rs j bs) (encOut is) Rs dbg
      ω1 μ1 s1 H1 (RoData.RoIs.keep H run1 hro) M n n ⟨E - 32, (232 * n + 31) / 32 + 1, true⟩ Kp Rs (expTo env is x)
      ⟨by omega, hM1, by omega, hM8⟩ (by omega) (by omega) (by omega) (by omega) ⟨hcb, rfl⟩
      (by simp only; omega) (by simp only; omega) hkp0 b1
      b168 (by simp only [hE32]; exact b176) b184 elem
      (fun j bs μ hj h => h) (fun j bs hj h => h)
      (fun j bs hj h => ⟨ts j, (hk j hj).1.nd, (hk j hj).1.tag bs h⟩)
      (fun j hj => (hk j hj).1.enc) (fun j hj => (hk j hj).1.len)
      w c' q ret r5' r6' t cp hw64
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s80)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s88)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s112)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s624)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s616)
      (by rw [m1 _ _ (by omega) (by omega) (by omega) (by omega)]; exact s608)
      hc' (fun _ => ⟨Or.inl rfl, hcpq, fun e => fresh1 cp hcp.1 hcp.2.1 e⟩) hret hr5' hr6'
      (by rw [tab1]; exact tab2) (fun a h1 h2 => by rw [rtab1 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [dtab1]; exact dtab) (fun a h1 h2 => by rw [rdtab1 a h1 h2]; exact rdtab a h1 h2) with
    ⟨ω2, μ2, s2, N2, buf, run2, H2, e0, e1, e5, e6, e7, e8, eo, erd⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨ω2, μ2, s2, _, buf, run1.trans run2, H2, e0, e1, e5, e6, e7, e8, eo, erd⟩
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩

end Services.Bootstrap.Refine.RunMixed
