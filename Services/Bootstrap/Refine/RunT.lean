import Services.Bootstrap.Refine.InvT
import Services.Bootstrap.Refine.RunMixedG
import Services.Bootstrap.Refine.ExitRunW

/-!
# T1c's run: refine from the payload to its return

Step 3 of the plan in `Refine/README.md`. `StepT` is what each decoded slot gives the transform loop: a slot refine
passes through (`PassKind`, `PkgT.PassSlot`), an `ExportSegs` slot, or an eager `Lookup` slot; `pkg_step` is every
T1c instruction's element decoder with that slot property (`PkgAll.pkg_all`, `ExportEmpty`, `VecVecOwn`, `lookupF`).
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code), B.7 (the instruction list).
-/

namespace Services.Bootstrap.Refine.RunT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.Kinds
  Services.Bootstrap.Refine.PkgT Services.Bootstrap.Refine.PkgAll Services.Bootstrap.Refine.SpecRunT
  Services.Bootstrap.CodeR Services.Bootstrap.CodeT1B Services.Bootstrap.CodeT1C Services.Bootstrap.Alloc
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.LoopT Services.Bootstrap.Refine.RunMixed
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.GrowH

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The empty `ExportSegs`' decoded slot. -/
def ExpEmptyRep (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0

/-- **What a decoded slot gives the loop** (for the decode's chunks cs, in every memory keeping them as μr). -/
def StepT (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program) (C : Spec.Consts) (x : Spec.Instr)
    (cs : List Chunk) (bs : List UInt8) (μr : Memory) : Prop :=
  (PassKind x ∧ PassSlot env K pb p P C x cs bs μr) ∨
  (x = .exportSegs [] ∧ ExpEmptyRep bs) ∨
  (∃ ds, x = .exportSegs ds ∧ ds ≠ [] ∧ 24 * ds.length < 1073741760 ∧ (∀ d ∈ ds, d.length < 1073741760) ∧
    ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) →
      Decode.VecVecOwn.VecVecRepC (9223372036854775807 + 10) ds cs bs μ'') ∨
  (∃ sv h, x = .lookup sv h true ∧ kindRep (.lookup sv h true) bs)

theorem encodeNat_len_pos (n : Nat) : 1 ≤ (Blob.encodeNat n).length := by
  unfold Blob.encodeNat; split
  · simp
  · split <;> simp

theorem encs_bounds : ∀ ds : List (List UInt8),
    ds.length ≤ (Decode.VecVecU8.encs ds).flatten.length ∧ ∀ d ∈ ds, d.length ≤ (Decode.VecVecU8.encs ds).flatten.length
  | [] => ⟨by simp, by simp⟩
  | d :: ds => by
    obtain ⟨h1, h2⟩ := encs_bounds ds
    have h0 := encodeNat_len_pos d.length
    simp only [Decode.VecVecU8.encs, List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      List.mem_cons] at h1 h2 ⊢
    refine ⟨by omega, ?_⟩
    rintro e (rfl | he)
    · omega
    · have := h2 e he; omega

/-- **Every T1c instruction's decode package with `StepT`**: x well-formed for C, not `ImportSegs` or
    `RandomStorageRefine`, |x.encode| ≤ 2^24; the global words as `PkgAll.pkg_all` needs. -/
theorem pkg_step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (hgD : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 341)
    (hgA : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 80)
    (C : Spec.Consts) (hmax : C.maxValCount ≤ 1023) (hQ : C.authQueueLen = 80)
    (x : Spec.Instr) (hw : x.WF C) (hni : NoImpRsr x) (hlen : x.encode.length ≤ 16777216) :
    DecPkg env K pb gl p P x (StepT env K pb p P C x) := by
  by_cases hk : PassKind x
  · obtain ⟨N, Rd, hF, hS⟩ := pkg_all (p := p) (P := P) env K pb hK1 hK gl hgD hgA C hmax hQ x hw hk hlen
    exact ⟨N, Rd, hF, fun cs bs μr h => Or.inl ⟨hk, hS cs bs μr h⟩⟩
  cases x with
  | exportSegs ds =>
    rcases ds with _ | ⟨d0, ds'⟩
    · exact pkg_ofAF (fun F RD hL => by
          rw [show (Spec.Instr.exportSegs []).encode = [10, 0] by simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl]
          exact Decode.ExportEmpty.export_empty_elem F RD hL)
        (fun cs bs μr h => Or.inr (Or.inl ⟨rfl, h⟩))
    · have he := RunMixed.encode_exportSegs (d0 :: ds')
      obtain ⟨b1, b2⟩ := encs_bounds (d0 :: ds')
      have hl := hlen
      rw [he] at hl
      simp only [List.length_cons, List.length_append] at hl
      have hb1 : 24 * (d0 :: ds').length < 1073741760 := by simp only [List.length_cons] at b1 ⊢; omega
      have hb2 : ∀ d ∈ d0 :: ds', d.length < 1073741760 := fun d hd => by have := b2 d hd; omega
      refine ⟨_, _, fun F RD hL => he ▸ Decode.VecVecOwn.export_elem_bigC env K pb hK1 hK gl F RD hL (d0 :: ds')
        ⟨by simp, hb1⟩ hb2, fun cs bs μr h => Or.inr (Or.inr (Or.inl ⟨_, rfl, by simp, hb1, hb2, h⟩))⟩
  | lookup sv h e =>
    cases e with
    | false => exact absurd rfl hk
    | true =>
      obtain ⟨hs, hh⟩ := hw
      have he : (Spec.Instr.lookup sv h true).encode = 8 :: (Codec.fixed 4 sv ++ h ++ [UInt8.ofNat 1]) := by
        simp [Spec.Instr.encode]
      exact pkg_ofF (fun F RD hL => he ▸ Decode.Elems.lookupF F RD hL (Codec.fixed 4 sv) h 1
          (by simp [Codec.fixed]) hh (by decide))
        (fun cs bs μr hb => Or.inr (Or.inr (Or.inr ⟨sv, h, rfl, hb⟩)))
  | importSegs => exact absurd hni id
  | randomStorageRefine => exact absurd hni id
  | _ => exact absurd trivial hk

theorem encode_len_pos (x : Spec.Instr) : 1 ≤ x.encode.length := by
  unfold Spec.Instr.encode
  split <;> simp

theorem off_le (enc : Nat → List UInt8) (Bd : Nat) : ∀ n, (∀ j, j < n → (enc j).length ≤ Bd) →
    Encode.Loop.off enc n ≤ n * Bd
  | 0, _ => by simp [Encode.Loop.off]
  | n + 1, h => by
    have ih := off_le enc Bd n (fun j hj => h j (by omega))
    have hn := h n (by omega)
    unfold Encode.Loop.off at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [Nat.succ_mul]; omega

/-- A `PassKind` instruction is returned as it is and exports nothing. -/
theorem passKind_out {x : Spec.Instr} (h : PassKind x) (lk : Nat → List UInt8 → Option (List UInt8))
    (env : RefineHost.Env) (y : RefineCtx) : outT lk x = x ∧ instrCtx env x y = y := by
  cases x <;> first | exact absurd h id | (constructor <;> rfl) | skip
  case lookup sv h e => cases e with
    | false => exact ⟨rfl, rfl⟩
    | true => exact absurd h (by simp [PassKind])

/-- **Refine from the payload to its return, T1c** (step 3): as `RunMixedG.run_mixedG`, for 1 ≤ n ≤ 2^24
    well-formed instructions with no `Import` and no `RandomStorageRefine`, each of at most 2^24 octets: refine
    returns ℰ(n) ⌢ the encodings of `outT (lookupOf env)` of each instruction ⌢ ℰ₂(w), the context the segments
    exported in order. Hypotheses: the global words 𝖢, 𝖰 (`hgD`, `hgA`) with C's bounds; preimages shorter than 2^63
    octets and the eager `Lookup`'s gas bound; `ExportFmtOk`, `LookupFmtOk`, the drop table's entry 8, and
    `DebugLineOk` for `DRt C`. -/
theorem run_t {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] [HasCodeR p P]
    [HasCodeT1B p P] [HasCodeT1C p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {hb pb : Nat} (gl : Nat → UInt8)
    (hgD : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 341)
    (hgA : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 80)
    (C : Spec.Consts) (hmax : C.maxValCount ≤ 1023) (hQ : C.authQueueLen = 80)
    (is : List Spec.Instr) (hwf : ∀ x ∈ is, x.WF C) (hni : ∀ x ∈ is, NoImpRsr x)
    (hlenI : ∀ x ∈ is, x.encode.length ≤ 16777216)
    (hlenL : ∀ sv h d, LookupStep.lookupOf env sv h = some d → d.length < 9223372036854775808)
    (hgas : ∀ sv h d, LookupStep.lookupOf env sv h = some d →
      Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap0)
    {ro : List UInt8} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1 ro)
    (lfmt : LookupFmt.LookupFmtOk p cap0 env pb S0 S1 ro) (htab : (ro.drop 32).take 4 = Lookup.dropEntry8)
    (dbg : ExitRun.DebugLineOk p cap0 env pb S0 S1 ro (fun _ => DRt C 0))
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
    (pay : μ.readN (q + (Blob.encodeNat is.length).length) (is.map Spec.Instr.encode).flatten.length =
      (is.map Spec.Instr.encode).flatten)
    (ssalt : μ.readN (q + (Blob.encodeNat is.length).length + (is.map Spec.Instr.encode).flatten.length) 32 = salt)
    (w c' ret r5' r6' t : Nat) (hw64 : w < 18446744073709551616)
    (s80 : μ.readN (M + 80) 8 = Num.encodeLE 8 w) (s88 : μ.readN (M + 88) 8 = Num.encodeLE 8 c')
    (s624 : μ.readN (M + 624) 8 = Num.encodeLE 8 ret) (s616 : μ.readN (M + 616) 8 = Num.encodeLE 8 r5')
    (s608 : μ.readN (M + 608) 8 = Num.encodeLE 8 r6')
    (hc' : c' < 18446744073709551616)
    (hret : Fin.RetTo P ret t) (hr5' : r5' < 18446744073709551616)
    (hr6' : r6' < 18446744073709551616)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (tab2 : μ.readN 67376 100 = Encode.Enc.table) (rtab2 : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (dtab : μ.readN 67760 96 = DropOut.dtable) (rdtab : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (rltab : ∀ a, 65568 ≤ a → a < 65572 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N buf : Nat),
      FreeStepsH p (refineContractK cap0 env) 4792 ω μ x t ω' μ' (expTo env is x is.length) N ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 632) ∧ ω'[5] = UInt64.ofNat r5' ∧
      ω'[6] = UInt64.ofNat r6' ∧ ω'[7] = UInt64.ofNat buf ∧
      ω'[8] = UInt64.ofNat ((Blob.encodeNat is.length).length +
        Encode.Loop.off (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode) is.length + 2) ∧
      μ'.readN buf ((Blob.encodeNat is.length).length +
          Encode.Loop.off (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode) is.length + 2) =
        Blob.encodeNat is.length ++ Encode.Loop.out (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode)
          is.length ++ Num.encodeLE 2 (w % 65536) ∧
      ((∀ a, buf ≤ a → a < buf + ((Blob.encodeNat is.length).length +
          Encode.Loop.off (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode) is.length + 2) →
          μ'.readable a = true) ∧
        buf + ((Blob.encodeNat is.length).length +
          Encode.Loop.off (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode) is.length + 2) < 2147483648)) ∨
    ∃ N, ExhaustsX env cap0 pb p 4792 ω μ x N := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  have hgd : ∀ j (hj : j < is.length), is.getD j .panic = is[j] := fun j hj => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hmem : ∀ j, j < is.length → is.getD j .panic ∈ is := fun j hj => by rw [hgd j hj]; exact List.getElem_mem hj
  have hL : Lay (M - 744) (M + 272) := ⟨by omega, by omega, by omega, by omega⟩
  -- the packages
  have pk : ∀ j, ∃ (N : Nat) (Rd : List Chunk → List UInt8 → Memory → Prop), j < is.length →
      (∀ F RD, Lay F RD → Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P F RD N (is.getD j .panic).encode Rd) ∧
      ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) → Rd cs bs μ'') →
        StepT env cap0 pb p P C (is.getD j .panic) cs bs μr := fun j => by
    by_cases hj : j < is.length
    · obtain ⟨N, Rd, h1, h2⟩ := pkg_step (p := p) (P := P) env cap0 pb hcap1 hcap0 gl hgD hgA C hmax hQ _
        (hwf _ (hmem j hj)) (hni _ (hmem j hj)) (hlenI _ (hmem j hj))
      exact ⟨N, Rd, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun _ _ _ => True, fun h => absurd h hj⟩
  let Ns : Nat → Nat := fun j => Classical.choose (pk j)
  let Rds : Nat → List Chunk → List UInt8 → Memory → Prop := fun j => Classical.choose (Classical.choose_spec (pk j))
  have hpk : ∀ j, j < is.length → _ := fun j => Classical.choose_spec (Classical.choose_spec (pk j))
  have hes : ∀ j (hj : j < (is.map Spec.Instr.encode).length),
      (is.map Spec.Instr.encode)[j] = (is.getD j .panic).encode := fun j hj => by
    rw [List.getElem_map, hgd j (by simpa using hj)]
  rcases DecodeC.decode_allC (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω μ s H M q Ly r5
      (is.map Spec.Instr.encode) salt Rds cp Ns
      (fun j hj => by rw [hes j hj]; exact ((hpk j (by simpa using hj)).1) _ _ hL) hg
      (by simp only [List.length_map]; omega) (by simp only [List.length_map]; omega)
      (fun j hj => by rw [hes j hj]; exact encode_len_pos _)
      ⟨by omega, by omega, hM8⟩ hr5 hcp hcpd (by simpa using hLy) h1 h5 h6 s112 (by simpa using senc)
      (by simpa using pay) (by simpa using ssalt) tab rt with
    ⟨ω1, μD, s1, E, N1, run1, b1, -, -, b168, b176, b184, -, -, -, H1, hcb, hcbd, ⟨csOf, hcs, hdisj⟩, keep1, fresh1,
      hi1, -⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.of hx⟩
  simp only [List.length_map] at b168 b184 hcb hcbd hcs hdisj fresh1
  obtain ⟨n, hN⟩ : ∃ n, is.length = n := ⟨_, rfl⟩
  rw [hN] at hn b168 b184 hcb hcbd hcs hdisj fresh1 hmem ⊢
  have hb1 := H1.hb0
  have hbT1 := H1.hbT
  obtain ⟨hE0, -, hET⟩ := Decode.VecU8.chunk_in H1.wf hcb rfl
  simp only at hE0 hET
  have hE32 : E - 32 + 32 = E := by omega
  have hcp1 : cp ∈ chunks s1 := (keep1 cp hcp.1 hcp.2.1).1
  have ainj : ∀ c ∈ chunks s1, ∀ d ∈ chunks s1, c.addr = d.addr → c = d := by
    have ht := H1.wf.2.2.2.1
    unfold TilesOk at ht
    exact Tiles.addr_inj ht
  have cbnd : ∀ c ∈ chunks s1, c.used = true → ∀ a, InData c a → a < 2147483648 := fun c hc hu a ha => by
    have := Decode.VecU8.chunk_in H1.wf hc hu
    unfold InData at ha; omega
  let ce : Chunk := ⟨E - 32, (232 * n + 31) / 32 + 1, true⟩
  have hcE : ce.addr + 32 = E := hE32
  let Kp0 : Chunk → Prop := fun d => d = cp ∨ ∃ j, j < n ∧ d ∈ csOf j
  have hkp0 : ∀ d, Kp0 d → d ∈ chunks s1 ∧ d.used = true := by
    rintro d (hd | ⟨j, hj, hd⟩)
    · rw [hd]; exact ⟨hcp1, hcp.2.1⟩
    · exact ⟨((hcs j hj).1 d hd).1, ((hcs j hj).1 d hd).2.1⟩
  obtain ⟨ω2, μE, run2, L, st, efr⟩ := Entry.entry (p := p) (P := P) (R := refineContractK cap0 env) env
    (expTo env is x 0) ω1 μD s1 M n n ce Kp0 (fun _ bs => bs = ([] : List UInt8)) H1
    ⟨by omega, by omega, by omega, hM8⟩ (by omega) (by omega) (by omega) (by omega) ⟨hcb, rfl⟩
    (by rw [hcE]; simp only [ce]; omega) (by rw [hcE]; omega) hkp0 b1 b168 (by rw [hcE]; exact b176) b184
  rw [hcE] at L st
  have lowE : ∀ a, a < 2147483648 → μE.read a = μD.read a := fun a h => efr a (by omega) (Or.inl (by omega))
  have hEt : E + 232 * n < 2147483648 := L.hEtop
  have hin : ∀ k, k < n → ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a :=
    fun k hk a h1 h2 => hcbd a (by omega) (by omega)
  have hceB : ∀ a, InData ce a → a < 2147483648 := cbnd ce hcb rfl
  -- what each decoded slot gives, in μE
  have hstep : ∀ k, k < n →
      StepT env cap0 pb p P C (is.getD k .panic) (csOf k) (μE.readN (E + 232 * k) 232) μE := by
    intro k hk
    have e1 : μE.readN (E + 232 * k) 232 = μD.readN (E + 232 * k) 232 :=
      Memory.readN_congr (fun j hj => lowE _ (by omega))
    rw [e1]
    exact (hpk k (by omega)).2 _ _ _ (fun μ'' hk'' => (hcs k hk).2 μ'' (fun c hc a ha =>
      (hk'' c hc a ha).trans (lowE a (cbnd c ((hcs k hk).1 c hc).1 ((hcs k hk).1 c hc).2.1 a ha))))
  let xs : Nat → Spec.Instr := fun j => is.getD j .panic
  have hcsOk : InvT.CsOk ce cp csOf n :=
    ⟨fun j c hj hc => ⟨((hcs j hj).1 c hc).2.2.1, ((hcs j hj).1 c hc).2.2.2⟩, hdisj⟩
  have hinv0 : InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n 0 μE Kp0 (fun _ => []) :=
    ⟨fun _ _ => rfl, fun _ _ _ => rfl, Or.inl rfl,
      fun c d hc hd e => ainj c (hkp0 c hc).1 d (hkp0 d hd).1 e,
      fun c hc a ha => cbnd c (hkp0 c hc).1 (hkp0 c hc).2 a ha,
      fun j _ hj c hc => ⟨Or.inr ⟨j, hj, hc⟩, fun _ _ => rfl⟩,
      fun _ _ => False, fun j hj => absurd hj (Nat.not_lt_zero _), fun j c hj => absurd hj (Nat.not_lt_zero _),
      fun j _ _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have elem : ∀ k μ0 Kp B, k < n →
      InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n k μ0 Kp B →
      PassOkT μ0 E k Kp B (expTo env is x k) (expTo env is x (k + 1))
        (InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n (k + 1)) ∨
      ExportOkT env μ0 E k ce Kp B (expTo env is x k) (expTo env is x (k + 1))
        (InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n (k + 1)) ∨
      LookupOk env cap0 μ0 E k ce Kp B (expTo env is x k) (expTo env is x (k + 1))
        (InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n (k + 1)) := by
    intro k μ0 Kp B hk hI
    have hxs := expTo_succ env is x (k := k) (by omega)
    rcases hstep k hk with ⟨hpk', hps⟩ | ⟨hx', hrep⟩ | ⟨ds, hx', -, hb1', hb2', hrep⟩ | ⟨sv, h, hx', hrep⟩
    · obtain ⟨ho, hc⟩ := passKind_out hpk' (LookupStep.lookupOf env) env (expTo env is x k)
      rw [hxs, hc]
      exact Or.inl (InvT.inv_pass hcsOk hk (hin k hk) hps ho (Nat.lt_of_le_of_lt (hlenI _ (hmem k hk)) (by decide)) hI)
    · rw [hxs, hx']
      exact Or.inr (Or.inl (InvT.inv_export_empty hcap1 hcap0 hcsOk hk (hin k hk) hx' hrep hI))
    · rw [hxs, hx']
      exact Or.inr (Or.inl (InvT.inv_export_big hcap1 hcap0 hcsOk hk (hin k hk) hx'
        (hrep μ0 (fun c hc a ha => (hI.2.2.2.2.2.1 k (Nat.le_refl _) hk c hc).2 a ha)) hb1' hb2' hI))
    · have hw := hwf _ (hmem k hk)
      rw [hx'] at hw
      have hsv : sv < 4294967296 := hw.1
      rw [hxs, hx']
      exact Or.inr (Or.inr (InvT.inv_lookup hcap1 hcap0 hcsOk hk (hin k hk) hceB hx' hrep hsv rfl (hlenL sv h)
        (hgas sv h) hI))
  have pre12 := run1.trans run2
  have hroE := RoData.RoIs.keep H pre12 hro
  obtain ⟨-, rlt⟩ := ExitRun.ro_keep H pre12 (a := 65568) (l := 4) (by omega)
  rcases loop_t (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 fmt lfmt htab (expTo env is x) L
      (fun k μ0 Kp B => InvT.Inv env cap0 pb p P C (LookupStep.lookupOf env) xs μE ce cp csOf n k μ0 Kp B) elem
      5054 (Or.inr (by omega)) ω2 μE s1 hroE (fun a h1 h2 => by rw [rlt a h1 h2]; exact rltab a h1 h2)
      μE Kp0 (fun _ => []) hinv0 st with ⟨s3, ω3, μ3, N3, μ0', Kp', B', run3, st3, hI3⟩ | ⟨N, hx⟩
  rotate_left
  · exact Or.inr ⟨_, ExhaustsX.pre pre12 hx⟩
  obtain ⟨-, ifr, icp, -, -, -, own, iown, iownK, idisj⟩ := hI3
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st3.out
  have sw : ∀ j, j < n → SlotW env cap0 pb p P (DRt C 0) (outT (LookupStep.lookupOf env) (xs j)).encode
      (ptr + 232 * j) μ3 s3 (own j) := fun j hj =>
    (iown j hj).1 μ3 s3 _ (hout j hj) (fun d hd => st3.kp d (iownK j d hj hd).1)
  have sw' : ∀ j, ∃ (rep DR : List UInt8 → Memory → Prop) (src : Nat → Nat → Prop), j < n →
      Encode.GrowH.EncOkMH env cap0 pb p P 232 (outT (LookupStep.lookupOf env) (xs j)).encode rep src ∧
      rep (μ3.readN (ptr + 232 * j) 232) μ3 ∧ DR (μ3.readN (ptr + 232 * j) 232) μ3 ∧
      (∀ bs μ, DR bs μ → DRt C 0 bs μ) ∧
      (∀ bs μ μ', (∀ q m, src q m → μ'.readN q m = μ.readN q m) → rep bs μ → rep bs μ') ∧
      (∀ bs μ μ', (∀ q m, src q m → μ'.readN q m = μ.readN q m) → DR bs μ → DR bs μ') ∧
      (∀ q m, src q m → ∃ c, own j c ∧ c.addr + 32 ≤ q ∧ q + m ≤ c.addr + 32 * c.size) ∧
      ((∃ t, DropOut.NoDrop t ∧ μ3.readN (ptr + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨
        DropVecW.HeapElW μ3 s3 (ptr + 232 * j) (own j)) := fun j => by
    by_cases hj : j < n
    · obtain ⟨r, d, sr, hh⟩ := sw j hj
      exact ⟨r, d, sr, fun _ => hh⟩
    · exact ⟨fun _ _ => True, fun _ _ => False, fun _ _ => False, fun h => absurd h hj⟩
  let reps : Nat → List UInt8 → Memory → Prop := fun j => Classical.choose (sw' j)
  let DRs : Nat → List UInt8 → Memory → Prop := fun j => Classical.choose (Classical.choose_spec (sw' j))
  let srcs : Nat → Nat → Nat → Prop := fun j =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (sw' j)))
  have hsw : ∀ j, j < n → _ := fun j => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (sw' j)))
  have pre3 := pre12.trans run3
  have fr0 : ∀ a l, (M + 80 ≤ a ∧ a + l ≤ M + 120) ∨ (M + 608 ≤ a ∧ a + l ≤ M + 632) →
      μ0'.readN a l = μ.readN a l := fun a l h => Memory.readN_congr (fun j hj =>
    (ifr _ (by omega) (by omega)).trans ((efr _ (by omega) (by omega)).trans
      (hi1 _ (by omega) (by omega) (by omega) (by omega))))
  obtain ⟨tab3, rtab3⟩ := ExitRun.ro_keep H pre3 (a := 67376) (l := 100) (by omega)
  obtain ⟨dtab3, rdtab3⟩ := ExitRun.ro_keep H pre3 (a := 67760) (l := 96) (by omega)
  have h5n := PVM.encodeNat_len_le5 n (by omega)
  have hoff := off_le (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode) 8589934592 n
    (fun j hj => Nat.le_of_lt (iown j hj).2)
  rcases ExitRunW.exit_runW (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0
      (fun j bs μ => j < n ∧ DRs j bs μ) (fun j => (outT (LookupStep.lookupOf env) (is.getD j .panic)).encode)
      reps srcs own
      (Top.DebugLineOk.mono dbg (fun j bs μ h => (hsw j h.1).2.2.2.1 bs μ h.2))
      (expTo env is x n) ω3 μ3 s3 (RoData.RoIs.keep H pre3 hro) L (by omega) (by omega) (by omega)
      (by unfold capBound; omega) (by unfold capBound; omega) st3 (by omega) ptr (by omega) vp
      (fun j hj => ⟨hj, (hsw j hj).2.2.1⟩) (fun j hj => (hsw j hj).2.1) (fun j hj => (hsw j hj).1)
      (fun j hj => (hsw j hj).2.2.2.2.1)
      (fun j hj bs μ μ' hk h => ⟨h.1, (hsw j hj).2.2.2.2.2.1 bs μ μ' hk h.2⟩)
      (fun j hj q m h => by
        obtain ⟨c, hc, h1, h2⟩ := (hsw j hj).2.2.2.2.2.2.1 q m h
        exact ⟨c, (iownK j c hj hc).1, (iownK j c hj hc).2.1, h1, h2⟩)
      (fun j d hj hd => ⟨(iownK j d hj hd).1, (iownK j d hj hd).2.1⟩)
      (fun j j' d hj hj' hne h h' => idisj j j' d hj hj' hne h h')
      (fun j hj => (hsw j hj).2.2.2.2.2.2.2)
      w c' q ret r5' r6' t cp hw64
      (by rw [fr0 _ _ (by omega)]; exact s80) (by rw [fr0 _ _ (by omega)]; exact s88)
      (by rw [fr0 _ _ (by omega)]; exact s112) (by rw [fr0 _ _ (by omega)]; exact s624)
      (by rw [fr0 _ _ (by omega)]; exact s616) (by rw [fr0 _ _ (by omega)]; exact s608)
      hc' (fun _ => ⟨icp, hcpq, fresh1 cp hcp.1 hcp.2.1⟩) (fun _ j hj h => (iownK j cp hj h).2.2.1 rfl)
      hret hr5' hr6' (by rw [tab3]; exact tab2) (fun a h1 h2 => by rw [rtab3 a h1 h2]; exact rtab2 a h1 h2)
      (by rw [dtab3]; exact dtab) (fun a h1 h2 => by rw [rdtab3 a h1 h2]; exact rdtab a h1 h2) with
    ⟨ω4, μ4, s4, N4, buf, run4, H4, f0, f1, f5, f6, f7, f8, fo, frd⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨ω4, μ4, s4, _, buf, pre3.trans run4, H4, f0, f1, f5, f6, f7, f8, fo, frd⟩
  · exact Or.inr ⟨_, ExhaustsX.pre pre3 hx⟩

end Services.Bootstrap.Refine.RunT
