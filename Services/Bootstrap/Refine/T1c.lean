import Services.Bootstrap.Refine.TopT
import Services.Bootstrap.Refine.Milestone

/-!
# T1c: bootstrap's refine on canonical payloads

`refine_t1c`: Ψ_R (GP v0.8.0 eq. `refinvocation`) of a work item whose code is bootstrap (`IsBootstrapC`), for a
payload ℰ(`Instructions { is, salt }`) ⌢ rest of 1 ≤ |is| well-formed instructions, none `Import` (`hnoimport`) or
`RandomStorageRefine` (`hrsr`), with |y| + 48 ≤ 2^24: Ψ_R returns `Spec.refine`'s output and exports under the GP
refine host functions (`RSem.run`), with C = `Consts.ofParams Params.full rk`; or runs out of gas; or the run
reaches a failed allocation (`ExhaustsHeap`). T1c of `docs/bootstrap-target.md` (M1) for those instructions.
-/

namespace Services.Bootstrap.Refine.T1c

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix Services.Bootstrap.Bridge
  Services.Bootstrap.Refine.RunMixed Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.SpecRunT
  Services.Bootstrap.Refine.Milestone Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Facts about the vendored blob for T1c** (a named hypothesis until step 10 of `docs/bootstrap-target.md`
    discharges it): `Milestone.VendoredFacts`, and the drop dispatch table's entry for index 8 (the 4 octets at
    read-only offset 32, which the eager `Lookup`'s slot drop reads). A closed statement about the constant
    `Bridge.vendored` alone. -/
def VendoredFactsC : Prop :=
  VendoredFacts ∧ ∃ vb : JamBlob, vendored = some vb ∧ (vb.ro.toList.drop 32).take 4 = Lookup.dropEntry8

/-- **The looked-up preimage is a bootstrap binary, with T1c's code facts**: `IsBootstrap`, and its code also
    passes `checkCode` for the append-only tiers T1c's run uses (`CodeT1B`, `CodeT1C`;
    `docs/code-fact-tiers.md`). For the vendored blob the kernel discharges these (step 10;
    `CodeT1BCheck.checkCode_ok`, `CodeT1CCheck.checkCode_ok`). -/
def IsBootstrapC (l : List UInt8) : Prop :=
  IsBootstrap l ∧ ∃ (code : ByteArray) (jb : JamBlob), splitMetadata l = some code ∧
    JamBlob.parse? code = some jb ∧ checkCode jb.code CodeT1B.facts = true ∧
    checkCode jb.code CodeT1C.facts = true

/-- **The fmt summaries T1c assumes** (named hypotheses, in the approved pattern, to be discharged by the fmt
    session), at the gas cap K = 2^62 of refine's host contract: the service id's log line
    (`Prologue.ArgsLineOk`, 4742), the `Export` segment's line (`ExportSeg.ExportFmtOk`, 5744), the eager
    `Lookup`'s log line (`LookupFmt.LookupFmtOk`) and the output's `Debug` line (`ExitRun.DebugLineOk` for
    `SlotT.DRt C`, 6159). The cap only bounds the host calls' gas in the contract the gas-free run uses; Ψ_M's
    lift holds at any cap. -/
def FmtHypsC (C : Spec.Consts) : Prop :=
  ∀ vb : JamBlob, vendored = some vb → ∀ (p : ByteArray) (P : Program) [HasCode p P] [CodeX.HasCodeX p P]
    [CodeR.HasCodeR p P] [CodeF.HasCodeF p P] [CodeA.HasCodeA p P] [CodeT1B.HasCodeT1B p P]
    [CodeT1C.HasCodeT1C p P] (env : RefineHost.Env), heapBounds env.code = (48, 1044430) →
    Prologue.ArgsLineOk p 4611686018427387904 env 1044430 S0 S1 vb.ro.toList ∧
    ExportSeg.ExportFmtOk p 4611686018427387904 env 1044430 S0 S1 vb.ro.toList ∧
    LookupFmt.LookupFmtOk p 4611686018427387904 env 1044430 S0 S1 vb.ro.toList ∧
    ExitRun.DebugLineOk p 4611686018427387904 env 1044430 S0 S1 vb.ro.toList (fun _ => DRt C 0)

theorem encode_pos (x : Spec.Instr) : 1 ≤ x.encode.length := by
  unfold Spec.Instr.encode; split <;> simp

theorem length_le_flatten (is : List Spec.Instr) : is.length ≤ (is.map Spec.Instr.encode).flatten.length := by
  induction is with
  | nil => simp
  | cons x is ih => have := encode_pos x; simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons]; omega

/-- **T1c** (`docs/bootstrap-target.md` M1, for every instruction but `Import` and `RandomStorageRefine`): for a
    work item whose code is bootstrap (`IsBootstrapC`), core index c < 2^16, item index i < 2^16, service id < 2^32,
    and payload y = ℰ(`Instructions { is, salt }`) ⌢ rest with 1 ≤ |is| well-formed instructions (`WF C`), none
    `Import` (`hnoimport`) or `RandomStorageRefine` (`hrsr`), |y| + 48 ≤ 2^24, and every preimage the historical
    lookup can return shorter than 2^63 octets (`hpre`): `Spec.refine C` under the GP refine host functions returns
    some output and exports, and Ψ_R's result and exports are those; or Ψ_R runs out of gas (∞, no exports); or
    the run reaches a failed allocation (`ExhaustsHeap`: heap exhaustion, decision 4; that it then ends in ☇ with
    no exports is not yet proved).

    C = `Spec.Consts.ofParams Params.full rk` for any rk (Adam's decision (A)): refine reads 𝖢 and 𝖰 from the full
    chain's parameters, and `randomKeys` is irrelevant here since `RandomStorageRefine` is excluded. The output is
    ℰ(`BootstrapWorkOutput { outT lk is, i }`): each instruction passed through, each `ExportSegs ds` returned as
    `Exported |ds|`, each eager `Lookup s h` as `LookedUp (lk s h)` (`SpecRunT.run_refineT`).

    Hypotheses besides the payload's shape: `VendoredFactsC` (a closed fact about the vendored blob, for step 10),
    `FmtHypsC C` (the four fmt summaries, at gas cap 2^62), `hnoimport` (Import deferred, Adam), `hrsr`
    (`RandomStorageRefine` excluded, decision of 2026-11-13), `hpre` (preimages < 2^63 octets). The bound
    |y| + 48 ≤ 2^24 is Ψ_M's argument limit Z_I = 2^24 (GP v0.8.0 Appendix A.7). GP v0.8.0 eq. `refinvocation`. -/
theorem refine_t1c (rk : Nat → Nat → List Spec.Bytes) (hvend : VendoredFactsC)
    (hfmt : FmtHypsC (Spec.Consts.ofParams Params.full rk)) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem)
    (l : List UInt8) (hw : p.items[i]? = some w)
    (hl : (d.get? w.service).bind (·.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList) = some l)
    (hboot : IsBootstrapC l) (hc : c < 65536) (hi : i < 65536) (hs : w.service < 4294967296)
    (is : List Spec.Instr) (salt rest : List UInt8) (hy : w.payload.toList = Spec.encodePayload is salt ++ rest)
    (hsalt : salt.length = 32) (hn : 1 ≤ is.length) (hY : w.payload.size + 48 ≤ 16777216)
    (hwf : ∀ x ∈ is, x.WF (Spec.Consts.ofParams Params.full rk))
    (hnoimport : ∀ x ∈ is, ∀ ds, x ≠ .importSegs ds)
    (hrsr : ∀ x ∈ is, ∀ sd n, x ≠ .randomStorageRefine sd n)
    (hpre : ∀ s h v, (d.get? s).bind (·.historicalLookup p.context.lookupAnchorSlot h) = some v →
      v.length < 9223372036854775808) :
    let o := psiR Params.full d c i p r imports extrinsics off
    ∃ out ex, RSem.run (Spec.refine (Spec.Consts.ofParams Params.full rk) i w.payload.toList)
        (RSem.Env.of d p imports i off) = some (out, ex) ∧
      ((o.result, o.exports) = (.ok ⟨out.toArray⟩, ex) ∨ (o.result = .err .outOfGas ∧ o.exports = []) ∨
        ExhaustsHeap Params.full d c i p r imports extrinsics off) := by
  intro o
  generalize hC : Spec.Consts.ofParams Params.full rk = C at hfmt hwf ⊢
  have hmax : C.maxValCount ≤ 1023 := by rw [← hC]; show 3 * Params.full.coreCount ≤ 1023; decide
  have hQ : C.authQueueLen = 80 := by rw [← hC]; show Params.full.authQueueSize = 80; decide
  have hni : ∀ x ∈ is, NoImpRsr x := fun x hx => by
    cases x with
    | importSegs ds => exact hnoimport _ hx ds rfl
    | randomStorageRefine sd n => exact hrsr _ hx sd n rfl
    | _ => trivial
  have hYs0 : w.payload.size = (Spec.encodePayload is salt ++ rest).length := by
    rw [← hy, ByteArray.length_toList']
  have hnb : is.length ≤ 16777216 := by
    have := length_le_flatten is
    rw [hYs0] at hY; unfold Spec.encodePayload Spec.vec at hY; simp only [List.length_append] at hY; omega
  have hspec := SpecRunT.run_refineT C (RSem.Env.of d p imports i off) i is salt rest hwf (by omega) hsalt hni
  refine ⟨_, _, by rw [hy]; exact hspec, ?_⟩
  obtain ⟨⟨hsize, code, jb, vb, hcode, hjb, hvb, hro, hrw, hhp, hss, hheap, hcc, hccX, hccA, hccF, hccR⟩,
    code', jb', hcode', hjb', hccT1B, hccT1C⟩ := hboot
  obtain rfl : code = code' := Option.some.inj (hcode.symm.trans hcode')
  obtain rfl : jb = jb' := Option.some.inj (hjb.symm.trans hjb')
  obtain ⟨⟨vb', hvb', hlay', t1, t2, t3, -⟩, vb'', hvb'', t8⟩ := hvend
  obtain rfl : vb' = vb := Option.some.inj (hvb'.symm.trans hvb)
  obtain rfl : vb' = vb'' := Option.some.inj (hvb'.symm.trans hvb'')
  have hlay : layoutOk jb = true := by unfold layoutOk; rw [hro, hrw, hhp, hss]; exact hlay'
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI : HasCode jb.code P := ⟨hP⟩
  haveI : CodeX.HasCodeX jb.code P := CodeX.HasCodeX.of hP hccX
  haveI : CodeA.HasCodeA jb.code P := CodeA.HasCodeA.of hP hccA
  haveI : CodeF.HasCodeF jb.code P := CodeF.HasCodeF.of hP hccF
  haveI : CodeR.HasCodeR jb.code P := CodeR.HasCodeR.of hP hccR
  haveI : CodeT1B.HasCodeT1B jb.code P := CodeT1B.HasCodeT1B.of hP hccT1B
  haveI : CodeT1C.HasCodeT1C jb.code P := CodeT1C.HasCodeT1C.of hP hccT1C
  -- Ψ_R's steps up to Ψ_M
  show (let o := psiR Params.full d c i p r imports extrinsics off
    (o.result, o.exports) = (.ok ⟨(Spec.encodeOutput (is.map (outT (rsemLk (RSem.Env.of d p imports i off)))) i).toArray⟩,
      SpecRun.expsL (RSem.Env.of d p imports i off).exportOffset is []) ∨
    (o.result = .err .outOfGas ∧ o.exports = []) ∨ ExhaustsHeap Params.full d c i p r imports extrinsics off)
  simp only [psiR, hw, hl]
  rw [ite_eq_right (by omega)]
  simp only [hcode]
  have hEnv : psiREnv Params.full d i p r imports extrinsics off w code = RefineHost.Env.mk Params.full w.service d
      p.context.lookupAnchorSlot code off (FetchContext.mk Params.full (some p) (some (List.replicate 32 0)) (some r)
      (some i) (some imports) (some extrinsics) none) := rfl
  have hArgs : psiRArgs c i w p = (⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
      (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩ : ByteArray) := rfl
  have hlk : rsemLk (RSem.Env.of d p imports i off) = LookupStep.lookupOf (RefineHost.Env.mk Params.full w.service d
      p.context.lookupAnchorSlot code off (FetchContext.mk Params.full (some p) (some (List.replicate 32 0)) (some r)
      (some i) (some imports) (some extrinsics) none)) := rfl
  rw [hlk]
  generalize hE : RefineHost.Env.mk Params.full w.service d p.context.lookupAnchorSlot code off
    (FetchContext.mk Params.full (some p) (some (List.replicate 32 0)) (some r) (some i) (some imports)
      (some extrinsics) none) = env at hEnv ⊢
  have hcodeE : env.code = code := by rw [← hE]
  have hparE : env.fetch.params = Params.full := by rw [← hE]
  have hoffE : env.exportOffset = off := by rw [← hE]
  have hlenL : ∀ sv h v, LookupStep.lookupOf env sv h = some v → v.length < 9223372036854775808 :=
    fun sv h v hv => hpre sv h v (by rw [← hE] at hv; exact hv)
  generalize hA : (⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
    (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩ : ByteArray) = a at hArgs ⊢
  generalize hyy : w.payload.toList = y at hy
  have hYs : w.payload.size = y.length := by rw [← hyy, ByteArray.length_toList']
  have hlist : a.toList = Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat y.length ++ y ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList := by
    rw [← hA]
    simp only [Codec.var, Codec.nat, ← ByteArray.length_toList' w.payload, hyy, List.append_assoc]
    rw [ByteArray.toList_eq_data]
  have hasize : a.size = (Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat y.length ++ y ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).length := by
    rw [← hlist, ByteArray.length_toList']
  have hwC := encodeNat_len_le3 c hc
  have hwI := encodeNat_len_le3 i hi
  have hwS := encodeNat_len_le5 w.service hs
  have hwY := encodeNat_len_le5 y.length (by omega)
  have hh := PsiREmpty.hash256_length ⟨p.encode.toArray⟩
  have hLsum : a.size = (Blob.encodeNat c).length + (Blob.encodeNat i).length + (Blob.encodeNat w.service).length +
      (Blob.encodeNat y.length).length + y.length + 32 := by
    rw [hasize]; simp only [List.length_append, hh]
  have ha : a.size ≤ inputSize := by rw [hLsum]; simp only [inputSize]; omega
  have hSM := startMem_initial jb a hlay ha
  have hZ := startMemZ_initial jb a hlay ha
  have hlay2 := hlay
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay2
  obtain ⟨⟨⟨⟨⟨hros, hrws⟩, hheapP⟩, hstack⟩, _⟩, _⟩ := hlay2
  have hY0 : standardInit code a = some (jb.code, initialRegs a, initialMemory jb a) := by
    have hfit : ¬(5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32) := by
      rw [hros, hrws, hheapP, hstack]; decide
    unfold standardInit validJamBlob?
    rw [ite_eq_right (by omega), hjb, Option.bind_some, ite_eq_right hfit]
    rfl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hros, roundZone, zoneSize]
  have hmem := initialMemory_readN_args jb a (by simp [roStart, zoneSize, hros, two32])
    (by simp [hrs, hrws, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)
  rw [hlist] at hmem
  have tabR : ∀ o l, o + l ≤ 11608 → (initialMemory jb a).readN (65536 + o) l = (vb'.ro.toList.drop o).take l :=
    fun o l h => by rw [initialMemory_readN_ro jb a hlay ha o l h, hro]
  have rdR : ∀ x, 65536 ≤ x → x < 77144 → (initialMemory jb a).readable x = true := hSM.ro
  obtain ⟨hfA, hfE, hfL, hfD⟩ := hfmt vb' hvb' jb.code P env (by rw [hcodeE, hheap])
  have hsize' : y.length < 16777216 := by omega
  rcases TopT.refine_coreT (p := jb.code) (P := P) env C (by rw [hcodeE, hheap]) hparE hmax hQ hfA hfE hfL t8 hfD
      hlenL is salt rest hsalt ⟨hn, hnb⟩ hwf hni (initialMemory jb a) hSM hZ tabR c i w.service
      (Blake2b.hash256 ⟨p.encode.toArray⟩).toList y hc hi hs hh hy hsize' a.size hLsum.symm (by omega)
      (by simpa [argStart, zoneSize, inputSize] using hmem)
      (fun j h1 h2 => initialMemory_readable_args jb a j (by simp [argStart, zoneSize, inputSize]; omega)
        (by simp [argStart, zoneSize, inputSize] at h2 ⊢; omega))
      (by rw [show (67476 : Nat) = 65536 + 1940 from rfl, tabR _ _ (by omega)]; exact t1)
      (fun x h1 h2 => rdR x (by omega) (by omega))
      (by rw [show (67376 : Nat) = 65536 + 1840 from rfl, tabR _ _ (by omega)]; exact t2)
      (fun x h1 h2 => rdR x (by omega) (by omega))
      (by rw [show (67760 : Nat) = 65536 + 2224 from rfl, tabR _ _ (by omega)]; exact t3)
      (fun x h1 h2 => rdR x (by omega) (by omega)) with
    ⟨ω', μ', N, buf, len, hsteps, h0, h7, h8, hout, hrdo⟩ | ⟨N, ω', μ', x', j, run, hfail⟩
  · rw [← initRegs_eq] at hsteps
    have hexit : FreeRunH jb.code (refineContractK 4611686018427387904 env) 6373 ω' μ'
        (expTo env is ((∅, []) : RefineCtx) is.length) .halt ω' μ' (expTo env is ((∅, []) : RefineCtx) is.length) :=
      .exit (FreeRun.exit (NoInstr.halt_6373 (P := P) ω' μ' h0)) (by simp)
    rcases psiM_of_freeRunH code 0 (UInt64.ofNat w.refineGasLimit) a ((∅, []) : RefineCtx) _
        (refineHostFn_gasNonIncreasing env) (refineContractK 4611686018427387904 env)
        (refineContractK_pins 4611686018427387904 env) hY0 (hsteps.run hexit) with h | h
    · right; left
      cases hm : (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
        ((∅, []) : RefineCtx)).2.1 <;> simp_all [InvOutput.isOog, InvOutput.toWorkResult]
    · left
      obtain ⟨hrd1, hbl⟩ := hrdo
      have h7' : (ω'.get 7).toNat = buf := by
        rw [show ω'.get 7 = ω'[7] from rfl, h7]; simp; omega
      have h8' : (ω'.get 8).toNat = len := by
        rw [show ω'.get 8 = ω'[8] from rfl, h8]; simp; omega
      have hrr : μ'.rangeReadable buf len = true :=
        Services.Witness.rangeReadable_of (fun j h1 h2 => hrd1 j h1 h2) (by omega)
      have hP : (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
          ((∅, []) : RefineCtx)).2.1 = .ok ⟨(μ'.readN buf len).toArray⟩ := by
        rw [show (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
          ((∅, []) : RefineCtx)).2.1 = (freeOutput .halt ω' μ') from congrArg Prod.fst h]
        simp [freeOutput, h7', h8', hrr]
      rw [hP]
      simp only [h]
      rw [SpecRun.expTo_eq, List.take_length, hoffE, hout]
      rfl
  · right; right
    rw [← initRegs_eq] at run
    exact ⟨w, l, code, jb.code, initialRegs a, initialMemory jb a, hw, hl, hcode, by rw [hArgs]; exact hY0,
      4611686018427387904, j, N, ω', μ', x', by rw [hEnv]; exact run, hfail⟩

end Services.Bootstrap.Refine.T1c
