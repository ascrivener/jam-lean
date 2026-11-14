import Services.Bootstrap.Refine.Top
import Services.Bootstrap.NoInstr
import Services.Bootstrap.StartMemZ
import Services.Bootstrap.Bridge
import Services.Bootstrap.CodeA
import Services.Bootstrap.CodeF

/-!
# T1c, first milestone: bootstrap's refine on payloads of pass-through and `Export` instructions

`refine_milestone`: Ψ_R (GP v0.8.0 eq. `refinvocation`) of a work item whose code is bootstrap (`IsBootstrap`),
for a payload ℰ(`Instructions { is, salt }`) ⌢ rest of 1 ≤ |is| < 128 well-formed instructions each passed
through or `ExportSegs`, returns `Spec.refine`'s output and exports under the GP refine host functions
(`RSem.run`); or runs out of gas; or the run reaches a failed allocation (`ExhaustsHeap`). A milestone of T1c
(`docs/bootstrap-target.md`, M1), not T1c itself.
-/

namespace Services.Bootstrap.Refine.Milestone

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix Services.Bootstrap.Bridge
  Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.RunMixed Services.Bootstrap.Refine.Top
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Facts about the vendored blob** (a named hypothesis until step 10 of `docs/bootstrap-target.md` discharges
    it): a closed statement about the constant `Bridge.vendored` alone, no free variables. Its section sizes and the
    data octets the paths read are as deployed (`Prefix.layoutOk`), and its read-only data holds, at their offsets
    from 65536, the three tables refine reads: the decoder's variant table (67476, 100 octets), the encoder's
    dispatch table (67376, 100 octets) and the drop dispatch table (67760, 96 octets). -/
def VendoredFacts : Prop :=
  ∃ vb : JamBlob, vendored = some vb ∧ layoutOk vb = true ∧
    (vb.ro.toList.drop 1940).take 100 = Decode.Tag.table ∧ (vb.ro.toList.drop 1840).take 100 = Encode.Enc.table ∧
    (vb.ro.toList.drop 2224).take 96 = DropOut.dtable

/-- Y's RAM holds the read-only data at 65536 (for a blob with the deployed layout, any arguments). -/
theorem initialMemory_readN_ro (jb : JamBlob) (a : ByteArray) (hl : layoutOk jb = true)
    (ha : a.size ≤ inputSize) (o l : Nat) (hol : o + l ≤ 11608) :
    (initialMemory jb a).readN (65536 + o) l = (jb.ro.toList.drop o).take l := by
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, -⟩, -⟩, -⟩, -⟩ := hl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  apply List.ext_getElem
  · simp [Memory.length_readN, ByteArray.length_toList', hro]; omega
  · intro j h1 h2
    simp only [Memory.length_readN] at h1
    simp only [Memory.readN, List.getElem_map, List.getElem_range]
    rw [initialMemory_read jb a (65536 + o + j) (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
      (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
    rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
      ite_eq_right (by rw [hrs, hrw]; omega), ite_eq_left (by simp only [roStart, zoneSize, hro]; omega)]
    have hr0 : roStart = 65536 := rfl
    rw [hr0, show 65536 + o + j - 65536 = o + j by omega, List.getElem_take, List.getElem_drop,
      List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ByteArray.length_toList', hro]; omega)]
    rfl

/-- **The fmt summaries T1 assumes** (named hypotheses, in the approved pattern, to be discharged by the fmt
    session): for bootstrap's code and heap bounds, the service id's log line (`Prologue.ArgsLineOk`, 4742), the
    `Export` segment's line (`ExportSeg.ExportFmtOk`, 5744) and the output's `Debug` line
    (`ExitRun.DebugLineOk` for `Top.DRm C`, 6159). -/
def FmtHyps (C : Spec.Consts) : Prop :=
  ∀ (p : ByteArray) (P : Program) [HasCode p P] [CodeX.HasCodeX p P] [CodeR.HasCodeR p P] [CodeF.HasCodeF p P]
    [CodeA.HasCodeA p P] (env : RefineHost.Env), heapBounds env.code = (48, 1044430) →
    Prologue.ArgsLineOk p 134217728 env 1044430 S0 S1 ∧ ExportSeg.ExportFmtOk p 134217728 env 1044430 S0 S1 ∧
    ExitRun.DebugLineOk p 134217728 env 1044430 S0 S1 (DRm C)

/-- **T1c, first milestone** (`docs/bootstrap-target.md` M1; not T1c itself): for a work item whose code is
    bootstrap (`IsBootstrap`), core index c < 2^16, item index i < 2^16, service id < 2^32, and payload
    y = ℰ(`Instructions { is, salt }`) ⌢ rest with 1 ≤ |is| < 128 well-formed instructions, each one refine passes
    through (`MFixed`: `Upgrade`, `Transfer`, `Zombify`, `Eject`, `Solicit`, `Forget`, `Lookup` with eager = false,
    `Yield`, `Checkpoint`, `Panic`, `Benchmark`, `Exported`) or `ExportSegs`, and |y| + 48 ≤ 2^24: `Spec.refine`
    under the GP refine host functions returns some output and exports, and Ψ_R's result and exports are those;
    or Ψ_R runs out of gas (∞, no exports); or the run reaches a failed allocation (`ExhaustsHeap`: heap
    exhaustion, decision 4; that it then ends in ☇ with no exports is not yet proved).

    Not covered: eager `Lookup`, `Import`, `RandomStorageRefine`, and the variable-width instructions
    (`CreateService`, `DeleteItems`, `Bless`, `Assign`, `Designate`, `Provide`, `LookedUp`, `Imported`,
    `RandomStorageAccumulate`, `AssignForGasCost`); n ≥ 128.

    Hypotheses besides the payload's shape: `VendoredFacts` (a closed fact about the vendored blob, for step 10)
    and `FmtHyps` (the three fmt summaries). The bound |y| + 48 ≤ 2^24 is Ψ_M's argument limit Z_I = 2^24 (GP
    v0.8.0 Appendix A.7) for the arguments ℰ(c, i, s, ↕y, ℋ(p)); a valid package's payloads are far smaller
    (W_B, GP v0.8.0 eq. 14.6). GP v0.8.0 eq. `refinvocation`. -/
theorem refine_milestone (C : Spec.Consts) (hvend : VendoredFacts) (hfmt : FmtHyps C) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem)
    (l : List UInt8) (hw : p.items[i]? = some w)
    (hl : (d.get? w.service).bind (·.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList) = some l)
    (hboot : IsBootstrap l) (hc : c < 65536) (hi : i < 65536) (hs : w.service < 4294967296)
    (is : List Spec.Instr) (salt rest : List UInt8) (hy : w.payload.toList = Spec.encodePayload is salt ++ rest)
    (hsalt : salt.length = 32) (hn : 1 ≤ is.length ∧ is.length < 128) (hY : w.payload.size + 48 ≤ 16777216)
    (hwf : ∀ x ∈ is, x.WF C) (hk : ∀ x ∈ is, MFixed x ∨ ∃ ds, x = .exportSegs ds) :
    let o := psiR Params.full d c i p r imports extrinsics off
    ∃ out ex, RSem.run (Spec.refine C i w.payload.toList) (RSem.Env.of d p imports i off) = some (out, ex) ∧
      ((o.result, o.exports) = (.ok ⟨out.toArray⟩, ex) ∨ (o.result = .err .outOfGas ∧ o.exports = []) ∨
        ExhaustsHeap Params.full d c i p r imports extrinsics off) := by
  intro o
  refine ⟨_, _, by rw [hy]; exact SpecRun.run_refine C _ i is salt rest hwf (by omega) hsalt hk, ?_⟩
  obtain ⟨hsize, code, jb, vb, hcode, hjb, hvb, hro, hrw, hhp, hss, hheap, hcc, hccX, hccA, hccF, hccR⟩ := hboot
  obtain ⟨vb', hvb', hlay', t1, t2, t3⟩ := hvend
  obtain rfl : vb' = vb := Option.some.inj (hvb'.symm.trans hvb)
  have hlay : layoutOk jb = true := by unfold layoutOk; rw [hro, hrw, hhp, hss]; exact hlay'
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI : HasCode jb.code P := ⟨hP⟩
  haveI : CodeX.HasCodeX jb.code P := CodeX.HasCodeX.of hP hccX
  haveI : CodeA.HasCodeA jb.code P := CodeA.HasCodeA.of hP hccA
  haveI : CodeF.HasCodeF jb.code P := CodeF.HasCodeF.of hP hccF
  haveI : CodeR.HasCodeR jb.code P := CodeR.HasCodeR.of hP hccR
  -- the expected outcome
  have hspec := SpecRun.run_refine C (RSem.Env.of d p imports i off) i is salt rest hwf (by omega) hsalt hk
  -- Ψ_R's steps up to Ψ_M
  show (let o := psiR Params.full d c i p r imports extrinsics off
    (o.result, o.exports) = (.ok ⟨(Spec.encodeOutput (is.map outI) i).toArray⟩,
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
  generalize hE : RefineHost.Env.mk Params.full w.service d p.context.lookupAnchorSlot code off
    (FetchContext.mk Params.full (some p) (some (List.replicate 32 0)) (some r) (some i) (some imports)
      (some extrinsics) none) = env at hEnv ⊢
  have hcodeE : env.code = code := by rw [← hE]
  have hparE : env.fetch.params = Params.full := by rw [← hE]
  have hoffE : env.exportOffset = off := by rw [← hE]
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
  obtain ⟨hfA, hfE, hfD⟩ := hfmt jb.code P env (by rw [hcodeE, hheap])
  rcases Top.refine_core (p := jb.code) (P := P) env C (by rw [hcodeE, hheap]) hparE hfA hfE hfD is salt rest hsalt
      hn hwf hk (initialMemory jb a) hSM hZ c i w.service (Blake2b.hash256 ⟨p.encode.toArray⟩).toList y hc hi hs hh hy
      (by omega) a.size hLsum.symm (by omega)
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
    have hexit : FreeRunH jb.code (refineContractK 134217728 env) 6373 ω' μ'
        (expTo env is ((∅, []) : RefineCtx) is.length) .halt ω' μ' (expTo env is ((∅, []) : RefineCtx) is.length) :=
      .exit (FreeRun.exit (NoInstr.halt_6373 (P := P) ω' μ' h0)) (by simp)
    rcases psiM_of_freeRunH code 0 (UInt64.ofNat w.refineGasLimit) a ((∅, []) : RefineCtx) _
        (refineHostFn_gasNonIncreasing env) (refineContractK 134217728 env) (refineContractK_pins 134217728 env) hY0
        (hsteps.run hexit) with h | h
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
      have hX : (psiM code 0 (UInt64.ofNat w.refineGasLimit) a (toHostFn (RefineHost.dispatch env))
          ((∅, []) : RefineCtx)).2.2 = expTo env is ((∅, []) : RefineCtx) is.length := congrArg Prod.snd h
      rw [hP]
      simp only [h]
      rw [SpecRun.expTo_eq, List.take_length, hoffE, hout]
      rfl
  · right; right
    rw [← initRegs_eq] at run
    exact ⟨w, l, code, jb.code, initialRegs a, initialMemory jb a, hw, hl, hcode, by rw [hArgs]; exact hY0,
      134217728, j, N, ω', μ', x', by rw [hEnv]; exact run, hfail⟩

end Services.Bootstrap.Refine.Milestone
