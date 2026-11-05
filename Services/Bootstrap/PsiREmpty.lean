import Services.Bootstrap.EmptyPayload
import Services.Witness.Args
import JAM.Theorems.RefineContract
import JAM.Theorems.HostGas

/-!
# Bootstrap's Ψ_R on the empty payload

`EmptyPayload.run_empty` (the gas-free run from Y's state to the trap at 6377) through the lift to
Ψ_M (`psiM_of_freeRunH`, GP §A.8) and Ψ_R (GP eq. `refinvocation`).
-/

namespace Services.Bootstrap.PsiREmpty

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Prefix
  Services.Bootstrap.EmptyPayload

/-- **The trap** at 6377: `trap` panics (GP §A.5.1: ε = ☇), leaving registers and memory as they
    are. -/
theorem trap_6377 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) :
    FreeExit p 6377 ω μ .panic ω μ := by
  have hd := d_6377 (p := p) (P := P)
  have hs : P.freeStep 6377 ω μ = (.panic, P.next 6377, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- **Ψ_M panics or runs out of gas**, given a gas-free run from Y's state to the trap at 6377. -/
theorem psiM_of_trap {p : ByteArray} {P : Program} [HasCode p P] (code a : ByteArray) (gas : UInt64)
    (env : RefineHost.Env) {ω₀ : Regs} {μ₀ : Memory}
    (hY : standardInit code a = some (p, ω₀, μ₀)) (N : Nat)
    (hrun : ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω₀ μ₀ ((∅, []) : RefineCtx) 6377 ω' μ' x' N) :
    (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 = .panic ∨
      (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 = .oog := by
  obtain ⟨ω', μ', x', hsteps⟩ := hrun
  have hexit : FreeRunH p (refineContract env) 6377 ω' μ' x' .panic ω' μ' x' :=
    .exit (FreeRun.exit (trap_6377 (P := P) ω' μ')) (by simp)
  rcases psiM_of_freeRunH code 0 gas a ((∅, []) : RefineCtx) _ (refineHostFn_gasNonIncreasing env)
      (refineContract env) (refineContract_pins env) hY (hsteps.run hexit) with h | h
  · right
    cases hm : (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 <;>
      simp_all [InvOutput.isOog]
  · left
    rw [show (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.1 =
      (freeOutput .panic ω' μ') from congrArg Prod.fst h]
    rfl

theorem hash256_length (m : ByteArray) : (Blake2b.hash256 m).toList.length = 32 := by
  rw [ByteArray.toList_eq_data]
  simp [Blake2b.hash256, Blake2b.hash]

/-- **Bootstrap's refine panics on the empty payload** (GP eq. `refinvocation`). For a work item
    whose service's code, looked up historically, is a blob with the deployed layout that passes
    `checkCode` for bootstrap's code facts (`lake build bootstrapcheck` checks both of the vendored
    blob) and the deployed heap bounds, refined with the full-chain parameters: for every core
    index c < 2^16, item index i < 2^16 and service id < 2^32, with an empty payload, Ψ_R's result
    is ☇ (panic), or ∞. -/
theorem psiR_empty (params : Params) (hpar : params = Params.full) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (w : WorkItem) (hw : p.items[i]? = some w) (l : List UInt8)
    (hl : (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot
      w.codeHash.toList) = some l)
    (hsize : l.length ≤ Constants.Cmaxservicecodesize) (code : ByteArray)
    (hcode : splitMetadata l = some code) (jb : JamBlob) (hjb : JamBlob.parse? code = some jb)
    (hlay : layoutOk jb = true) (hcc : checkCode jb.code facts = true)
    (hheap : heapBounds code = (48, 1044430)) (hc : c < 65536) (hi : i < 65536)
    (hs : w.service < 4294967296) (hy : w.payload.size = 0) :
    (psiR params d c i p r imports extrinsics off).result = .err .panic ∨
      (psiR params d c i p r imports extrinsics off).result = .err .outOfGas := by
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI : HasCode jb.code P := ⟨hP⟩
  simp only [psiR, hw, hl]
  rw [ite_eq_right (by omega)]
  simp only [hcode]
  generalize hE : RefineHost.Env.mk params w.service d p.context.lookupAnchorSlot code off
    (FetchContext.mk params (some p) (some (List.replicate 32 0)) (some r) (some i) (some imports)
      (some extrinsics) none) = env
  have hcodeE : env.code = code := by rw [← hE]
  have hparE : env.fetch.params = params := by rw [← hE]
  generalize hA : (⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
    (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩ : ByteArray) = a
  have hlist : a.toList = Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat 0 ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList := by
    have h0 : w.payload.toList = [] := by
      rw [← ByteArray.length_toList'] at hy; exact List.eq_nil_of_length_eq_zero hy
    rw [← hA]
    simp only [Codec.var, Codec.nat, ← ByteArray.length_toList' w.payload, h0, List.length_nil,
      List.append_nil]
    rw [ByteArray.toList_eq_data]
  have hasize : a.size = (Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat 0 ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).length := by
    rw [← hlist, ByteArray.length_toList']
  have hwC := encodeNat_len_le3 c hc
  have hwI := encodeNat_len_le3 i hi
  have hwS := encodeNat_len_le5 w.service hs
  have hw0 : (Blob.encodeNat 0).length = 1 := by simp [Blob.encodeNat]
  have hh := hash256_length ⟨p.encode.toArray⟩
  have ha : a.size ≤ inputSize := by
    rw [hasize]; simp only [List.length_append, hh, hw0, inputSize]; omega
  have hSM := startMem_initial jb a hlay ha
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheapP⟩, hstack⟩, _⟩, _⟩ := hlay
  have hY : standardInit code a = some (jb.code, initialRegs a, initialMemory jb a) := by
    have hfit : ¬(5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32) := by
      rw [hro, hrw, hheapP, hstack]; decide
    unfold standardInit validJamBlob?
    rw [ite_eq_right (by omega), hjb, Option.bind_some, ite_eq_right hfit]
    rfl
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  have hmem := initialMemory_readN_args jb a (by simp [roStart, zoneSize, hro, two32])
    (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)
  rw [hlist, hasize] at hmem
  have hrun := run_empty jb.code P env (by rw [hcodeE, hheap]) (by rw [hparE, hpar])
    (initialMemory jb a) hSM c i w.service (Blake2b.hash256 ⟨p.encode.toArray⟩).toList hc hi hs hh
    (by simpa [argStart, zoneSize, inputSize] using hmem)
    (fun j h1 h2 => initialMemory_readable_args jb a j (by simp [argStart, zoneSize, inputSize]; omega)
      (by rw [hasize]; simp [argStart, zoneSize, inputSize] at h2 ⊢; omega))
  rw [← hasize, ← initRegs_eq] at hrun
  rcases psiM_of_trap (P := P) code a (UInt64.ofNat w.refineGasLimit) env hY 8000 hrun with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

end Services.Bootstrap.PsiREmpty
