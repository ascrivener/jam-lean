import Services.Witness.BadPayload
import Services.Witness.PsiRLift

/-!
# Witness's Ψ_R on a payload with a bad tag

`BadPayload.run_badTag` (the gas-free run from Y's state to the halt with [12, 0]) through
`psiR_of_run` (the lift to Ψ_M and Ψ_R).
-/

namespace Services.Witness.PsiR

open PVM JAM Services.Witness Services.Witness.Code Services.Witness.Prefix
  Services.Witness.BadPayload

theorem hash256_length (m : ByteArray) : (Blake2b.hash256 m).toList.length = 32 := by
  rw [ByteArray.toList_eq_data]
  simp [Blake2b.hash256, Blake2b.hash]

/-- **Witness's refine rejects a payload with a bad tag** (GP eq. `refinvocation`). For a work
    item whose service's code, looked up historically, is a blob with the deployed layout that
    passes `checkCode` for witness's code facts (`lake build witnesscheck` checks both of the
    vendored blob) and the deployed heap bounds, refined with the full-chain parameters: for every
    core index c < 2^16, item index i < 2^16, service id < 2^32 and payload of 1 to 15 octets whose
    first octet is at least 12, Ψ_R's result is ℰ(`Rejected(BadPayload)`) = [12, 0], or ∞. -/
theorem psiR_badTag (params : Params) (hpar : params = Params.full) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (w : WorkItem) (hw : p.items[i]? = some w) (l : List UInt8)
    (hl : (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot
      w.codeHash.toList) = some l)
    (hsize : l.length ≤ Constants.Cmaxservicecodesize) (code : ByteArray)
    (hcode : splitMetadata l = some code) (jb : JamBlob) (hjb : JamBlob.parse? code = some jb)
    (hlay : layoutOk jb = true) (hcc : checkCode jb.code facts = true)
    (hheap : heapBounds code = (48, 1044368)) (hc : c < 65536) (hi : i < 65536)
    (hs : w.service < 4294967296) (hy : 1 ≤ w.payload.size ∧ w.payload.size ≤ 15)
    (htag : 12 ≤ (w.payload.toList.headD 0).toNat) :
    (psiR params d c i p r imports extrinsics off).result = .ok ⟨#[12, 0]⟩ ∨
      (psiR params d c i p r imports extrinsics off).result = .err .outOfGas := by
  refine psiR_of_run params d c i p r imports extrinsics off w hw l hl hsize code hcode jb hjb hlay hcc
    (fun P _ env hcodeE hparE => ?_)
  intro a
  have hlist : a.toList = Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat w.payload.toList.length ++ w.payload.toList ++
      (Blake2b.hash256 ⟨p.encode.toArray⟩).toList := by
    simp only [a, Codec.var, Codec.nat, ← ByteArray.length_toList' w.payload, List.append_assoc]
    rw [ByteArray.toList_eq_data]
  have hasize : a.size = (Blob.encodeNat c ++ Blob.encodeNat i ++ Blob.encodeNat w.service ++
      Blob.encodeNat w.payload.toList.length ++ w.payload.toList ++
      (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).length := by
    rw [← hlist, ByteArray.length_toList']
  have hwC := encodeNat_length_le3 c hc
  have hwI := encodeNat_length_le3 i hi
  have hwS := encodeNat_length_le5 w.service hs
  have hwY := encodeNat_length_le3 w.payload.toList.length (by rw [ByteArray.length_toList']; omega)
  have hh := hash256_length ⟨p.encode.toArray⟩
  have hplen : w.payload.toList.length = w.payload.size := ByteArray.length_toList' _
  have ha : a.size ≤ inputSize := by
    rw [hasize]; simp only [List.length_append, hh, inputSize]; omega
  refine ⟨ha, ?_⟩
  have hY := startMem_initial jb a hlay ha
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheapP⟩, hstack⟩, _⟩, _⟩ := hlay
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  have hmem := initialMemory_readN_args jb a (by simp [roStart, zoneSize, hro, two32])
    (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)
  rw [hlist, hasize] at hmem
  obtain ⟨ω', μ', x', hrun, h0, h7, h8, hb0, hb1, hr0, hr1⟩ := run_badTag jb.code P env
    (by rw [hcodeE, hheap]) (by rw [hparE, hpar]) (initialMemory jb a) hY c i w.service
    w.payload.toList (Blake2b.hash256 ⟨p.encode.toArray⟩).toList hc hi hs
    (by rw [hplen]; exact hy) htag hh (by simpa [argStart, zoneSize, inputSize] using hmem)
    (fun j h1 h2 => initialMemory_readable_args jb a j (by simp [argStart, zoneSize, inputSize]; omega)
      (by rw [hasize]; simp [argStart, zoneSize, inputSize] at h2 ⊢; omega))
  refine ⟨ω', μ', x', ?_, h0, h7, h8, hb0, hb1, hr0, hr1⟩
  rw [initRegs_eq, hasize]
  exact hrun

end Services.Witness.PsiR
