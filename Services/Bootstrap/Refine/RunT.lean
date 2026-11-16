import Services.Bootstrap.Refine.InvT
import Services.Bootstrap.Refine.RunMixedG

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

end Services.Bootstrap.Refine.RunT
