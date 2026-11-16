import Services.Bootstrap.Refine.SlotFixed
import Services.Bootstrap.Refine.SlotHeap
import Services.Bootstrap.Refine.SlotVV
import Services.Bootstrap.Refine.SlotEmpty
import Services.Bootstrap.Refine.LoopT

/-!
# T1c's per-instruction decode packages (part 1: the forms that own no chunk)

For an instruction x that refine passes through, `DecPkg … x (PassSlot … x)` packages what T1c's run needs of it:
an element decoder for x's encoding (`VecVecOwn.ElemOkAFC`, for `DecodeCG.decode_allC`) whose slot predicate `Rd`,
for every memory that keeps the decode's chunks cs as in a reference memory μr, gives `PassSlot`: the slot's word
`PassW` (what the transform loop passes through, `LoopAll.PassOk`) and the slot `SlotT.SlotOK` for x's encoding,
owning chunks of cs (what the exit needs, `ExitRunW.exit_runW`).

This file: the milestone's fixed kinds (`pkg_fixed`) and the variable-width kinds' forms that allocate nothing:
`LookedUp(None)`, `Provide(s, Hash h)`, `CreateService` with no code or an empty one,
`RandomStorageAccumulate(Err)`, and the empty `Bless`, `Designate`, `LookedUp(Some [])`, `DeleteItems`, `Imported`.
GP v0.8.0 Appendix B.4 (Ψ_R), B.7 (the instruction list), Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.PkgT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.GrowH Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.Kinds
  Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.SlotHeap Services.Bootstrap.Refine.EmptyElems

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A passed-through slot, as the loop and the exit need it**: its word D is one the loop passes through
    (`PassW`, with the flag octet 44), and the slot is `SlotOK` for x's encoding owning chunks of cs. -/
def PassSlot (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program) (C : Spec.Consts) (x : Spec.Instr)
    (cs : List Chunk) (bs : List UInt8) (μr : Memory) : Prop :=
  ∃ (D : Nat) (own : Chunk → Prop), PassW D (Num.decodeLE ((bs.drop 44).take 1)) ∧
    bs.take 8 = Num.encodeLE 8 D ∧ SlotOK env K pb p P (DRt C 0) x.encode bs own μr ∧ (∀ c, own c → c ∈ cs)

/-- **x's decode package**: an element decoder for x's encoding whose slot predicate gives `Step` in every memory
    that keeps the decode's chunks as in μr. -/
def DecPkg (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program)
    (x : Spec.Instr) (Step : List Chunk → List UInt8 → Memory → Prop) : Prop :=
  ∃ (N : Nat) (Rd : List Chunk → List UInt8 → Memory → Prop),
    (∀ F RD, Lay F RD → Decode.VecVecOwn.ElemOkAFC env cap pb gl p P F RD N x.encode Rd) ∧
    ∀ cs bs μr, (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μr.read a) → Rd cs bs μ'') →
      Step cs bs μr

/-- A package from an `ElemOkAF` whose slot predicate does not depend on memory. -/
theorem pkg_ofAF {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {x : Spec.Instr} {Step : List Chunk → List UInt8 → Memory → Prop} {N : Nat} {Rep : List UInt8 → Prop}
    (hF : ∀ F RD, Lay F RD → ElemOkAF env cap pb gl p P F RD N x.encode (fun bs _ => Rep bs))
    (h : ∀ cs bs μr, Rep bs → Step cs bs μr) : DecPkg env cap pb gl p P x Step :=
  ⟨N, fun _ bs _ => Rep bs, fun F RD hL => ElemOkAF.toAFC (hF F RD hL), fun cs bs μr hR => h cs bs μr (hR μr
    (fun _ _ _ _ => rfl))⟩

/-- A package from an `ElemOkF` (nothing allocated). -/
theorem pkg_ofF {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {x : Spec.Instr} {Step : List Chunk → List UInt8 → Memory → Prop} {Rep : List UInt8 → Prop}
    (hF : ∀ F RD, Lay F RD → ElemOkF p P F RD x.encode Rep)
    (h : ∀ cs bs μr, Rep bs → Step cs bs μr) : DecPkg env cap pb gl p P x Step :=
  pkg_ofAF (fun F RD hL => ElemOkAF.of_elemOkF hL (hF F RD hL)) h

/-- `PassSlot` with nothing owned, from the slot's word and a `SlotOK` owning nothing. -/
theorem passSlot_noown {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {C : Spec.Consts}
    {x : Spec.Instr} {cs : List Chunk} {bs : List UInt8} {μr : Memory} (D : Nat)
    (hW : PassW D (Num.decodeLE ((bs.drop 44).take 1))) (h0 : bs.take 8 = Num.encodeLE 8 D)
    (hS : SlotOK env K pb p P (DRt C 0) x.encode bs (fun _ => False) μr) :
    PassSlot env K pb p P C x cs bs μr :=
  ⟨D, fun _ => False, hW, h0, hS, fun _ h => h.elim⟩

/-- A discriminant 2^63 − 1 + t of a passed-through index t is `PassW` whatever the flag. -/
theorem passW_idx {t b : Nat} (h : PassIdx t) : PassW (9223372036854775807 + t) b := PassW.ofK (Or.inl h)

/-- **The milestone's fixed kinds**: `FixedKind`'s decoder, and `slotOK_fixed`. -/
theorem pkg_fixed {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (x : Spec.Instr) (hm : MFixed x) (hw : x.WF C) :
    DecPkg env K pb gl p P x (PassSlot env K pb p P C x) := by
  obtain ⟨t, hk⟩ := kind_of (p := p) (P := P) C x hm hw
  exact pkg_ofF hk.dec (fun cs bs μr h => passSlot_noown _ (PassW.ofK (hk.pass bs h)) (hk.tag bs h)
    (SlotFixed.slotOK_fixed env K pb hK1 hK C x hm hw bs h μr))

/-- **`LookedUp(None)`** ([18, 0]). -/
theorem pkg_luNone {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) :
    DecPkg env K pb gl p P (.lookedUp none) (PassSlot env K pb p P C (.lookedUp none)) := by
  have he : (Spec.Instr.lookedUp none).encode = [18, 0] := by simp [Spec.Instr.encode, Spec.opt]
  refine pkg_ofF (fun F RD hL => he ▸ Decode.LookupProvideElem.looked_up_noneF F RD hL) (fun cs bs μr h => ?_)
  refine ⟨9223372036854775807 + 18, fun _ => False, passW_idx (by unfold PassIdx; omega), h.1, ?_, fun _ h => h.elim⟩
  intro μ s el hel _
  exact SlotLU.slotW_lu env K pb hK1 hK C none (fun d e => by cases e) 0 (by decide) el μ s _
    ⟨by rw [hel]; exact h.1, by rw [hel]; exact h.2⟩ (fun d e => by cases e)

/-- **`Provide(s, Hash h)`** (17 :: ℰ₄(s) ++ 0 :: h). -/
theorem pkg_provideHash {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (sv : Nat) (h : List UInt8) (hw : (Spec.Instr.provide sv (.hash h)).WF C) :
    DecPkg env K pb gl p P (.provide sv (.hash h)) (PassSlot env K pb p P C (.provide sv (.hash h))) := by
  have hw' := hw
  obtain ⟨hs, hh⟩ := hw'
  have he : (Spec.Instr.provide sv (.hash h)).encode = 17 :: (Codec.fixed 4 sv ++ 0 :: h) := by
    simp [Spec.Instr.encode]
  refine pkg_ofF (fun F RD hL => he ▸ Decode.LookupProvideElem.provide_hashF F RD hL (Codec.fixed 4 sv) h
    (by simp [Codec.fixed]) hh) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1
    (slotOK_provideHash env K pb hK1 hK C sv h hw _ bs hb μr)

/-- **`RandomStorageAccumulate(Err)`** ([22, 1]). -/
theorem pkg_rsaErr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) :
    DecPkg env K pb gl p P (.randomStorageAccumulate none)
      (PassSlot env K pb p P C (.randomStorageAccumulate none)) := by
  have he : (Spec.Instr.randomStorageAccumulate none).encode = [22, 1] := by simp [Spec.Instr.encode]
  refine pkg_ofF (fun F RD hL => he ▸ random_storage_errF F RD hL) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1 (slotOK_rsaErr env K pb hK1 hK C _ bs hb μr)

/-- **`LookedUp(Some [])`** ([18, 1, 0]). -/
theorem pkg_luEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) :
    DecPkg env K pb gl p P (.lookedUp (some [])) (PassSlot env K pb p P C (.lookedUp (some []))) := by
  have he : (Spec.Instr.lookedUp (some [])).encode = [18, 1, 0] := by
    simp [Spec.Instr.encode, Spec.opt, Spec.bytes, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ looked_up_emptyF F RD hL) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1
    (SlotEmpty.slotOK_luEmpty env K pb hK1 hK C bs μr hb)

/-- **`Designate([])`** ([13, 0]; it reads the core count, `ElemOkFG`). -/
theorem pkg_designateEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (hw : (Spec.Instr.designate []).WF C) :
    DecPkg env K pb gl p P (.designate []) (PassSlot env K pb p P C (.designate [])) := by
  have he : (Spec.Instr.designate []).encode = [13, 0] := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofAF (fun F RD hL => he ▸ of_elemOkFG hL (designate_emptyF F RD hL)) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1
    (SlotEmpty.slotOK_designateEmpty env K pb hK1 hK C hw bs μr hb)

/-- **`Bless(m, a, v, r, [])`**. -/
theorem pkg_blessEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (m a v r : Nat) (hw : (Spec.Instr.bless m a v r []).WF C) :
    DecPkg env K pb gl p P (.bless m a v r []) (PassSlot env K pb p P C (.bless m a v r [])) := by
  have he : (Spec.Instr.bless m a v r []).encode =
      11 :: (Codec.fixed 4 m ++ Codec.fixed 4 a ++ Codec.fixed 4 v ++ Codec.fixed 4 r ++ [0]) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ bless_emptyF F RD hL _ _ _ _ (by simp [Codec.fixed]) (by simp [Codec.fixed])
    (by simp [Codec.fixed]) (by simp [Codec.fixed])) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1.1
    (SlotEmpty.slotOK_blessEmpty env K pb hK1 hK C m a v r hw bs μr hb)

/-- **`DeleteItems([])`** ([5, 0]). -/
theorem pkg_deleteItemsEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) :
    DecPkg env K pb gl p P (.deleteItems []) (PassSlot env K pb p P C (.deleteItems [])) := by
  have he : (Spec.Instr.deleteItems []).encode = [5, 0] := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ Decode.ExportEmpty.delete_items_emptyF F RD hL) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1
    (SlotVV.slotOK_deleteItemsEmpty env K pb hK1 hK C bs μr hb)

/-- **`Imported([])`** ([19, 0]). -/
theorem pkg_importedEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) :
    DecPkg env K pb gl p P (.imported []) (PassSlot env K pb p P C (.imported [])) := by
  have he : (Spec.Instr.imported []).encode = [19, 0] := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ Decode.ExportEmpty.imported_emptyF F RD hL) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (by unfold PassIdx; omega)) hb.1
    (SlotVV.slotOK_importedEmpty env K pb hK1 hK C bs μr hb)

end Services.Bootstrap.Refine.PkgT
