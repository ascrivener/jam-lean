import Services.Bootstrap.Refine.SlotHeap
import Services.Bootstrap.Refine.EmptyElems

/-!
# T1c's output slots of the heap kinds' empty forms

The slots `EmptyElems` decodes, which own no chunk, are `SlotT.SlotOK` with nothing owned:

* `slotOK_blessEmpty`: `Bless(m, a, v, r, [])` (`BlessEmptyRep`, the empty `Vec` `{0, 8, 0}`);
* `slotOK_designateEmpty`: `Designate([])` (`VecNilRep (2^63 + 12) 1`);
* `slotOK_luEmpty`: `LookedUp(Some [])` (`VecNilRep (2^63 + 17) 1`, through `SlotLU.slotW_lu`).

The encoder arms read nothing (n = 0) and the drop's arm frees nothing (capacity 0). GP v0.8.0 Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotEmpty

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW
  Services.Bootstrap.Refine.SlotHeap Services.Bootstrap.Refine.EmptyElems

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Bless(m, a, v, r, [])`'s decoded slot is good**, owning nothing. -/
theorem slotOK_blessEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (m a v r : Nat) (hw : (Spec.Instr.bless m a v r []).WF C) (bs : List UInt8) (μr : Memory)
    (hE : BlessEmptyRep (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v) (Codec.fixed 4 r) bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.bless m a v r []).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨⟨h0, h8, h16, h24⟩, hm, ha, hd, hr⟩ := hE
  let R := Encode.Enc.BlessRepAt 8 (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v) (Codec.fixed 4 r) 0 []
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP 8 (16 * 0) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' _ ⟨e0, e1, e2, e3, e4, e8, e16, e24, _⟩ =>
      ⟨e0, e1, e2, e3, e4, e8, e16, e24, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact hm, by rw [hel]; exact ha, by rw [hel]; exact hd, by rw [hel]; exact hr,
      by rw [hel]; exact h8, by rw [hel]; exact h16, by rw [hel]; exact h24, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have henc : (Spec.Instr.bless m a v r []).encode = 11 :: (Codec.fixed 4 m ++ Codec.fixed 4 a ++ Codec.fixed 4 v ++
      Codec.fixed 4 r ++ Blob.encodeNat 0 ++ []) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP 8 (16 * 0),
    blessH_232 env K pb hK1 hK 8 _ _ _ _ 0 [] (by simp [Codec.fixed]) (by simp [Codec.fixed])
      (by simp [Codec.fixed]) (by simp [Codec.fixed]) rfl (by decide) (by decide), hrep, hrep,
    fun bs μ h => ⟨.bless m a v r [], hw, by
      show Decode.Bless.BlessRep _ _ _ _ _ _ bs μ
      exact (Encode.Enc.blessRep_iff _ _ _ _ 0 [] bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, fun q m h => absurd h.1 (by simp),
    Or.inr (Or.inr ⟨false, 8, ⟨0, 0, false⟩, ?_, by omega, fun h => absurd h (by simp)⟩)⟩
  refine Or.inr (Or.inl ⟨11, 0, by omega, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
    by rw [rd 16 8 (by omega)]; exact h16, by simp⟩)

/-- **`Designate([])`'s decoded slot is good**, owning nothing. -/
theorem slotOK_designateEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (hw : (Spec.Instr.designate []).WF C) (bs : List UInt8) (μr : Memory)
    (hE : VecNilRep 9223372036854775820 1 bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.designate []).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨h0, h8, h16, h24⟩ := hE
  let R := Encode.Enc.DesignateRepAt 1 0 []
  have hz : ∀ μ : Memory, μ.readN 1 (336 * 0) = Decode.VecKey336.keysRot 0 [] := fun μ => by
    simp [Memory.readN, Decode.VecKey336.keysRot]
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP 1 (336 * 0) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' _ ⟨e0, e8, e16, e24, _⟩ => ⟨e0, e8, e16, e24, hz μ'⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact h16, by rw [hel]; exact h24, hz μ⟩
  have henc : (Spec.Instr.designate []).encode = 13 :: (Blob.encodeNat 0 ++ []) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP 1 (336 * 0),
    designateH_232 env K pb hK1 hK 1 0 [] rfl (by decide) (by decide), hrep, hrep,
    fun bs μ h => ⟨.designate [], hw, (Encode.Enc.designateRep_iff 0 [] bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, fun q m h => absurd h.1 (by simp),
    Or.inr (Or.inr ⟨false, 1, ⟨0, 0, false⟩, ?_, by omega, fun h => absurd h (by simp)⟩)⟩
  refine Or.inr (Or.inl ⟨13, 0, by omega, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
    by rw [rd 16 8 (by omega)]; exact h16, by simp⟩)

/-- **`LookedUp(Some [])`'s decoded slot is good**, owning nothing. -/
theorem slotOK_luEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (bs : List UInt8) (μr : Memory) (hE : VecNilRep 9223372036854775825 1 bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.lookedUp (some [])).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨h0, h8, h16, h24⟩ := hE
  exact SlotLU.slotW_lu env K pb hK1 hK C (some []) (fun d e => by cases e; decide) 1 (by decide) el μ s _
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact h16, by rw [hel]; exact h24⟩
    (fun d e hne => by cases e; exact absurd rfl hne)

end Services.Bootstrap.Refine.SlotEmpty
