import Services.Bootstrap.Refine.SlotT

/-!
# T1c's output slots of the milestone's fixed-width kinds

`kind_okH`: the encoder arm (`EncOkMH 232`, no heap octets) of every kind the milestone passes through
(`Kinds.MFixed`), with the slot representation `Kinds.kindRep`. `slotOK_fixed`: such a slot is `SlotT.SlotOK` with no
owned chunks (its drop does nothing). GP v0.8.0 Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotFixed

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Encode.EncMH Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.SlotT

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem ok_of {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {D : Nat} {e e' : List UInt8}
    {R : List UInt8 → Memory → Prop} {S : Nat → Nat → Prop} (he : e = e') (h : EncOkMH env K pb p P D e' R S) :
    EncOkMH env K pb p P D e R S := he ▸ h

/-- **The encoder arm of a milestone kind**: every `MFixed` well-formed instruction encodes from its `kindRep` slot,
    reading no heap octets (`EncOkMH 232`). -/
theorem kind_okH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (i : Spec.Instr) (hm : MFixed i) (hw : i.WF C) :
    EncOkMH env K pb p P 232 i.encode (fun bs _ => kindRep i bs) (fun _ _ => False) := by
  cases i with
  | upgrade h g m =>
    obtain ⟨hh, -, -⟩ := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((upgradeH env K pb hK1 hK h (Codec.fixed 8 g) (Codec.fixed 8 m) hh
      (by simp [Codec.fixed]) (by simp [Codec.fixed])).mono (by decide))
  | transfer d a g memo =>
    obtain ⟨-, -, -, hm⟩ := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((transferH env K pb hK1 hK (Codec.fixed 4 d) (Codec.fixed 8 a)
      (Codec.fixed 8 g) memo (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) hm).mono
      (by decide))
  | zombify e =>
    exact ok_of (by simp [Spec.Instr.encode]) ((zombifyH env K pb hK1 hK (Codec.fixed 4 e)
      (by simp [Codec.fixed])).mono (by decide))
  | eject t h =>
    obtain ⟨-, hh⟩ := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((ejectH env K pb hK1 hK (Codec.fixed 4 t) h
      (by simp [Codec.fixed]) hh).mono (by decide))
  | solicit h l =>
    obtain ⟨hh, -⟩ := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((solicitH env K pb hK1 hK h (Codec.fixed 8 l) hh
      (by simp [Codec.fixed])).mono (by decide))
  | forget h l =>
    obtain ⟨hh, -⟩ := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((forgetH env K pb hK1 hK h (Codec.fixed 8 l) hh
      (by simp [Codec.fixed])).mono (by decide))
  | lookup sv h e =>
    obtain ⟨-, hh⟩ := hw
    have he : e = false := hm
    subst he
    exact ok_of (by simp [Spec.Instr.encode]) ((lookupH env K pb hK1 hK (Codec.fixed 4 sv) h 0
      (by simp [Codec.fixed]) hh).mono (by decide))
  | yield h =>
    have hh : h.length = 32 := hw
    exact ok_of (by simp [Spec.Instr.encode]) ((yieldH env K pb hK1 hK h hh).mono (by decide))
  | checkpoint => exact ok_of rfl ((unitH env K pb hK1 hK 15 (by omega)).mono (by decide))
  | panic => exact ok_of rfl ((unitH env K pb hK1 hK 16 (by omega)).mono (by decide))
  | benchmark => exact ok_of rfl ((unitH env K pb hK1 hK 23 (by omega)).mono (by decide))
  | exported n =>
    exact ok_of (by simp [Spec.Instr.encode]) ((exportedH env K pb hK1 hK (Codec.fixed 8 n)
      (by simp [Codec.fixed])).mono (by decide))
  | _ => exact absurd hm (by simp [MFixed])

/-- **A milestone kind's slot is good everywhere**: the slot octets bs of an `MFixed` well-formed instruction i
    (`kindRep i bs`) are `SlotOK` for i's encoding with no owned chunks, in any reference memory. -/
theorem slotOK_fixed {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (i : Spec.Instr) (hm : MFixed i) (hw : i.WF C) (bs : List UInt8) (hb : kindRep i bs)
    (μr : Memory) : SlotOK env K pb p P (DRt C 0) i.encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨t, hkind⟩ := kind_of (p := p) (P := P) C i hm hw
  refine ⟨fun bs _ => kindRep i bs, fun bs _ => kindRep i bs, fun _ _ => False,
    kind_okH env K pb hK1 hK C i hm hw, by rw [hel]; exact hb, by rw [hel]; exact hb,
    fun bs μ h => ⟨i, hw, (slotRep_fixed hm bs μ).mpr h⟩, fun _ _ _ _ h => h, fun _ _ _ _ h => h,
    fun _ _ h => h.elim, Or.inl ⟨t, hkind.nd, ?_⟩⟩
  rw [← readN_take μ el 232 8 (by omega), hel]
  exact hkind.tag bs hb

end Services.Bootstrap.Refine.SlotFixed
