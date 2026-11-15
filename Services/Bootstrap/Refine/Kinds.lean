import Services.Bootstrap.Refine.Body
import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Encode.Top
import Services.Bootstrap.Spec

/-!
# The milestone's fixed-width instructions, decoded and re-encoded

For each instruction the milestone passes through (`MFixed`: `Upgrade`, `Transfer`, `Zombify`, `Eject`,
`Solicit`, `Forget`, `Lookup` with `eager = false`, `Yield`, `Checkpoint`, `Panic`, `Exported`, `Benchmark`),
`kind_of` gives one slot property R shared by the decoder (`Decode.Elems`, its `ElemOkF`) and the encoder
(`Encode.Enc`, its `EncOk`) for ℰ(i) (`Spec.Instr.encode`), with the slot's discriminant word, the loop's
pass-through test (`Pass.PassK`) and a drop that does nothing (`DropOut.NoDrop`). GP v0.8.0 Appendix B.4;
`Spec.refineInstr`'s `| i => pure i` and `.lookup s h false`.
-/

namespace Services.Bootstrap.Refine.Kinds

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Refine.Pass

/-- What the loop needs of a fixed-width instruction with encoding e passed through: one slot property R that
    its decode leaves (`dec`) and its encode reads (`enc`), with discriminant t. -/
structure FixedKind (p : ByteArray) (P : Program) (e : List UInt8) (R : List UInt8 → Prop) (t : Nat) : Prop where
  dec : ∀ F RD, Decode.Loop.Lay F RD → Decode.Loop.ElemOkF p P F RD e R
  enc : Encode.Enc.EncOk p P e R
  tag : ∀ bs, R bs → bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)
  nd : DropOut.NoDrop t
  pass : ∀ bs, R bs → PassK t (Num.decodeLE ((bs.drop 44).take 1))
  len : e.length ≤ 232
  ne : 1 ≤ e.length

/-- The instructions the milestone passes through: fixed width, `Lookup` only with `eager = false`, no
    `RandomStorageRefine`. -/
def MFixed : Spec.Instr → Prop
  | .upgrade .. | .transfer .. | .zombify _ | .eject .. | .solicit .. | .forget .. | .yield _ | .checkpoint
  | .panic | .benchmark | .exported _ => True
  | .lookup _ _ e => e = false
  | _ => False

private theorem pidx {t b : Nat} (h : PassIdx t) : PassK t b := Or.inl h

/-- A `FixedKind` from the decoder's and the encoder's theorems for the same encoding e'. -/
theorem FixedKind.of {p : ByteArray} {P : Program} {e e' : List UInt8} {R : List UInt8 → Prop} {t : Nat}
    (he : e = e') (dec : ∀ F RD, Decode.Loop.Lay F RD → Decode.Loop.ElemOkF p P F RD e' R)
    (enc : Encode.Enc.EncOk p P e' R)
    (tag : ∀ bs, R bs → bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) (nd : DropOut.NoDrop t)
    (pass : ∀ bs, R bs → PassK t (Num.decodeLE ((bs.drop 44).take 1))) (len : e'.length ≤ 232)
    (ne : 1 ≤ e'.length) : FixedKind p P e R t := by
  subst he; exact ⟨dec, enc, tag, nd, pass, len, ne⟩

theorem kind_of {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (C : Spec.Consts) (i : Spec.Instr)
    (hm : MFixed i) (hw : i.WF C) : ∃ R t, FixedKind p P i.encode R t := by
  cases i with
  | upgrade h g m =>
    obtain ⟨hh, -, -⟩ := hw
    exact ⟨_, 1, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.upgradeF F RD hL h (Codec.fixed 8 g) (Codec.fixed 8 m) hh (by simp [Codec.fixed])
        (by simp [Codec.fixed]))
      (Encode.Enc.upgrade h (Codec.fixed 8 g) (Codec.fixed 8 m) hh (by simp [Codec.fixed]) (by simp [Codec.fixed]))
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed, hh]) (by simp)⟩
  | transfer d a g memo =>
    obtain ⟨-, -, -, hm⟩ := hw
    exact ⟨_, 2, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.transferF F RD hL (Codec.fixed 4 d) (Codec.fixed 8 a) (Codec.fixed 8 g) memo
        (by simp [Codec.fixed]) (by simp [Codec.fixed]) (by simp [Codec.fixed]) hm)
      (Encode.Enc.transfer (Codec.fixed 4 d) (Codec.fixed 8 a) (Codec.fixed 8 g) memo (by simp [Codec.fixed])
        (by simp [Codec.fixed]) (by simp [Codec.fixed]) hm)
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed, hm]) (by simp)⟩
  | zombify e =>
    exact ⟨_, 3, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.zombifyF F RD hL (Codec.fixed 4 e) (by simp [Codec.fixed]))
      (Encode.Enc.zombify (Codec.fixed 4 e) (by simp [Codec.fixed]))
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed]) (by simp)⟩
  | eject t h =>
    obtain ⟨-, hh⟩ := hw
    exact ⟨_, 4, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.ejectF F RD hL (Codec.fixed 4 t) h (by simp [Codec.fixed]) hh)
      (Encode.Enc.eject (Codec.fixed 4 t) h (by simp [Codec.fixed]) hh)
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed, hh]) (by simp)⟩
  | solicit h l =>
    obtain ⟨hh, -⟩ := hw
    exact ⟨_, 6, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.solicitF F RD hL h (Codec.fixed 8 l) hh (by simp [Codec.fixed]))
      (Encode.Enc.solicit h (Codec.fixed 8 l) hh (by simp [Codec.fixed]))
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed, hh]) (by simp)⟩
  | forget h l =>
    obtain ⟨hh, -⟩ := hw
    exact ⟨_, 7, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.forgetF F RD hL h (Codec.fixed 8 l) hh (by simp [Codec.fixed]))
      (Encode.Enc.forget h (Codec.fixed 8 l) hh (by simp [Codec.fixed]))
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed, hh]) (by simp)⟩
  | lookup sv h e =>
    obtain ⟨-, hh⟩ := hw
    have he : e = false := hm
    subst he
    exact ⟨_, 8, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.lookupF F RD hL (Codec.fixed 4 sv) h 0 (by simp [Codec.fixed]) hh (by decide))
      (Encode.Enc.lookup (Codec.fixed 4 sv) h 0 (by simp [Codec.fixed]) hh)
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega)
      (fun bs h => Or.inr ⟨rfl, by rw [h.2.2.2]; decide⟩)
      (by simp [Codec.fixed, hh]) (by simp)⟩
  | yield h =>
    have hh : h.length = 32 := hw
    exact ⟨_, 14, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.yieldF F RD hL h hh) (Encode.Enc.yield h hh)
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [hh]) (by simp)⟩
  | checkpoint =>
    exact ⟨_, 15, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.unitF F RD hL 15 (by omega)) (Encode.Enc.unit 15 (by omega))
      (fun bs h => h) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp) (by simp)⟩
  | panic =>
    exact ⟨_, 16, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.unitF F RD hL 16 (by omega)) (Encode.Enc.unit 16 (by omega))
      (fun bs h => h) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp) (by simp)⟩
  | benchmark =>
    exact ⟨_, 23, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.unitF F RD hL 23 (by omega)) (Encode.Enc.unit 23 (by omega))
      (fun bs h => h) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp) (by simp)⟩
  | exported n =>
    exact ⟨_, 20, FixedKind.of (by simp [Spec.Instr.encode])
      (fun F RD hL => Decode.Elems.exportedF F RD hL (Codec.fixed 8 n) (by simp [Codec.fixed]))
      (Encode.Enc.exported (Codec.fixed 8 n) (by simp [Codec.fixed]))
      (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => pidx (by unfold PassIdx; omega))
      (by simp [Codec.fixed]) (by simp)⟩
  | _ => exact absurd hm (by simp [MFixed])

end Services.Bootstrap.Refine.Kinds
