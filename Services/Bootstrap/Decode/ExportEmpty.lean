import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Decode.LoopA
import Services.Bootstrap.Decode.VecEmpty

/-!
# The single-`Vec` variants with no elements, as elements of the decode loop

`DeleteItems { keys: [] }` (tag 5), `Export { data: [] }` (tag 10) and `Imported { data: [] }` (tag 19)
(GP v0.8.0 B.7, the bootstrap service's instruction list), each encoded as [t, 0] (the tag octet, then
ℰ(0) = 0), stated at the decode loop's frame base F (the tag at F, the slot at F + 120, the reader at
RD, laid out as `Lay F RD`), from `VecEmpty.vec_empty`:

* `vec_emptyF`: the three at once, as an `ElemOkF`: the slot holds the discriminant W and then
  `{cap 0, ptr 8, len 0}`;
* `delete_items_emptyF`, `export_emptyF`, `imported_emptyF`: the instances (W = 2^63 + 4, 2^63 + 9,
  2^63 + 18);
* `export_empty_elem`: `export_emptyF` as an `ElemOkAF` (nothing is allocated).
-/

namespace Services.Bootstrap.Decode.ExportEmpty

open PVM Services.Bootstrap Services.Bootstrap.Code JAM Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.VecEmpty

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The slot of an empty single-`Vec` variant: the discriminant W, then `{cap 0, ptr 8, len 0}`. -/
def VecEmptyRep (W : Nat) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 W ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0

/-- **The single-`Vec` variants with no elements** (tags 5, 10, 19): the encoding [t, 0] decodes to a
    slot holding the discriminant W and then `{cap 0, ptr 8, len 0}`. -/
theorem vec_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (tag h r1 r2 r3 W : Nat)
    (htag : (tag = 5 ∧ h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ W = 9223372036854775812) ∨
      (tag = 10 ∧ h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ W = 9223372036854775826)) :
    ElemOkF p P F RD [UInt8.ofNat tag, 0] (VecEmptyRep W) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  have hs : Shape h r1 r2 r3 8 := by
    unfold Shape
    rcases htag with ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ <;> simp
  have htag' : (tag = 5 ∧ h = 21522 ∧ W = 9223372036854775812) ∨ (tag = 10 ∧ h = 21871 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ W = 9223372036854775826) ∨ (tag = 9 ∧ h = 21028 ∧ W = 9223372036854775816) := by
    omega
  have hW : W < 18446744073709551616 ∧ W ≠ 18446744073709551614 := by omega
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tagr rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one, List.headD_cons,
    List.tail_cons] at tagr hlen hptr hpb pay rpay ⊢
  have hzero : μ.read ptr = 0 := by simpa [Memory.readN] using pay
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, eO24, eR0, eR8, efr, erd, ewr⟩ :=
    vec_empty (p := p) (P := P) (R := R) x ω μ tag h r1 r2 r3 8 W F (F + 120) 18 723 v5 v6 RD ptr len
      (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) hs htag' (by omega) h6 h7 tagr tab rt
      ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL hzero (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
      (rpay ptr (Nat.le_refl _) (by omega))
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨W, hW.1, eO, hW.2⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  refine ⟨(slot_parts μ' (F + 120) 0 8 (by omega)).1.trans eO, ?_, ?_, ?_⟩
  · exact (slot_parts μ' (F + 120) 8 8 (by omega)).2.trans eO8
  · rw [(slot_parts μ' (F + 120) 16 8 (by omega)).2, show F + 120 + 16 = F + 120 + 8 + 8 by omega]; exact eO16
  · rw [(slot_parts μ' (F + 120) 24 8 (by omega)).2, show F + 120 + 24 = F + 120 + 8 + 16 by omega]; exact eO24

/-- **`DeleteItems { keys: [] }`** (tag 5): the encoding [5, 0] decodes to a slot holding the
    discriminant 2^63 + 4 and then `{cap 0, ptr 8, len 0}`. -/
theorem delete_items_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [5, 0]
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775812 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0) :=
  vec_emptyF F RD hL 5 21522 990 1088 1090 9223372036854775812 (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- **`Export { data: [] }`** (tag 10): the encoding [10, 0] decodes to a slot holding the
    discriminant 2^63 + 9 and then `{cap 0, ptr 8, len 0}`. -/
theorem export_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [10, 0]
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0) :=
  vec_emptyF F RD hL 10 21871 1010 1110 1112 9223372036854775817
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))

/-- **`Imported { data: [] }`** (tag 19): the encoding [19, 0] decodes to a slot holding the
    discriminant 2^63 + 18 and then `{cap 0, ptr 8, len 0}`. -/
theorem imported_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [19, 0]
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775826 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0) :=
  vec_emptyF F RD hL 19 22072 1022 1170 1172 9223372036854775826
    (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))

/-- **`Export { data: [] }`, as an `ElemOkAF`**: nothing is allocated. -/
theorem export_empty_elem {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray}
    {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkAF env cap pb gl p P F RD 4000 [10, 0]
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0) :=
  ElemOkAF.of_elemOkF hL (export_emptyF F RD hL)

end Services.Bootstrap.Decode.ExportEmpty
