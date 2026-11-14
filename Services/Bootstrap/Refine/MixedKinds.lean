import Services.Bootstrap.Refine.RunMixed

/-!
# The milestone's instructions as `run_mixed` takes them

`mixed_kinds`: for well-formed instructions, each passed through (`Kinds.MFixed`) or `ExportSegs`, whose encodings
take fewer than 2^24 octets, the slot properties `Rs j` and discriminants `ts j` that `RunMixed.run_mixed` asks for:
a `FixedKind` for the output instruction `outI` (from `Kinds.kind_of`, or `Exported |ds|`), and for an `Export`
its bounds (≤ 2^26 segments of < 2^30 octets, from the length). GP v0.8.0 Appendix B.4; `Spec.refineInstr`.
-/

namespace Services.Bootstrap.Refine.MixedKinds

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Refine.Pass
  Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.RunMixed

theorem len_le_flatten {α : Type} {L : List (List α)} {e : List α} (h : e ∈ L) : e.length ≤ L.flatten.length := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    simp only [List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem encodeNat_pos (x : Nat) : 1 ≤ (Blob.encodeNat x).length := by
  unfold Blob.encodeNat
  split
  · simp
  · split <;> simp

theorem encs_len (ds : List (List UInt8)) : ds.length ≤ (Decode.VecVecU8.encs ds).flatten.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [Decode.VecVecU8.encs, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at *
    have := encodeNat_pos d.length
    omega

theorem encs_item (ds : List (List UInt8)) (d : List UInt8) (hd : d ∈ ds) :
    d.length ≤ (Decode.VecVecU8.encs ds).flatten.length := by
  have h1 : Blob.encodeNat d.length ++ d ∈ Decode.VecVecU8.encs ds := by
    unfold Decode.VecVecU8.encs; exact List.mem_map.mpr ⟨d, hd, rfl⟩
  have := len_le_flatten h1
  simp only [List.length_append] at this
  omega

theorem segsOf_fixed' {x : Spec.Instr} (hm : MFixed x) : segsOf x = none := by
  cases x <;> simp only [MFixed] at hm <;> rfl

theorem mixed_kinds {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (C : Spec.Consts)
    (is : List Spec.Instr) (hwf : ∀ x ∈ is, x.WF C)
    (hk : ∀ x ∈ is, MFixed x ∨ ∃ ds, x = .exportSegs ds)
    (hlen : (is.map Spec.Instr.encode).flatten.length < 16777216) :
    ∃ (Rs : Nat → List UInt8 → Prop) (ts : Nat → Nat), ∀ j, j < is.length →
      FixedKind p P (encOut is j) (Rs j) (ts j) ∧
      (segsOf (is.getD j .panic) = none ∨ ∃ ds, segsOf (is.getD j .panic) = some ds ∧
        (∀ bs, bs.take 8 = Num.encodeLE 8 9223372036854775827 → (bs.drop 8).take 8 = Num.encodeLE 8 ds.length →
          Rs j bs) ∧ 24 * ds.length < 1073741760 ∧ ∀ d ∈ ds, d.length < 1073741760) := by
  have key : ∀ j, ∃ (R : List UInt8 → Prop) (t : Nat), j < is.length →
      FixedKind p P (encOut is j) R t ∧
      (segsOf (is.getD j .panic) = none ∨ ∃ ds, segsOf (is.getD j .panic) = some ds ∧
        (∀ bs, bs.take 8 = Num.encodeLE 8 9223372036854775827 → (bs.drop 8).take 8 = Num.encodeLE 8 ds.length →
          R bs) ∧ 24 * ds.length < 1073741760 ∧ ∀ d ∈ ds, d.length < 1073741760) := by
    intro j
    by_cases hj : j < is.length
    rotate_left
    · exact ⟨fun _ => True, 0, fun h => absurd h hj⟩
    have hg : is.getD j .panic = is[j] := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hx : is.getD j .panic ∈ is := by rw [hg]; exact List.getElem_mem hj
    rcases hk _ hx with hm | ⟨ds, hds⟩
    · obtain ⟨R, t, hK⟩ := kind_of (p := p) (P := P) C (is.getD j .panic) hm (hwf _ hx)
      refine ⟨R, t, fun _ => ⟨?_, Or.inl (segsOf_fixed' hm)⟩⟩
      have e : encOut is j = (is.getD j .panic).encode := by unfold encOut outI; rw [segsOf_fixed' hm]
      rw [e]; exact hK
    · have hle : (is.getD j .panic).encode.length < 16777216 :=
        Nat.lt_of_le_of_lt (len_le_flatten (List.mem_map.mpr ⟨_, hx, rfl⟩)) hlen
      rw [hds, encode_exportSegs] at hle
      simp only [List.length_cons, List.length_append] at hle
      have h1 := encs_len ds
      refine ⟨fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = Codec.fixed 8 ds.length,
        20, fun _ => ⟨?_, Or.inr ⟨ds, by rw [hds]; rfl, fun bs h1 h2 => ⟨h1, h2⟩, by omega, fun d hd => ?_⟩⟩⟩
      · have e : encOut is j = (Spec.Instr.exported ds.length).encode := by unfold encOut outI; rw [hds]; rfl
        rw [e]
        exact FixedKind.of (by simp [Spec.Instr.encode])
          (fun F RD hL => Decode.Elems.exportedF F RD hL (Codec.fixed 8 ds.length) (by simp [Codec.fixed]))
          (Encode.Enc.exported (Codec.fixed 8 ds.length) (by simp [Codec.fixed]))
          (fun bs h => h.1) (by unfold DropOut.NoDrop; omega) (fun bs _ => Or.inl (by unfold PassIdx; omega))
          (by simp [Codec.fixed]) (by simp)
      · have := encs_item ds d hd; omega
  exact ⟨fun j => Classical.choose (key j), fun j => Classical.choose (Classical.choose_spec (key j)),
    fun j hj => Classical.choose_spec (Classical.choose_spec (key j)) hj⟩

end Services.Bootstrap.Refine.MixedKinds
