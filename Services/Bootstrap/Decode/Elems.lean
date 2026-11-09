import Services.Bootstrap.Decode.Loop
import Services.Bootstrap.Decode.Fixed
import Services.Bootstrap.Decode.Hash
import Services.Bootstrap.Decode.HashU64
import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.Decode.Upgrade
import Services.Bootstrap.Decode.Lookup
import Services.Bootstrap.Decode.Transfer
import Services.Bootstrap.Decode.RandomStorageRefine

/-!
# `ElemOk` for the decoded variants

Each variant's decode theorem, instantiated in the decode loop's frame (A = 4278057632, O = 4278057752,
the reader at 4278058648, returning to 723), gives an `ElemOk` for that variant's encodings, with the
property of its slot value that the theorem proves.
-/

namespace Services.Bootstrap.Decode.Elems

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Loop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The decode loop's frame at base F as `Tag.Frame` sees it: returning to 723. -/
theorem loopFrame {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (ω : Regs)
    (μ : Memory) (v5 v6 : Nat)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat (F + 120))
    (s0 : μ.readN (F + 48) 8 = Num.encodeLE 8 18) (s5 : μ.readN (F + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 32) 8 = Num.encodeLE 8 v6) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616)
    (ws : ∀ a, 4278050816 ≤ a → a < F + 584 → μ.writable a = true) :
    Tag.Frame P F (F + 120) 18 723 v5 v6 ω μ := by
  obtain ⟨l1, l2, l3, l4⟩ := hL
  exact ⟨by omega, by omega, Or.inr (by omega), h1, h5, hv5, hv6, s0, s5, s6, by decide,
    by simp only [Nat.reduceDiv, Nat.reduceSub, jte_8], bs_723, fun a h1 h2 => ws a (by omega) (by omega),
    fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega))⟩

/-- **`Checkpoint`, `Panic`, `Benchmark`** (tags 15, 16, 23): the one-octet encoding [t] decodes to a
    slot whose first word is the discriminant 2^63 + t − 1. -/
theorem unitF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) :
    ElemOkF p P F RD [UInt8.ofNat t] (fun bs => bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL _ _ _ _ _ _ s0 s5 s6 hv5 hv6 tab rt ws wr
  obtain ⟨ω', run, e0, e1, e5, e6⟩ := Tag.unit_variant (p := p) (P := P) (R := R) x ω μ F (F + 120) 18
    723 v5 v6 t (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) ht h7 (by simpa using tag) tab rt
  have hw8 : (9223372036854775807 + t) < 18446744073709551616 := by omega
  refine ⟨ω', _, run.mono (by omega), e1, e5, e6, ?_, ?_, ⟨9223372036854775807 + t, hw8, ?_, by omega⟩, ?_,
    fun a h0 _ _ h3 => ?_, fun a => by rw [Memory.readable_writeN], fun a => by rw [Memory.writable_writeN]⟩
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]; simpa using rP
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]; simpa using rL
  · exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32] <;> omega)
  · show List.take 8 _ = _
    rw [readN_take _ _ 232 8 (by omega)]
    exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32] <;> omega)
  · exact Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)

/-- The first word and a later stretch of a 232-octet slot, from reads at O. -/
theorem slot_parts (μ : Memory) (O i m : Nat) (him : i + m ≤ 232) :
    (μ.readN O 232).take 8 = μ.readN O 8 ∧ ((μ.readN O 232).drop i).take m = μ.readN (O + i) m :=
  ⟨readN_take _ _ 232 8 (by decide), (readN_sub μ O 232 i m _ rfl him).symm⟩

/-- **`Zombify`** (tag 3): the encoding 3 :: e, with e the 4 octets of `ejector`, decodes to a slot
    holding the discriminant 2^63 + 2 and then e. -/
theorem zombifyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (e : List UInt8) (he : e.length = 4) :
    ElemOkF p P F RD (3 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775810 ∧ (bs.drop 8).take 4 = e) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, he, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Fixed.zombify (p := p) (P := P) (R := R)
    x ω μ F (F + 120) 18 723 v5 v6 RD ptr len (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775810, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 4 (by omega)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Exported`** (tag 20): the encoding 20 :: e, with e the 8 octets of the segment index, decodes to a
    slot holding the discriminant 2^63 + 19 and then e. -/
theorem exportedF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (e : List UInt8) (he : e.length = 8) :
    ElemOkF p P F RD (20 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = e) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, he, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Fixed.exported (p := p) (P := P) (R := R)
    x ω μ F (F + 120) 18 723 v5 v6 RD ptr len (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775827, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 8 (by omega)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Yield`** (tag 14): the encoding 14 :: h, with h the 32 octets of the hash, decodes to a slot
    holding the discriminant 2^63 + 13 and then h. -/
theorem yieldF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (h : List UInt8) (hh : h.length = 32) :
    ElemOkF p P F RD (14 :: h) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775821 ∧ (bs.drop 8).take 32 = h) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, hh, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Hash.yield (p := p) (P := P) (R := R)
    x ω μ F (F + 120) 18 723 v5 v6 RD ptr len (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775821, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 32 (by omega)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Solicit`** (tag 6): the encoding 6 :: h ++ z, with h the 32 octets of the hash and z the 8 of the
    length, decodes to a slot holding the discriminant 2^63 + 5, then h, then z. -/
theorem solicitF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOkF p P F RD (6 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775813 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hz, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := HashU64.solicit (p := p) (P := P)
    (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775813, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 32 (by omega)
  obtain ⟨-, d40⟩ := slot_parts μ' (F + 120) 40 8 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 40 0 32 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]
  · rw [readN_sub μ ptr 40 32 8 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]

/-- **`Forget`** (tag 7): as `solicit`, with the discriminant 2^63 + 6. -/
theorem forgetF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOkF p P F RD (7 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775814 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hz, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := HashU64.forget (p := p) (P := P)
    (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775814, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 32 (by omega)
  obtain ⟨-, d40⟩ := slot_parts μ' (F + 120) 40 8 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 40 0 32 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]
  · rw [readN_sub μ ptr 40 32 8 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]

/-- **`Eject`** (tag 4): the encoding 4 :: d ++ h, with d the 4 octets of the service and h the 32 of
    the hash, decodes to a slot holding the discriminant 2^63 + 3, then h, then d. -/
theorem ejectF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (d h : List UInt8) (hd : d.length = 4)
    (hh : h.length = 32) :
    ElemOkF p P F RD (4 :: (d ++ h)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775811 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 4 = d) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hd, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := U32Hash.eject (p := p) (P := P)
    (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775811, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 32 (by omega)
  obtain ⟨-, d40⟩ := slot_parts μ' (F + 120) 40 4 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [readN_sub μ ptr 36 4 32 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, hh]
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 36 0 4 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, hh]

/-- **`Upgrade`** (tag 1): the encoding 1 :: c ++ g ++ m, with c the 32 octets of the code hash and
    g, m the 8 of each gas limit, decodes to a slot holding the discriminant 2^63, then c, g, m. -/
theorem upgradeF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (c g m : List UInt8) (hc : c.length = 32)
    (hg : g.length = 8) (hm : m.length = 8) :
    ElemOkF p P F RD (1 :: (c ++ g ++ m)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775808 ∧
      (bs.drop 8).take 32 = c ∧ (bs.drop 40).take 8 = g ∧ (bs.drop 48).take 8 = m) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hc, hg, hm, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eO48, eR0, eR8, efr, erd, ewr⟩ := Upgrade.upgrade (p := p)
    (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775808, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 32 (by omega)
  obtain ⟨-, d40⟩ := slot_parts μ' (F + 120) 40 8 (by omega)
  obtain ⟨-, d48⟩ := slot_parts μ' (F + 120) 48 8 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_), d48.trans (eO48.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 48 0 32 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]
  · rw [readN_sub μ ptr 48 32 8 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]
  · rw [readN_sub μ ptr 48 40 8 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]

/-- **`Lookup`** (tag 8): the encoding 8 :: s ++ h ++ [b], with s the 4 octets of the service, h the 32
    of the hash and b ∈ {0, 1} the flag, decodes to a slot holding the discriminant 2^63 + 7, then s, h
    and b. -/
theorem lookupF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (s h : List UInt8) (b : Nat) (hs : s.length = 4)
    (hh : h.length = 32) (hb : b < 2) :
    ElemOkF p P F RD (8 :: (s ++ h ++ [UInt8.ofNat b])) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775815 ∧
      (bs.drop 8).take 4 = s ∧ (bs.drop 12).take 32 = h ∧ (bs.drop 44).take 1 = [UInt8.ofNat b]) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, List.length_nil, hs, hh, Nat.add_sub_cancel,
    List.headD_cons, List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have sb : μ.read (ptr + 36) = UInt8.ofNat b := by
    have := readN_sub μ ptr 37 36 1 _ pay (by omega)
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh,
      Memory.readN] at this
    simpa using this
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO12, eO44, eR0, eR8, efr, erd, ewr⟩ := Lookup.lookup (p := p)
    (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len b
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ hb sb rP rL (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775815, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 4 (by omega)
  obtain ⟨-, d12⟩ := slot_parts μ' (F + 120) 12 32 (by omega)
  obtain ⟨-, d44⟩ := slot_parts μ' (F + 120) 44 1 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d12.trans (eO12.trans ?_), d44.trans ?_⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 37 0 4 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh]
  · rw [readN_sub μ ptr 37 4 32 _ pay (by omega)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh]
  · simp [Memory.readN, eO44]

/-- **`Transfer`** (tag 2): the encoding 2 :: d ++ a ++ g ++ m, with d the 4 octets of the destination,
    a and g the 8 of the amount and the gas limit and m the 128 of the memo, decodes to a slot holding the
    discriminant 2^63 + 1, then m, a, g and d. -/
theorem transferF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (d a g m : List UInt8) (hd : d.length = 4)
    (ha : a.length = 8) (hg : g.length = 8) (hm : m.length = 128) :
    ElemOkF p P F RD (2 :: (d ++ a ++ g ++ m)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775809 ∧
      (bs.drop 8).take 128 = m ∧ (bs.drop 136).take 8 = a ∧ (bs.drop 144).take 8 = g ∧
      (bs.drop 152).take 4 = d) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hd, ha, hg, hm, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eM, eA, eG, eD, eR0, eR8, efr, erd, ewr⟩ := Transfer.transfer
    (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by omega) (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775809, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 128 (by omega)
  obtain ⟨-, d136⟩ := slot_parts μ' (F + 120) 136 8 (by omega)
  obtain ⟨-, d144⟩ := slot_parts μ' (F + 120) 144 8 (by omega)
  obtain ⟨-, d152⟩ := slot_parts μ' (F + 120) 152 4 (by omega)
  refine ⟨t8.trans eO, d8.trans (eM.trans ?_), d136.trans (eA.trans ?_), d144.trans (eG.trans ?_),
    d152.trans (eD.trans ?_)⟩
  · rw [readN_sub μ ptr 148 20 128 _ pay (by omega)]
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, ha, hg, hm]
  · rw [readN_sub μ ptr 148 4 8 _ pay (by omega)]
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, ha, hg, hm]
  · rw [readN_sub μ ptr 148 12 8 _ pay (by omega)]
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, ha, hg, hm]
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 148 0 4 _ pay (by omega)]
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, ha, hg, hm]

/-- **`RandomStorageRefine`** (tag 21): the encoding 21 :: g ++ [n], with g the 8 octets of the seed
    and n any octet, decodes to a slot holding the discriminant 2^63 + 20, then g, then n. -/
theorem random_storage_refineF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) (g : List UInt8) (n : UInt8)
    (hg : g.length = 8) :
    ElemOkF p P F RD (21 :: (g ++ [n])) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775828 ∧
      (bs.drop 8).take 8 = g ∧ (bs.drop 16).take 1 = [n]) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, List.length_nil, hg, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO16, eR0, eR8, efr, erd, ewr⟩ :=
    RandomStorageRefine.random_storage_refine (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6
      RD ptr len (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
      (by omega) h6 h7 tag tab rt (by omega) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
      (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775828, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 8 (by omega)
  obtain ⟨-, d16⟩ := slot_parts μ' (F + 120) 16 1 (by omega)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d16.trans ?_⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 9 0 8 _ pay (by omega)]
    simp [List.take_append, List.take_of_length_le, hg]
  · have hn := readN_sub μ ptr 9 8 1 _ pay (by omega)
    simp [List.drop_append, List.drop_of_length_le, hg, Memory.readN] at hn
    simp [Memory.readN, eO16, hn]

/-! ## In refine's frame -/

/-- `unitF` in refine's frame. -/
theorem unit {p : ByteArray} {P : Program} [HasCode p P] (t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) :
    ElemOk p P [UInt8.ofNat t] (fun bs => bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) :=
  unitF 4278057632 4278058648 lay_refine t ht

/-- `zombifyF` in refine's frame. -/
theorem zombify {p : ByteArray} {P : Program} [HasCode p P] (e : List UInt8) (he : e.length = 4) :
    ElemOk p P (3 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775810 ∧ (bs.drop 8).take 4 = e) :=
  zombifyF 4278057632 4278058648 lay_refine e he

/-- `exportedF` in refine's frame. -/
theorem exported {p : ByteArray} {P : Program} [HasCode p P] (e : List UInt8) (he : e.length = 8) :
    ElemOk p P (20 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = e) :=
  exportedF 4278057632 4278058648 lay_refine e he

/-- `yieldF` in refine's frame. -/
theorem yield {p : ByteArray} {P : Program} [HasCode p P] (h : List UInt8) (hh : h.length = 32) :
    ElemOk p P (14 :: h) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775821 ∧ (bs.drop 8).take 32 = h) :=
  yieldF 4278057632 4278058648 lay_refine h hh

/-- `solicitF` in refine's frame. -/
theorem solicit {p : ByteArray} {P : Program} [HasCode p P] (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOk p P (6 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775813 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) :=
  solicitF 4278057632 4278058648 lay_refine h z hh hz

/-- `forgetF` in refine's frame. -/
theorem forget {p : ByteArray} {P : Program} [HasCode p P] (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOk p P (7 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775814 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) :=
  forgetF 4278057632 4278058648 lay_refine h z hh hz

/-- `ejectF` in refine's frame. -/
theorem eject {p : ByteArray} {P : Program} [HasCode p P] (d h : List UInt8) (hd : d.length = 4)
    (hh : h.length = 32) :
    ElemOk p P (4 :: (d ++ h)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775811 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 4 = d) :=
  ejectF 4278057632 4278058648 lay_refine d h hd hh

/-- `upgradeF` in refine's frame. -/
theorem upgrade {p : ByteArray} {P : Program} [HasCode p P] (c g m : List UInt8) (hc : c.length = 32)
    (hg : g.length = 8) (hm : m.length = 8) :
    ElemOk p P (1 :: (c ++ g ++ m)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775808 ∧
      (bs.drop 8).take 32 = c ∧ (bs.drop 40).take 8 = g ∧ (bs.drop 48).take 8 = m) :=
  upgradeF 4278057632 4278058648 lay_refine c g m hc hg hm

/-- `lookupF` in refine's frame. -/
theorem lookup {p : ByteArray} {P : Program} [HasCode p P] (s h : List UInt8) (b : Nat) (hs : s.length = 4)
    (hh : h.length = 32) (hb : b < 2) :
    ElemOk p P (8 :: (s ++ h ++ [UInt8.ofNat b])) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775815 ∧
      (bs.drop 8).take 4 = s ∧ (bs.drop 12).take 32 = h ∧ (bs.drop 44).take 1 = [UInt8.ofNat b]) :=
  lookupF 4278057632 4278058648 lay_refine s h b hs hh hb

/-- `transferF` in refine's frame. -/
theorem transfer {p : ByteArray} {P : Program} [HasCode p P] (d a g m : List UInt8) (hd : d.length = 4)
    (ha : a.length = 8) (hg : g.length = 8) (hm : m.length = 128) :
    ElemOk p P (2 :: (d ++ a ++ g ++ m)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775809 ∧
      (bs.drop 8).take 128 = m ∧ (bs.drop 136).take 8 = a ∧ (bs.drop 144).take 8 = g ∧
      (bs.drop 152).take 4 = d) :=
  transferF 4278057632 4278058648 lay_refine d a g m hd ha hg hm

/-- `random_storage_refineF` in refine's frame. -/
theorem random_storage_refine {p : ByteArray} {P : Program} [HasCode p P] (g : List UInt8) (n : UInt8)
    (hg : g.length = 8) :
    ElemOk p P (21 :: (g ++ [n])) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775828 ∧
      (bs.drop 8).take 8 = g ∧ (bs.drop 16).take 1 = [n]) :=
  random_storage_refineF 4278057632 4278058648 lay_refine g n hg

end Services.Bootstrap.Decode.Elems
