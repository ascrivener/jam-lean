import Services.Bootstrap.Decode.Loop
import Services.Bootstrap.Decode.Fixed
import Services.Bootstrap.Decode.Hash
import Services.Bootstrap.Decode.HashU64
import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.Decode.Upgrade
import Services.Bootstrap.Decode.Lookup

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

/-- The decode loop's frame as `Tag.Frame` sees it: returning to 723. -/
theorem loopFrame {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (v5 v6 : Nat)
    (h1 : ω[1] = UInt64.ofNat 4278057632) (h5 : ω[5] = UInt64.ofNat 4278057752)
    (s0 : μ.readN 4278057680 8 = Num.encodeLE 8 18) (s5 : μ.readN 4278057672 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN 4278057664 8 = Num.encodeLE 8 v6) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616)
    (ws : ∀ a, 4278057448 ≤ a → a < 4278058216 → μ.writable a = true) :
    Tag.Frame P 4278057632 4278057752 18 723 v5 v6 ω μ :=
  { hA := by decide, hO := by decide, hOA := by decide, h1 := h1, h5 := h5, hv5 := hv5, hv6 := hv6,
    s0 := s0, s5 := s5, s6 := s6, hret := by decide,
    hjt := by simp only [Nat.reduceDiv, Nat.reduceSub, jte_8], hbt := bs_723,
    hw := fun a h1 h2 => ws a (by omega) (by omega),
    hr := fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega)) }

/-- **`Checkpoint`, `Panic`, `Benchmark`** (tags 15, 16, 23): the one-octet encoding [t] decodes to a
    slot whose first word is the discriminant 2^63 + t − 1. -/
theorem unit {p : ByteArray} {P : Program} [HasCode p P] (t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) :
    ElemOk p P [UInt8.ofNat t] (fun bs => bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL _ _ _ _ _ _ s0 s5 s6 hv5 hv6 tab rt ws wr
  obtain ⟨ω', run, e0, e1, e5, e6⟩ := Tag.unit_variant (p := p) (P := P) (R := R) x ω μ 4278057632 4278057752 18
    723 v5 v6 t (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) ht h7 (by simpa using tag) tab rt
  have hw8 : (9223372036854775807 + t) < 18446744073709551616 := by omega
  refine ⟨ω', _, run.mono (by omega), e1, e5, e6, ?_, ?_, ⟨9223372036854775807 + t, hw8, ?_, by omega⟩, ?_,
    fun a h0 _ _ h3 => ?_, fun a => by rw [Memory.readable_writeN], fun a => by rw [Memory.writable_writeN]⟩
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]; simpa using rP
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [two32]) (by simp [two32])]; simpa using rL
  · exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
  · show List.take 8 _ = _
    rw [readN_take _ _ 232 8 (by decide)]
    exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32])
  · exact Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega)

/-- The first word and a later stretch of a 232-octet slot, from reads at O. -/
theorem slot_parts (μ : Memory) (O i m : Nat) (him : i + m ≤ 232) :
    (μ.readN O 232).take 8 = μ.readN O 8 ∧ ((μ.readN O 232).drop i).take m = μ.readN (O + i) m :=
  ⟨readN_take _ _ 232 8 (by decide), (readN_sub μ O 232 i m _ rfl him).symm⟩

/-- **`Zombify`** (tag 3): the encoding 3 :: e, with e the 4 octets of `ejector`, decodes to a slot
    holding the discriminant 2^63 + 2 and then e. -/
theorem zombify {p : ByteArray} {P : Program} [HasCode p P] (e : List UInt8) (he : e.length = 4) :
    ElemOk p P (3 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775810 ∧ (bs.drop 8).take 4 = e) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, he, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Fixed.zombify (p := p) (P := P) (R := R)
    x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775810, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 4 (by decide)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Exported`** (tag 20): the encoding 20 :: e, with e the 8 octets of the segment index, decodes to a
    slot holding the discriminant 2^63 + 19 and then e. -/
theorem exported {p : ByteArray} {P : Program} [HasCode p P] (e : List UInt8) (he : e.length = 8) :
    ElemOk p P (20 :: e) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = e) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, he, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Fixed.exported (p := p) (P := P) (R := R)
    x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775827, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 8 (by decide)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Yield`** (tag 14): the encoding 14 :: h, with h the 32 octets of the hash, decodes to a slot
    holding the discriminant 2^63 + 13 and then h. -/
theorem yield {p : ByteArray} {P : Program} [HasCode p P] (h : List UInt8) (hh : h.length = 32) :
    ElemOk p P (14 :: h) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775821 ∧ (bs.drop 8).take 32 = h) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, hh, Nat.add_sub_cancel, List.headD_cons, List.tail_cons] at *
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := Hash.yield (p := p) (P := P) (R := R)
    x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775821, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 32 (by decide)
  exact ⟨t8.trans eO, d8.trans (eO8.trans pay)⟩

/-- **`Solicit`** (tag 6): the encoding 6 :: h ++ z, with h the 32 octets of the hash and z the 8 of the
    length, decodes to a slot holding the discriminant 2^63 + 5, then h, then z. -/
theorem solicit {p : ByteArray} {P : Program} [HasCode p P] (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOk p P (6 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775813 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hz, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := HashU64.solicit (p := p) (P := P)
    (R := R) x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len
    (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by omega) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775813, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 32 (by decide)
  obtain ⟨-, d40⟩ := slot_parts μ' 4278057752 40 8 (by decide)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 40 0 32 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]
  · rw [readN_sub μ ptr 40 32 8 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]

/-- **`Forget`** (tag 7): as `solicit`, with the discriminant 2^63 + 6. -/
theorem forget {p : ByteArray} {P : Program} [HasCode p P] (h z : List UInt8) (hh : h.length = 32)
    (hz : z.length = 8) :
    ElemOk p P (7 :: (h ++ z)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775814 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hz, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := HashU64.forget (p := p) (P := P)
    (R := R) x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len
    (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by omega) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775814, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 32 (by decide)
  obtain ⟨-, d40⟩ := slot_parts μ' 4278057752 40 8 (by decide)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 40 0 32 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]
  · rw [readN_sub μ ptr 40 32 8 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hh, hz]

/-- **`Eject`** (tag 4): the encoding 4 :: d ++ h, with d the 4 octets of the service and h the 32 of
    the hash, decodes to a slot holding the discriminant 2^63 + 3, then h, then d. -/
theorem eject {p : ByteArray} {P : Program} [HasCode p P] (d h : List UInt8) (hd : d.length = 4)
    (hh : h.length = 32) :
    ElemOk p P (4 :: (d ++ h)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775811 ∧
      (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 4 = d) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hh, hd, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eR0, eR8, efr, erd, ewr⟩ := U32Hash.eject (p := p) (P := P)
    (R := R) x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len
    (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by omega) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775811, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 32 (by decide)
  obtain ⟨-, d40⟩ := slot_parts μ' 4278057752 40 4 (by decide)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_)⟩
  · rw [readN_sub μ ptr 36 4 32 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, hh]
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 36 0 4 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hd, hh]

/-- **`Upgrade`** (tag 1): the encoding 1 :: c ++ g ++ m, with c the 32 octets of the code hash and
    g, m the 8 of each gas limit, decodes to a slot holding the discriminant 2^63, then c, g, m. -/
theorem upgrade {p : ByteArray} {P : Program} [HasCode p P] (c g m : List UInt8) (hc : c.length = 32)
    (hg : g.length = 8) (hm : m.length = 8) :
    ElemOk p P (1 :: (c ++ g ++ m)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775808 ∧
      (bs.drop 8).take 32 = c ∧ (bs.drop 40).take 8 = g ∧ (bs.drop 48).take 8 = m) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hc, hg, hm, Nat.add_sub_cancel, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO40, eO48, eR0, eR8, efr, erd, ewr⟩ := Upgrade.upgrade (p := p)
    (P := P) (R := R) x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len
    (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL (by decide) (by omega)
    (by decide) (by decide) (by omega) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775808, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 32 (by decide)
  obtain ⟨-, d40⟩ := slot_parts μ' 4278057752 40 8 (by decide)
  obtain ⟨-, d48⟩ := slot_parts μ' 4278057752 48 8 (by decide)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d40.trans (eO40.trans ?_), d48.trans (eO48.trans ?_)⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 48 0 32 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]
  · rw [readN_sub μ ptr 48 32 8 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]
  · rw [readN_sub μ ptr 48 40 8 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hc, hg, hm]

/-- **`Lookup`** (tag 8): the encoding 8 :: s ++ h ++ [b], with s the 4 octets of the service, h the 32
    of the hash and b ∈ {0, 1} the flag, decodes to a slot holding the discriminant 2^63 + 7, then s, h
    and b. -/
theorem lookup {p : ByteArray} {P : Program} [HasCode p P] (s h : List UInt8) (b : Nat) (hs : s.length = 4)
    (hh : h.length = 32) (hb : b < 2) :
    ElemOk p P (8 :: (s ++ h ++ [UInt8.ofNat b])) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775815 ∧
      (bs.drop 8).take 4 = s ∧ (bs.drop 12).take 32 = h ∧ (bs.drop 44).take 1 = [UInt8.ofNat b]) := by
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, List.length_nil, hs, hh, Nat.add_sub_cancel,
    List.headD_cons, List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have sb : μ.read (ptr + 36) = UInt8.ofNat b := by
    have := readN_sub μ ptr 37 36 1 _ pay (by decide)
    simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh,
      Memory.readN] at this
    simpa using this
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eO, eO8, eO12, eO44, eR0, eR8, efr, erd, ewr⟩ := Lookup.lookup (p := p)
    (P := P) (R := R) x ω μ 4278057632 4278057752 18 723 v5 v6 4278058648 ptr len b
    (loopFrame ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws)
    (by decide) h6 h7 tag tab rt (by decide) ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ hb sb rP rL (by decide) (by omega)
    (by decide) (by decide) (by omega) (by decide) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775815, by decide, eO, by decide⟩, ?_,
    fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' 4278057752 8 4 (by decide)
  obtain ⟨-, d12⟩ := slot_parts μ' 4278057752 12 32 (by decide)
  obtain ⟨-, d44⟩ := slot_parts μ' 4278057752 44 1 (by decide)
  refine ⟨t8.trans eO, d8.trans (eO8.trans ?_), d12.trans (eO12.trans ?_), d44.trans ?_⟩
  · rw [show ptr = ptr + 0 by rfl, readN_sub μ ptr 37 0 4 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh]
  · rw [readN_sub μ ptr 37 4 32 _ pay (by decide)]; simp [List.take_append, List.drop_append, List.take_of_length_le, List.drop_of_length_le, hs, hh]
  · simp [Memory.readN, eO44]

end Services.Bootstrap.Decode.Elems
