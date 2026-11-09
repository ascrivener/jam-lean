import Services.Bootstrap.Decode.Loop
import Services.Bootstrap.Decode.Fixed

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

end Services.Bootstrap.Decode.Elems
