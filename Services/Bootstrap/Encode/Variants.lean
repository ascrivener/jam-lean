import Services.Bootstrap.Encode.Fixed

/-!
# `Instruction::encode_to`: the variants of fixed width

Each variant's arm appends its tag octet and then its fields, each by a call of
`Vec<u8>::extend_from_slice` (`Fixed.pieceTag`, `pieceField`, `pieceDirect`), and leaves through the
shared tail at 20329. The value's layout is the one `Instruction::decode` writes (`Decode.Elems`), so each
`EncOk` here takes the decode side's `Rep` for the variant.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Eject` (tag 4)**: a value holding the discriminant 2^63 + 3, then h, the 32 octets of the hash, at
    S + 8 and d, the 4 octets of the service, at S + 40, encodes to 4 :: d ++ h. -/
theorem eject {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (d h : List UInt8) (hd : d.length = 4) (hh : h.length = 32) :
    EncOk p P (4 :: (d ++ h))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775811 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 4 = d) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 4) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 4 = d := by rw [← slot_take μ S 40 4 (by decide)]; exact rep.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 4 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 4 = 18369 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 18369 4 746 18392
    (by unfold TagCase; omega) jte_372 bs_18392 a10 a11 (by simp [hd, hh])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceField (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 18392 748 18413 40 4
    (by unfold FieldCase; omega) jte_373 bs_18413 b25 b26 (by simp [hd, hh])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceDirect (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 18413 916 20329 8 32
    (by unfold DirectCase; omega) jte_457 bs_20329 b35 b36 (by simp [hd, hh])
  rw [c0, c1] at st4
  exact close L 20329 _ (by decide) (by simp [hd, hh]) (run1.trans (run2.trans (run3.trans (run4))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st4)

/-- **`Solicit` (tag 6)**: a value holding the discriminant 2^63 + 5, then h, the 32 octets of the hash,
    and z, the 8 octets of the length, encodes to 6 :: h ++ z. -/
theorem solicit {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (h z : List UInt8) (hh : h.length = 32) (hz : z.length = 8) :
    EncOk p P (6 :: (h ++ z))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775813 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 6) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = z := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 6 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 6 = 19474 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 19474 6 850 19500
    (by unfold TagCase; omega) jte_424 bs_19500 a10 a11 (by simp [hh, hz])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceDirect (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 19500 852 19515 8 32
    (by unfold DirectCase; omega) jte_425 bs_19515 b25 b26 (by simp [hh, hz])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceField (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 19515 916 20329 40 8
    (by unfold FieldCase; omega) jte_457 bs_20329 b35 b36 (by simp [hh, hz])
  rw [c0, c1] at st4
  exact close L 20329 _ (by decide) (by simp [hh, hz]) (run1.trans (run2.trans (run3.trans (run4))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st4)

/-- **`Forget` (tag 7)**: as `solicit`, with the discriminant 2^63 + 6. -/
theorem forget {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (h z : List UInt8) (hh : h.length = 32) (hz : z.length = 8) :
    EncOk p P (7 :: (h ++ z))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775814 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 7) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = z := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 7 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 7 = 18919 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 18919 7 850 19500
    (by unfold TagCase; omega) jte_424 bs_19500 a10 a11 (by simp [hh, hz])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceDirect (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 19500 852 19515 8 32
    (by unfold DirectCase; omega) jte_425 bs_19515 b25 b26 (by simp [hh, hz])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceField (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 19515 916 20329 40 8
    (by unfold FieldCase; omega) jte_457 bs_20329 b35 b36 (by simp [hh, hz])
  rw [c0, c1] at st4
  exact close L 20329 _ (by decide) (by simp [hh, hz]) (run1.trans (run2.trans (run3.trans (run4))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st4)

/-- **`Upgrade` (tag 1)**: a value holding the discriminant 2^63, then c, the 32 octets of the code hash,
    and g and m, 8 octets each, encodes to 1 :: c ++ g ++ m. -/
theorem upgrade {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (c g m : List UInt8) (hc : c.length = 32) (hg : g.length = 8) (hm : m.length = 8) :
    EncOk p P (1 :: (c ++ g ++ m))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775808 ∧ (bs.drop 8).take 32 = c ∧ (bs.drop 40).take 8 = g ∧ (bs.drop 48).take 8 = m) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 1) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = c := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = g := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 48) 8 = m := by rw [← slot_take μ S 48 8 (by decide)]; exact rep.2.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 1 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 1 = 18925 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 18925 1 798 18948
    (by unfold TagCase; omega) jte_398 bs_18948 a10 a11 (by simp [hc, hg, hm])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceDirect (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 18948 800 18963 8 32
    (by unfold DirectCase; omega) jte_399 bs_18963 b25 b26 (by simp [hc, hg, hm])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceField (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 18963 802 18984 40 8
    (by unfold FieldCase; omega) jte_400 bs_18984 b35 b36 (by simp [hc, hg, hm])
  obtain ⟨ω5, μ5, run5, st5, b55, b56⟩ := pieceField (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 18984 916 20329 48 8
    (by unfold FieldCase; omega) jte_457 bs_20329 b45 b46 (by simp [hc, hg, hm])
  rw [c0, c1, c2] at st5
  exact close L 20329 _ (by decide) (by simp [hc, hg, hm]) (run1.trans (run2.trans (run3.trans (run4.trans (run5)))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st5)

/-- **`Lookup` (tag 8)**: a value holding the discriminant 2^63 + 7, then s, the 4 octets of the service,
    h, the 32 of the hash, and the octet b, encodes to 8 :: s ++ h ++ [b]. -/
theorem lookup {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (s h : List UInt8) (b : Nat) (hs : s.length = 4) (hh : h.length = 32) :
    EncOk p P (8 :: (s ++ h ++ [UInt8.ofNat b]))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775815 ∧ (bs.drop 8).take 4 = s ∧ (bs.drop 12).take 32 = h ∧ (bs.drop 44).take 1 = [UInt8.ofNat b]) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 8) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 4 = s := by rw [← slot_take μ S 8 4 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 12) 32 = h := by rw [← slot_take μ S 12 32 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 44) 1 = [UInt8.ofNat b] := by rw [← slot_take μ S 44 1 (by decide)]; exact rep.2.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 8 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 8 = 19789 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 19789 8 876 19812
    (by unfold TagCase; omega) jte_437 bs_19812 a10 a11 (by simp [hs, hh])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceField (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 19812 878 19833 8 4
    (by unfold FieldCase; omega) jte_438 bs_19833 b25 b26 (by simp [hs, hh])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceDirect (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 19833 880 19848 12 32
    (by unfold DirectCase; omega) jte_439 bs_19848 b35 b36 (by simp [hs, hh])
  obtain ⟨ω5, μ5, run5, st5, b55, b56⟩ := pieceField (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 19848 916 20329 44 1
    (by unfold FieldCase; omega) jte_457 bs_20329 b45 b46 (by simp [hs, hh])
  rw [c0, c1, c2] at st5
  exact close L 20329 _ (by decide) (by simp [hs, hh]) (run1.trans (run2.trans (run3.trans (run4.trans (run5)))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st5)

/-- **`Transfer` (tag 2)**: a value holding the discriminant 2^63 + 1, then m, the 128 octets of the memo,
    at S + 8, a and g, 8 octets each, at S + 136 and S + 144, and d, the 4 octets of the destination, at
    S + 152, encodes to 2 :: d ++ a ++ g ++ m. -/
theorem transfer {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (d a g m : List UInt8) (hd : d.length = 4) (ha : a.length = 8) (hg : g.length = 8) (hm : m.length = 128) :
    EncOk p P (2 :: (d ++ a ++ g ++ m))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775809 ∧ (bs.drop 8).take 128 = m ∧ (bs.drop 136).take 8 = a ∧ (bs.drop 144).take 8 = g ∧ (bs.drop 152).take 4 = d) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 2) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 128 = m := by rw [← slot_take μ S 8 128 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 136) 8 = a := by rw [← slot_take μ S 136 8 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 144) 8 = g := by rw [← slot_take μ S 144 8 (by decide)]; exact rep.2.2.2.1
  have c3 : μ.readN (S + 152) 4 = d := by rw [← slot_take μ S 152 4 (by decide)]; exact rep.2.2.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 2 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 2 = 18778 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 18778 2 780 18801
    (by unfold TagCase; omega) jte_389 bs_18801 a10 a11 (by simp [hd, ha, hg, hm])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceField (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 18801 782 18823 152 4
    (by unfold FieldCase; omega) jte_390 bs_18823 b25 b26 (by simp [hd, ha, hg, hm])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceField (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 18823 784 18845 136 8
    (by unfold FieldCase; omega) jte_391 bs_18845 b35 b36 (by simp [hd, ha, hg, hm])
  obtain ⟨ω5, μ5, run5, st5, b55, b56⟩ := pieceField (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 18845 786 18867 144 8
    (by unfold FieldCase; omega) jte_392 bs_18867 b45 b46 (by simp [hd, ha, hg, hm])
  obtain ⟨ω6, μ6, run6, st6, b65, b66⟩ := pieceDirect (p := p) (P := P) (R := R) x ω5 μ5 μ L st5 18867 916 20329 8 128
    (by unfold DirectCase; omega) jte_457 bs_20329 b55 b56 (by simp [hd, ha, hg, hm])
  rw [c0, c1, c2, c3] at st6
  exact close L 20329 _ (by decide) (by simp [hd, ha, hg, hm]) (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6))))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st6)

/-- **`RandomStorageRefine` (tag 21)**: a value holding the discriminant 2^63 + 20, then g, the 8 octets of
    the seed, and the octet n, encodes to 21 :: g ++ [n]. -/
theorem random_storage_refine {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (g : List UInt8) (n : UInt8) (hg : g.length = 8) :
    EncOk p P (21 :: (g ++ [n]))
      (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775828 ∧ (bs.drop 8).take 8 = g ∧ (bs.drop 16).take 1 = [n]) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 21) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 8 = g := by rw [← slot_take μ S 8 8 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 16) 1 = [n] := by rw [← slot_take μ S 16 1 (by decide)]; exact rep.2.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 21 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 21 = 19256 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b25, b26⟩ := pieceTag (p := p) (P := P) (R := R) x ω1 μ1 μ L st1 19256 21 830 19279
    (by unfold TagCase; omega) jte_414 bs_19279 a10 a11 (by simp [hg])
  obtain ⟨ω3, μ3, run3, st3, b35, b36⟩ := pieceField (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 19279 832 19300 8 8
    (by unfold FieldCase; omega) jte_415 bs_19300 b25 b26 (by simp [hg])
  obtain ⟨ω4, μ4, run4, st4, b45, b46⟩ := pieceField (p := p) (P := P) (R := R) x ω3 μ3 μ L st3 19300 916 20329 16 1
    (by unfold FieldCase; omega) jte_457 bs_20329 b35 b36 (by simp [hg])
  rw [c0, c1] at st4
  exact close L 20329 _ (by decide) (by simp [hg]) (run1.trans (run2.trans (run3.trans (run4))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st4)

end Services.Bootstrap.Encode.Enc
