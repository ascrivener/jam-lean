import Services.Bootstrap.Encode.ArmsH

/-!
# The fixed-width arms with growth (`Variants`, `Fixed`): `EncOkMH … 136`

`Variants.eject`, `solicit`, `forget`, `upgrade`, `lookup`, `random_storage_refine` and `Fixed.zombify`,
`exported` as `EncOkMH` elements (the same encodings and slot representations, no heap octets), each
following `ArmsH.transferH`: every piece (`pieceTagH`, `pieceFieldH`, `pieceDirectH`) either appends or
reaches a failed `realloc` (`ExhaustsW`).
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000


/-- **`Eject` (tag 4), with growth** (`Variants.eject` as `EncOkMH`). -/
theorem ejectH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (d h : List UInt8) (hd : d.length = 4) (hh : h.length = 32) :
    EncOkMH env K pb p P 136 (4 :: (d ++ h))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775811 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 4 = d) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (4 :: (d ++ h) : List UInt8).length = 37 := by simp [hd, hh]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 4) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 4 = d := by rw [← slot_take μ S 40 4 (by decide)]; exact rep.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 4 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 4 = 18369 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18369 4 746 18392 (by unfold TagCase; decide) jte_372
      bs_18392 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 18392 748 18413 40 4 (by unfold FieldCase; decide)
      jte_373 bs_18413 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 18413 916 20329 8 32 (by unfold DirectCase; decide)
      jte_457 bs_20329 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1] at st4
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans run4)))
    (st4.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Solicit` (tag 6), with growth** (`Variants.solicit` as `EncOkMH`). -/
theorem solicitH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h z : List UInt8) (hh : h.length = 32) (hz : z.length = 8) :
    EncOkMH env K pb p P 136 (6 :: (h ++ z))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775813 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (6 :: (h ++ z) : List UInt8).length = 41 := by simp [hh, hz]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 6) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = z := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 6 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 6 = 19474 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 19474 6 850 19500 (by unfold TagCase; decide) jte_424
      bs_19500 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 19500 852 19515 8 32 (by unfold DirectCase; decide)
      jte_425 bs_19515 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 19515 916 20329 40 8 (by unfold FieldCase; decide)
      jte_457 bs_20329 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1] at st4
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans run4)))
    (st4.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Forget` (tag 7), with growth** (`Variants.forget` as `EncOkMH`). -/
theorem forgetH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h z : List UInt8) (hh : h.length = 32) (hz : z.length = 8) :
    EncOkMH env K pb p P 136 (7 :: (h ++ z))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775814 ∧ (bs.drop 8).take 32 = h ∧ (bs.drop 40).take 8 = z) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (7 :: (h ++ z) : List UInt8).length = 41 := by simp [hh, hz]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 7) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = z := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 7 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 7 = 18919 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18919 7 850 19500 (by unfold TagCase; decide) jte_424
      bs_19500 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 19500 852 19515 8 32 (by unfold DirectCase; decide)
      jte_425 bs_19515 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 19515 916 20329 40 8 (by unfold FieldCase; decide)
      jte_457 bs_20329 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1] at st4
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans run4)))
    (st4.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Upgrade` (tag 1), with growth** (`Variants.upgrade` as `EncOkMH`). -/
theorem upgradeH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (c g m : List UInt8) (hc : c.length = 32) (hg : g.length = 8) (hm : m.length = 8) :
    EncOkMH env K pb p P 136 (1 :: (c ++ g ++ m))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775808 ∧ (bs.drop 8).take 32 = c ∧ (bs.drop 40).take 8 = g ∧ (bs.drop 48).take 8 = m) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (1 :: (c ++ g ++ m) : List UInt8).length = 49 := by simp [hc, hg, hm]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 1) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = c := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 40) 8 = g := by rw [← slot_take μ S 40 8 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 48) 8 = m := by rw [← slot_take μ S 48 8 (by decide)]; exact rep.2.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 1 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 1 = 18925 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18925 1 798 18948 (by unfold TagCase; decide) jte_398
      bs_18948 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 18948 800 18963 8 32 (by unfold DirectCase; decide)
      jte_399 bs_18963 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 18963 802 18984 40 8 (by unfold FieldCase; decide)
      jte_400 bs_18984 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω4 μ4 Fr (by decide) st4 S 18984 916 20329 48 8 (by unfold FieldCase; decide)
      jte_457 bs_20329 b45 b46 L.hS' L.slot (by simp; omega) with ⟨ω5, μ5, run5, st5, b55, b56⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1, c2] at st5
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans run5))))
    (st5.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Lookup` (tag 8), with growth** (`Variants.lookup` as `EncOkMH`). -/
theorem lookupH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (s h : List UInt8) (b : Nat) (hs : s.length = 4) (hh : h.length = 32) :
    EncOkMH env K pb p P 136 (8 :: (s ++ h ++ [UInt8.ofNat b]))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775815 ∧ (bs.drop 8).take 4 = s ∧ (bs.drop 12).take 32 = h ∧ (bs.drop 44).take 1 = [UInt8.ofNat b]) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (8 :: (s ++ h ++ [UInt8.ofNat b]) : List UInt8).length = 38 := by simp [hs, hh]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 8) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 4 = s := by rw [← slot_take μ S 8 4 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 12) 32 = h := by rw [← slot_take μ S 12 32 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 44) 1 = [UInt8.ofNat b] := by rw [← slot_take μ S 44 1 (by decide)]; exact rep.2.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 8 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 8 = 19789 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 19789 8 876 19812 (by unfold TagCase; decide) jte_437
      bs_19812 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 19812 878 19833 8 4 (by unfold FieldCase; decide)
      jte_438 bs_19833 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 19833 880 19848 12 32 (by unfold DirectCase; decide)
      jte_439 bs_19848 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω4 μ4 Fr (by decide) st4 S 19848 916 20329 44 1 (by unfold FieldCase; decide)
      jte_457 bs_20329 b45 b46 L.hS' L.slot (by simp; omega) with ⟨ω5, μ5, run5, st5, b55, b56⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1, c2] at st5
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans run5))))
    (st5.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`RandomStorageRefine` (tag 21), with growth** (`Variants.random_storage_refine` as `EncOkMH`). -/
theorem random_storage_refineH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (g : List UInt8) (n : UInt8) (hg : g.length = 8) :
    EncOkMH env K pb p P 136 (21 :: (g ++ [n]))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775828 ∧ (bs.drop 8).take 8 = g ∧ (bs.drop 16).take 1 = [n]) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (21 :: (g ++ [n]) : List UInt8).length = 10 := by simp [hg]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 21) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 8 = g := by rw [← slot_take μ S 8 8 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 16) 1 = [n] := by rw [← slot_take μ S 16 1 (by decide)]; exact rep.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 21 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 21 = 19256 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 19256 21 830 19279 (by unfold TagCase; decide) jte_414
      bs_19279 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 19279 832 19300 8 8 (by unfold FieldCase; decide)
      jte_415 bs_19300 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 19300 916 20329 16 1 (by unfold FieldCase; decide)
      jte_457 bs_20329 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1] at st4
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans run4)))
    (st4.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Zombify` (tag 3), with growth** (`Fixed.zombify` as `EncOkMH`). -/
theorem zombifyH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (e : List UInt8) (he : e.length = 4) :
    EncOkMH env K pb p P 136 (3 :: e)
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775810 ∧ (bs.drop 8).take 4 = e) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (3 :: e : List UInt8).length = 5 := by simp [he]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 3) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 4 = e := by rw [← slot_take μ S 8 4 (by decide)]; exact rep.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 3 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 3 = 18890 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18890 3 792 18913 (by unfold TagCase; decide) jte_395
      bs_18913 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 18913 916 20329 8 4 (by unfold FieldCase; decide)
      jte_457 bs_20329 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0] at st3
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans run3))
    (st3.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Exported` (tag 20), with growth** (`Fixed.exported` as `EncOkMH`). -/
theorem exportedH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (e : List UInt8) (he : e.length = 8) :
    EncOkMH env K pb p P 136 (20 :: e)
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775827 ∧ (bs.drop 8).take 8 = e) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (20 :: e : List UInt8).length = 9 := by simp [he]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 20) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 8 = e := by rw [← slot_take μ S 8 8 (by decide)]; exact rep.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 20 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 20 = 19088 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 19088 20 816 19111 (by unfold TagCase; decide) jte_407
      bs_19111 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 19111 916 20329 8 8 (by unfold FieldCase; decide)
      jte_457 bs_20329 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0] at st3
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans run3))
    (st3.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

end Services.Bootstrap.Encode.GrowH
