import Services.Bootstrap.Decode.AssignGas
import Services.Bootstrap.Decode.RandomStorageOk
import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Refine.HashEmpty
import Services.Bootstrap.Refine.PkgT

/-!
# `AssignForGasCost` with q = [] and `RandomStorageAccumulate(Some [])` as elements of the decode loop

The two vector kinds whose hashes are read by the hash readers at 1764 / 907 (GP v0.8.0 B.7), with no hashes:

* `assign_gas_emptyF`: tag 24, the encoding 24 :: (c ++ ℰ(0) ++ g) (the core's two octets, the empty queue's length
  0, the assigner's four octets). The pieces of `AssignGas.assign_gas_elemF` (`ag1` … `ag5`, the reader, `decodeU32`)
  with `VecHash.vec_hash_empty` (n = 0) in place of `vec_hash`: nothing is allocated, the slot's queue is the empty
  `Vec` {cap 0, ptr 1, len 0}.
* `rsa_emptyF`: tag 22, the encoding [22, 0, 0] (`Ok`, ℰ(0)). The pieces of
  `RandomStorage.random_storage_ok_heap` (`q1`, `r_ok`, `r_call`, `r_fin`, `q2`) with `VecHash32.vec_hash32_empty`:
  the slot holds the discriminant 2^63 + 21 and the empty `Vec`.

Both are `Loop.ElemOkF` (no allocation, any host relation).
-/

namespace Services.Bootstrap.Refine.GapEmpty

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX JAM Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.Hash
  Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.Assign
  Services.Bootstrap.Decode.AssignGas

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The slot of `RandomStorageAccumulate(Some [])`: the discriminant 2^63 + 21 and the empty `Vec` {0, 1, 0}. -/
def RSAEmptyRep (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775829 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 1 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0

/-- **`RandomStorageAccumulate(Some [])`** (tag 22, encoded [22, 0, 0]; GP v0.8.0 B.7). -/
theorem rsa_emptyF {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [22, 0, 0] RSAEmptyRep := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  have hl : ([22, 0, 0] : List UInt8).length - 1 = 2 := rfl
  simp only [hl, List.headD_cons, List.tail_cons, List.length_cons, List.length_nil] at tag hlen hpb pay rpay ⊢
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  have he0 : Blob.encodeNat 0 = [0] := by decide
  have hw1 : (Blob.encodeNat 0).length = 1 := by decide
  have hok : μ.read ptr = 0 := by
    have := readN_sub μ ptr 2 0 1 _ pay (by omega); simpa [Memory.readN] using this
  have henc : μ.readN (ptr + 1) 1 = Blob.encodeNat 0 := by
    have := readN_sub μ ptr 2 1 1 _ pay (by omega); rw [he0]; simpa using this
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ F 22
    (by decide) (by omega) h1 h7 (by simpa using tag) tab (Fr.hr F (by omega) (by omega)) rt
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gsA, gfr, grd, gwr⟩ :=
    Decode.RandomStorage.q1 (p := p) (P := P) (R := R) x ω1 μ F (F + 120) RD ⟨by omega, by omega⟩ (e1.trans h1)
      (e5.trans h5) (e6.trans h6) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1676 35823 (F - 56) RD (F - 48) ptr len 1
      g0 g1 g7 g8 g9 (by decide) jte_837 bs_35823 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hlen' (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact rpay a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact rL)
  have htag : μ4.read (F - 56 + 8) = 0 := by
    rw [show F - 56 + 8 = F - 48 by omega, Decode.RandomStorage.read_of_readN1 kbuf, ← hok]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := Decode.RandomStorage.r_ok (p := p) (P := P) (R := R) x ω4 μ4 (F - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (ws _ (by omega) (by omega)))
  have pay4 : ∀ a, ptr ≤ a → a < ptr + 2 → μ4.read a = μ.read a := fun a h1 h2 =>
    (kfr a (by omega) (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω5 μ4 1678 35850 (F - 56) RD (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_838 bs_35850 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact wr a h1 h2) kR0 kR8 0 (by omega)
      (by rw [hw1]; omega)
      (fun a h1 h2 => by rw [hw1] at h2; rw [krd, grd]; exact rpay a (by omega) (by omega))
      (by rw [hw1, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hw1] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := Decode.RandomStorage.r_call (p := p) (P := P) (R := R) x ω6 μ6
    (F - 56) 0 (by omega) (by omega) (by rw [d1, m1, k1', g1]) d7 d8
  have b6 : ∀ a, a < 4294967296 → (a < F - 184 ∨ F ≤ a) → (a < RD ∨ RD + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [dwr, kwr, gwr]
  -- no hashes
  obtain ⟨ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    Decode.VecHash32.vec_hash32_empty (p := p) (P := P) (R := R) x ω7 μ6 (F - 208) (F - 56 + 8) RD 1680 35874
      18446744073709551614 RD ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1, show F - 208 + 152 = F - 56 by omega]) (by rw [o5, d5, m5])
      (by rw [o6, d6, m6, k6, g6]) o7 (by rw [o8, d6, m6, k6, g6]) o9 (by decide) (by omega) (by omega)
      (by decide) jte_839 bs_35874 (by omega) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr6]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr6]; exact ws a (by omega) (by omega))
  have hfA : ∀ a, F - 56 ≤ a → a < F + 56 → (a < F - 48 ∨ F - 24 ≤ a) → μ8.read a = μ3.read a :=
    fun a h1 h2 h3 => (vfr a (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    Decode.RandomStorage.r_fin (p := p) (P := P) (R := R) x ω8 μ8 (F - 56) F 0 1 0 1018 22018 (F + 120) RD
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [v1]; congr 1; omega) (by decide) (by decide)
      (by decide) (by omega) (by omega)
      vc (by rw [show F - 56 + 16 = F - 56 + 8 + 8 by omega]; exact vp)
      (by rw [show F - 56 + 24 = F - 56 + 8 + 16 by omega]; exact vl)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega))]; exact gsA)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)),
        show F - 56 + 48 = F - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)),
        show F - 56 + 40 = F - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)),
        show F - 56 + 32 = F - 24 by omega]; exact gs6)
      (by decide) jte_508 bs_22018
      (fun a h1 h2 => Memory.readable_of_writable (by rw [vwr, wr6]; exact ws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [vwr, wr6]; exact ws a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → F + 24 ≤ a → (a < RD ∨ RD + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h1 h2 => (cfr a h0 (by omega)).trans ((vfr a h0 (by omega) (by omega)).trans (b6 a h0 (by omega) h2))
  obtain ⟨ω10, μ10, run10, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    Decode.RandomStorage.q2 (p := p) (P := P) (R := R) x ω9 μ9 F (F + 120) 0 1 0 18 723 v5 v6 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) (by rw [c1]; congr 1; omega) c5 (by decide) (by decide) (by decide) (by decide)
      hv5 hv6 cO cO8 cO16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact s6)
      Fr.hret Fr.hjt Fr.hbt
      (fun a h1 h2 => Memory.readable_of_writable (by rw [cwr, vwr, wr6]; exact ws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [cwr, vwr, wr6]; exact ws a (by omega) (by omega))
  have run := run1.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans run10)))))))
  refine ⟨ω10, μ10, run.mono (by omega), n1, n5, n6, ?_, ?_, ⟨9223372036854775829, by decide, nO, by decide⟩,
    ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact nO,
      by rw [← readN_sub μ10 (F + 120) 232 8 8 _ rfl (by decide)]; exact nO8,
      by rw [← readN_sub μ10 (F + 120) 232 16 8 _ rfl (by decide)]; exact nO16,
      by rw [← readN_sub μ10 (F + 120) 232 24 8 _ rfl (by decide)]; exact nO24⟩, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega)).trans ((cfr _ (by omega) (by omega)).trans
      (vfr _ (by omega) (by omega) (by omega))))]
    exact dR0
  · rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega)).trans ((cfr _ (by omega) (by omega)).trans
      (vfr _ (by omega) (by omega) (by omega))))]
    exact dR8.trans (by congr 1 <;> omega)
  · intro a h0 h1 h2 h3
    rw [nfr a h0 (by omega), cfr a h0 (by omega), vfr a h0 (by omega) (by omega)]
    exact b6 a h0 (by omega) h2
  · intro a; rw [nrd, crd, vrd, drd, krd, grd]
  · intro a; rw [nwr, cwr, vwr, dwr, kwr, gwr]

/-- The slot of `AssignForGasCost` with no hashes: the discriminant 2^63 + 23, the assigner's four octets `g` at 32,
    the core's two `c` at 36, and the empty `Vec` {0, 1, 0} at 8. -/
def AssignGasEmptyRep (c g : List UInt8) (bs : List UInt8) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775831 ∧ (bs.drop 32).take 4 = g ∧ (bs.drop 36).take 2 = c ∧
    (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧ (bs.drop 16).take 8 = Num.encodeLE 8 1 ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 0

/-- **`AssignForGasCost` with q = []** (tag 24, encoded 24 :: (c ++ ℰ(0) ++ g); GP v0.8.0 B.7). -/
theorem assign_gas_emptyF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (c g : List UInt8) (hc : c.length = 2) (hg : g.length = 4) :
    ElemOkF p P F RD (24 :: (c ++ 0 :: g)) (AssignGasEmptyRep c g) := by
  obtain ⟨c0, c1, rfl⟩ : ∃ c0 c1, c = [c0, c1] := by
    match c, hc with | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨g0, g1, g2, g3, rfl⟩ : ∃ g0 g1 g2 g3, g = [g0, g1, g2, g3] := by
    match g, hg with | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  have hl : (24 :: ([c0, c1] ++ 0 :: [g0, g1, g2, g3])).length - 1 = 7 := rfl
  simp only [hl, List.headD_cons, List.tail_cons] at tag hlen hpb pay rpay ⊢
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  have he0 : Blob.encodeNat 0 = [0] := by decide
  have hw1 : (Blob.encodeNat 0).length = 1 := by decide
  have pc : μ.readN ptr 2 = [c0, c1] := by
    have := readN_sub μ ptr 7 0 2 _ pay (by omega); simpa using this
  have pe : μ.readN (ptr + 2) 1 = Blob.encodeNat 0 := by
    have := readN_sub μ ptr 7 2 1 _ pay (by omega); rw [he0]; simpa using this
  have pg : μ.readN (ptr + 3) 4 = [g0, g1, g2, g3] := by
    have := readN_sub μ ptr 7 3 4 _ pay (by omega); simpa using this
  have hcv : Num.decodeLE [c0, c1] < 65536 := by
    have := decodeLE_lt [c0, c1]; rw [hc] at this; simpa using this
  have ec : Num.encodeLE 2 (Num.decodeLE [c0, c1]) = [c0, c1] := by
    have := encodeLE_decodeLE [c0, c1]; rwa [hc] at this
  have hgv : Num.decodeLE [g0, g1, g2, g3] < 4294967296 := by
    have := decodeLE_lt [g0, g1, g2, g3]; rw [hg] at this; simpa using this
  have eg : Num.encodeLE 4 (Num.decodeLE [g0, g1, g2, g3]) = [g0, g1, g2, g3] := by
    have := encodeLE_decodeLE [g0, g1, g2, g3]; rwa [hg] at this
  -- the dispatch and the handler's frame
  obtain ⟨ω1, run1, d0, d1, d5, d6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ
    F 24 (by decide) (by omega) h1 h7 (by simpa using tag) tab (Fr.hr F (by omega) (by omega)) rt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    ag1 (p := p) (P := P) (R := R) x ω1 μ F (F + 120) RD
      ⟨by omega, by omega⟩ (d1.trans h1) (d5.trans h5) (d6.trans h6) (by omega) (by omega)
      (fun a h1 h2 => ws a (by omega) (by omega))
  -- the core, into S + 32
  obtain ⟨ω3, μ3, run3, g0', g1', g2', g3', g4', g5', g6', g12', g7', gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1174 25390 (F - 80) RD
      (F - 48) ptr len 2 f0 f1 f7 f8 f9 (by omega) jte_586 bs_25390 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hlen'
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact rpay a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rL)
  have low3 : ∀ a, a < 4278050816 → μ3.read a = μ.read a := fun a ha =>
    (gfr a (by omega) (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  -- the core parked, and the call of decodeU32
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k24, kfr, krd, kwr⟩ :=
    ag2 (p := p) (P := P) (R := R) x ω3 μ3 (F - 80) (F + 120) RD
      (Num.decodeLE [c0, c1]) ⟨by omega, by omega⟩ (g1'.trans f1) (g5'.trans f5) (g6'.trans f6) g7'
      (by omega) hcv
      (by rw [show F - 80 + 32 = F - 48 by omega, gbuf,
        Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), pc, ec])
      (fun a h1 h2 => by rw [gwr, fwr]; exact ws a (by omega) (by omega))
  have low4 : ∀ a, a < 4278050816 → μ4.read a = μ.read a := fun a ha =>
    (kfr a (by omega) (Or.inl (by omega))).trans (low3 a ha)
  -- the length ℰ(0)
  obtain ⟨ω5, μ5, run5, ⟨e0, e1, -, -, -, e5, e6, -, e7, e8, eR0, eR8, efr, erd, ewr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω4 μ4 1176 25408 (F - 80) RD (ptr + 2)
      (len - 2) k0 k1 k7 (by decide) jte_587 bs_25408 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact wr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR8)
      0 (by omega) (by rw [hw1]; omega)
      (fun a h1 h2 => by rw [hw1] at h2; rw [krd, grd, frd]; exact rpay a (by omega) (by omega))
      (by rw [hw1, Memory.readN_congr (fun j hj => low4 _ (by omega))]; exact pe)
  rw [hw1] at eR0 eR8
  have low5 : ∀ a, a < 4278050816 → μ5.read a = μ.read a := fun a ha =>
    (efr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (low4 a ha)
  have wr5 : ∀ a, μ5.writable a = μ.writable a := fun a => by rw [ewr, kwr, gwr, fwr]
  -- the call of the hash-Vec decoder, and no hashes
  obtain ⟨ω6, run6, a0, a1, a5, a6, a7, a8, a9⟩ :=
    ag3 (p := p) (P := P) (R := R) x ω5 μ5 (F - 80) (F + 120) RD 0 (by omega)
      (by rw [e1, k1]) (by rw [e5, k5]) (by rw [e6, k6]) e7 e8 (by omega) (by omega)
  obtain ⟨ω7, μ7, run7, v0, v1, v5', v6', vO, vO8, vO16, vfr, vrd, vwr⟩ :=
    Decode.VecHash.vec_hash_empty (p := p) (P := P) (R := R) x ω6 μ5 (F - 232) (F - 80 + 32) RD 1178 25431
      (F + 120) RD ⟨by omega, by omega⟩ a0 (by rw [a1, show F - 232 + 152 = F - 80 by omega]) a5 a6 a7 a8 a9
      (by omega) (by omega) (by omega) (by decide) jte_588 bs_25431 (by omega) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr5]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr5]; exact ws a (by omega) (by omega))
  have wr7 : ∀ a, μ7.writable a = μ.writable a := fun a => by rw [vwr, wr5]
  -- the Vec copied, and the assigner's call
  obtain ⟨ω8, μ8, run8, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    ag4 (p := p) (P := P) (R := R) x ω7 μ7 (F - 80) (F + 120) RD 0 1 0
      ⟨by omega, by omega⟩ (by rw [v1]; congr 1; omega) v5' v6' (by omega) (by decide) (by decide)
      (by decide) vO
      (by rw [show F - 80 + 40 = F - 80 + 32 + 8 by omega]; exact vO8)
      (by rw [show F - 80 + 48 = F - 80 + 32 + 16 by omega]; exact vO16)
      (fun a h1 h2 => by rw [wr7]; exact ws a (by omega) (by omega))
  have low8 : ∀ a, a < 4278050816 → μ8.read a = μ.read a := fun a ha =>
    (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((vfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (low5 a ha))
  have pg8 : μ8.readN (ptr + 3) 4 = [g0, g1, g2, g3] := by
    rw [Memory.readN_congr (fun j hj => low8 _ (by omega))]; exact pg
  obtain ⟨ω9, μ9, run9, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω8 μ8 1180 25470 (F - 80) RD
      (F - 48) (ptr + 3) (len - 2 - 1) 4 m0 m1 m7 (by rw [m8]; congr 1; omega) m9
      (by omega) jte_589 bs_25470
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [mwr, wr7]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, wr7]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [mwr, wr7]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mrd, vrd, erd, krd, grd, frd]; exact rpay a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (by omega) (by omega)).trans
        (vfr _ (by omega) (by omega) (by omega)))]; exact eR0)
      (by rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (by omega) (by omega)).trans
        (vfr _ (by omega) (by omega) (by omega)))]; exact eR8)
  -- the frame above S, from the start to before the store
  have up9 : ∀ a, (F - 24) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ9.read a = μ2.read a := fun a h0 h1 h3 =>
    (nfr a h1 (by omega) h3 (by omega)).trans
      ((mfr a h1 (by omega) (by omega)).trans
      ((vfr a h1 (by omega) (by omega)).trans
      ((efr a h1 (by omega) h3).trans ((kfr a h1 (by omega)).trans
        (gfr a h1 (by omega) h3 (by omega))))))
  have up2 : ∀ a, F ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h0 h1 =>
    ffr a h1 (Or.inr h0)
  have sv : ∀ a v, a + 8 ≤ RD → F ≤ a → μ.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up9 _ (by omega) (by omega) (by omega)).trans
      (up2 _ (by omega) (by omega)))]; exact h
  have sH : ∀ a v, (F - 80) ≤ a → a + 8 ≤ (F - 56) → μ8.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega) (by omega))]
    exact h
  have sK4 : ∀ a v, (F - 56) ≤ a → a + 8 ≤ (F - 48) → μ4.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega) (by omega)).trans
      ((mfr _ (by omega) (by omega) (by omega)).trans ((vfr _ (by omega) (by omega) (by omega)).trans
        (efr _ (by omega) (by omega) (by omega)))))]
    exact h
  have sA : ∀ a v, (F - 24) ≤ a → a + 8 ≤ F → μ2.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up9 _ (by omega) (by omega) (by omega))]; exact h
  have wr9 : ∀ a, μ9.writable a = μ.writable a := fun a => by rw [nwr, mwr, wr7]
  -- the variant, into the slot O, and the returns
  obtain ⟨ω10, μ10, run10, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    ag5 (p := p) (P := P) (R := R) x ω9 μ9 (F - 80) (F + 120) 18 723 v5 v6 RD
      0 1 0 (Num.decodeLE [g0, g1, g2, g3]) (Num.decodeLE [c0, c1]) (by omega) (by omega) (Or.inr (by omega))
      (n1.trans m1) (n5.trans m5) n7 hv5 hv6 (by omega) (by omega) (by decide) (by decide) (by decide) hgv hcv
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24)
      (by rw [show F - 80 + 32 = F - 48 by omega, nbuf, pg8, eg])
      (by rw [show F - 80 + 72 = F - 8 by omega]; exact sA _ _ (by omega) (by omega) f72)
      (by rw [show F - 80 + 64 = F - 16 by omega]; exact sA _ _ (by omega) (by omega) f64)
      (by rw [show F - 80 + 56 = F - 24 by omega]; exact sA _ _ (by omega) (by omega) f56)
      (by rw [show F - 80 + 128 = F + 48 by omega]; exact sv _ _ (by omega) (by omega) s0)
      (by rw [show F - 80 + 120 = F + 40 by omega]; exact sv _ _ (by omega) (by omega) s5)
      (by rw [show F - 80 + 112 = F + 32 by omega]; exact sv _ _ (by omega) (by omega) s6)
      Fr.hret Fr.hjt Fr.hbt
      (fun a h1 h2 => by rw [wr9]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr9]; exact ws a (by omega) (by omega)))
  have run := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans (run8.trans (run9.trans run10))))))))
  refine ⟨ω10, μ10, run.mono (by omega), (by rw [o1]; congr 1; omega), o5, o6, ?_, ?_,
    ⟨9223372036854775831, by omega, oO, by omega⟩,
    ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact oO,
      by rw [← readN_sub μ10 (F + 120) 232 32 4 _ rfl (by decide), oO32, eg],
      by rw [← readN_sub μ10 (F + 120) 232 36 2 _ rfl (by decide), oO36, ec],
      by rw [← readN_sub μ10 (F + 120) 232 8 8 _ rfl (by decide)]; exact oO8,
      by rw [← readN_sub μ10 (F + 120) 232 16 8 _ rfl (by decide)]; exact oO16,
      by rw [← readN_sub μ10 (F + 120) 232 24 8 _ rfl (by decide)]; exact oO24⟩, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (by omega))]
    exact nR0.trans (by congr 1 <;> omega)
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (by omega))]
    exact nR8.trans (by congr 1 <;> omega)
  · intro a h0 h1 h2 h3
    rw [ofr a h0 (by omega), nfr a h0 (by omega) h2 (by omega), mfr a h0 (by omega) (by omega),
      vfr a h0 (by omega) (by omega), efr a h0 (by omega) h2, kfr a h0 (by omega),
      gfr a h0 (by omega) h2 (by omega)]
    exact ffr a h0 (by omega)
  · intro a; rw [ord, nrd, mrd, vrd, erd, krd, grd, frd]
  · intro a; rw [owr, nwr, mwr, vwr, ewr, kwr, gwr, fwr]

section
open Picoalloc Services.Bootstrap.CodeA Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Encode.GrowH Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.DropVecH
  Services.Bootstrap.Refine.DropVecW Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.PkgT

/-- **`AssignForGasCost(c, [], a)`'s decoded slot is good**, owning nothing. -/
theorem slotOK_assignGasEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (c a : Nat) (hw : (Spec.Instr.assignForGasCost c [] a).WF C) (bs : List UInt8)
    (μr : Memory) (hE : AssignGasEmptyRep (Codec.fixed 2 c) (Codec.fixed 4 a) bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.assignForGasCost c [] a).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨h0, hg, hc, h8, h16, h24⟩ := hE
  let R := Encode.Enc.AssignGasRepAt 1 (Codec.fixed 2 c) 0 [] (Codec.fixed 4 a)
  have hz : ∀ μ : Memory, μ.readN 1 (32 * 0) = [] := fun μ => by simp [Memory.readN]
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP 1 (32 * 0) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' _ ⟨e0, e1, e2, e8, e16, e24, _⟩ => ⟨e0, e1, e2, e8, e16, e24, hz μ'⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact hg, by rw [hel]; exact hc, by rw [hel]; exact h8,
      by rw [hel]; exact h16, by rw [hel]; exact h24, hz μ⟩
  have henc : (Spec.Instr.assignForGasCost c [] a).encode =
      24 :: (Codec.fixed 2 c ++ Blob.encodeNat 0 ++ [] ++ Codec.fixed 4 a) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP 1 (32 * 0),
    assign_gasH_232 env K pb hK1 hK 1 (Codec.fixed 2 c) 0 [] (Codec.fixed 4 a)
      (by simp [Codec.fixed]) rfl (by simp [Codec.fixed]) (by omega) (by omega), hrep, hrep,
    fun bs μ h => ⟨.assignForGasCost c [] a, hw, (Encode.Enc.assignGasRep_iff _ 0 [] _ bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, fun q m h => absurd h.1 (by simp),
    Or.inr (Or.inr ⟨false, 1, ⟨0, 0, false⟩, ?_, by omega, fun h => absurd h (by simp)⟩)⟩
  exact Or.inr (Or.inl ⟨24, 0, by omega, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
    by rw [rd 16 8 (by omega)]; exact h16, by simp⟩)

/-- **`AssignForGasCost(c, [], a)`'s package.** -/
theorem pkg_assignGasEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (c a : Nat) (hw : (Spec.Instr.assignForGasCost c [] a).WF C) :
    DecPkg env K pb gl p P (.assignForGasCost c [] a) (PassSlot env K pb p P C (.assignForGasCost c [] a)) := by
  have he : (Spec.Instr.assignForGasCost c [] a).encode = 24 :: (Codec.fixed 2 c ++ 0 :: Codec.fixed 4 a) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ assign_gas_emptyF F RD hL _ _ (by simp [Codec.fixed])
    (by simp [Codec.fixed])) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (t := 24) (by unfold PassIdx; omega)) hb.1
    (slotOK_assignGasEmpty env K pb hK1 hK C c a hw bs μr hb)

/-- **`RandomStorageAccumulate(Some [])`'s decoded slot is good**, owning nothing. -/
theorem slotOK_rsaEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (hw : (Spec.Instr.randomStorageAccumulate (some [])).WF C) (bs : List UInt8)
    (μr : Memory) (hE : RSAEmptyRep bs) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.randomStorageAccumulate (some [])).encode bs (fun _ => False) μr := by
  intro μ s el hel _
  obtain ⟨h0, h8, h16, h24⟩ := hE
  let R := EncRSA.RSAOkRepAt 1 0 []
  have hz : ∀ μ : Memory, μ.readN 1 (32 * 0) = [] := fun μ => by simp [Memory.readN]
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP 1 (32 * 0) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' _ ⟨e0, e8, e16, e24, _⟩ => ⟨e0, e8, e16, e24, hz μ'⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact h16, by rw [hel]; exact h24, hz μ⟩
  have henc : (Spec.Instr.randomStorageAccumulate (some [])).encode = 22 :: 0 :: (Blob.encodeNat 0 ++ []) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP 1 (32 * 0), EncRSA.rsa_okH_232 env K pb hK1 hK 1 0 [] rfl (by omega) (by omega), hrep, hrep,
    fun bs μ h => ⟨.randomStorageAccumulate (some []), hw, (EncRSA.rsaOkRep_iff 0 [] bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, fun q m h => absurd h.1 (by simp),
    Or.inr (Or.inr ⟨false, 1, ⟨0, 0, false⟩, ?_, by omega, fun h => absurd h (by simp)⟩)⟩
  exact Or.inr (Or.inr (Or.inr ⟨0, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
    by rw [rd 16 8 (by omega)]; exact h16, by simp⟩))

/-- **`RandomStorageAccumulate(Some [])`'s package.** -/
theorem pkg_rsaEmpty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (gl : Nat → UInt8)
    (C : Spec.Consts) (hw : (Spec.Instr.randomStorageAccumulate (some [])).WF C) :
    DecPkg env K pb gl p P (.randomStorageAccumulate (some []))
      (PassSlot env K pb p P C (.randomStorageAccumulate (some []))) := by
  have he : (Spec.Instr.randomStorageAccumulate (some [])).encode = [22, 0, 0] := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]; rfl
  refine pkg_ofF (fun F RD hL => he ▸ rsa_emptyF F RD hL) (fun cs bs μr hb => ?_)
  exact passSlot_noown _ (passW_idx (t := 22) (by unfold PassIdx; omega)) hb.1
    (slotOK_rsaEmpty env K pb hK1 hK C hw bs μr hb)

end

end Services.Bootstrap.Refine.GapEmpty
