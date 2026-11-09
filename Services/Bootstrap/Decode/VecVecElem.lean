import Services.Bootstrap.Decode.VecVecU8
import Services.Bootstrap.Decode.LoopA

/-!
# `DeleteItems`, `Export` and `Imported`, as elements of the decode loop

The three `Vec<Vec<u8>>` variants (tags 5, 10, 19; GP v0.8.0 B.7, the bootstrap service's instruction
list) with 1 … 682 items of at most 16384 octets each, stated as `ElemOkAF`: from the decode loop's
frame at F (the tag at F, the slot at F + 120, the reader at RD, laid out as `Lay F RD`),
`Instruction::decode` returns the variant into the slot (`VecVecRep`), its items a fresh `Vec` of
fresh `Vec<u8>`s in the heap; or an allocation fails. The decoder's helper opens its frame at
F − 48 (`VecEmpty.e1` … `e4`) and calls the element reader at 8 (`VecVecU8.vec_vec_u8_heap`).
-/

namespace Services.Bootstrap.Decode.VecVecElem

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.VecEmpty Services.Bootstrap.Decode.VecVecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A `Vec<Vec<u8>>` variant's slot**: the discriminant word W, then the items, a `Vec` of capacity
    and length n = |es| at some q, item j at q + 24j the `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` whose
    octets at qs j are es[j] (in the heap μ). -/
def VecVecRep (W : Nat) (es : List (List UInt8)) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 W ∧
  ∃ q, ∃ qs : Nat → Nat, (bs.drop 8).take 8 = Num.encodeLE 8 es.length ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 es.length ∧
    ∀ j (hj : j < es.length),
      μ.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j]

/-- **`DeleteItems` (5), `Export` (10) or `Imported` (19), as an element of the decode loop**: the
    encoding [tag] ++ ℰ(n) ++ the items' encodings (each ℰ(|e|) ++ e), with 1 ≤ n = |es| ≤ 682 and every
    item at most 16384 octets, decodes to the variant's slot (`VecVecRep` with its discriminant word W),
    the items in fresh chunks of the heap; or an allocation fails. -/
theorem vecvec_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (tag h r1 r2 r3 W : Nat)
    (htag : (tag = 5 ∧ h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ W = 9223372036854775812) ∨
      (tag = 10 ∧ h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ W = 9223372036854775826))
    (es : List (List UInt8)) (hn : 1 ≤ es.length ∧ es.length ≤ 682) (hes : ∀ e ∈ es, e.length ≤ 16384) :
    ElemOkAF env cap pb gl p P F RD (34668 * es.length + 3000)
      (tag :: (Blob.encodeNat es.length ++ (encs es).flatten)) (VecVecRep W es) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tagr rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  obtain ⟨l1, l2, l3, l4⟩ := hL
  have hs : Shape h r1 r2 r3 8 := by
    unfold Shape
    rcases htag with ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ <;> simp
  have hh : handler tag = h := by
    rcases htag with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  have ht25 : tag < 25 := by omega
  have hr3 : 0 < r3 ∧ r3 ≤ 2806 ∧ r3 % 2 = 0 := by omega
  have hr2 : 0 < r2 ∧ r2 ≤ 2806 ∧ r2 % 2 = 0 := by omega
  obtain ⟨bs1, bs2, bs3⟩ := shape_bs (p := p) (P := P) hs
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, (encs es).flatten.length = L := ⟨_, rfl⟩
  have hlen' : (tag :: (Blob.encodeNat es.length ++ (encs es).flatten)).length - 1 = w + L := by
    simp [hN, hW, hLd]
  simp only [hlen', List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tagr ⊢
  rw [hN] at pay
  have hw1 : 1 ≤ w := by
    rw [← hW]; unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hencw : μ.readN ptr w = Blob.encodeNat n := by
    have := readN_sub μ ptr (w + L) 0 w _ pay (by omega)
    simp only [Nat.add_zero] at this
    rw [this, List.drop_zero, List.take_left' hW]
  have hpd : μ.readN (ptr + w) L = (encs es).flatten := by
    rw [readN_sub μ ptr (w + L) w L _ pay (by omega), List.drop_left' hW]
    exact List.take_of_length_le (by omega)
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨hcpb, hcpT, hcpT'⟩ := VecU8.chunk_in H.wf hcp hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  -- the dispatch, the helper's frame and the length
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ F tag
    ht25 (by omega) h1 h7 (by simpa using tagr) tab (Memory.readable_of_writable (ws F (by omega) (by omega))) rt
  rw [hh] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    e1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ h r1 r2 r3 8 F (F + 120) RD hs ⟨by omega, by omega⟩
      (e1'.trans h1) (e5'.trans h5) (e6'.trans h6) (by omega) (by omega) (fun a h1 h2 => ws a (by omega) (by omega))
  have hra : ∀ a, ptr ≤ a → a < ptr + w + L → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (VecU8.heap_writable H hcp hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω3, μ3, run3, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 r2 _ (F - 48) RD ptr len b0 b1 b7
      hr2 rfl bs2 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [bwr]; exact ws a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact wr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact rL) n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [brd]; exact hra a h1 (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hencw)
  rw [hW] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := e2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    h r1 r2 r3 8 (F - 48) n hs (by omega) (by omega) (by rw [d1, b1]) d7 d8
  have b3 : ∀ a, a < 4294967296 → (a < F - 176 ∨ F ≤ a) → (a < RD ∨ RD + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [dwr, bwr]
  have H3 : HeapCtx env pb S0 S1 μ3 s :=
    VecU8.ctx_congr_data H hcp (fun a h1 _ => b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr3
  have run04 := run1.trans (run2.trans (run3.trans run4))
  -- the items
  rcases vec_vec_u8_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω4 μ3 s (F - 48) (F - 48) RD (ptr + w)
      (len - w) r3 _ (F + 120) RD pb S0 S1 es H3 ⟨cp, hcp, hcpu, by omega, by omega⟩ ⟨by unfold S0; omega, by unfold S1; omega⟩
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) (by rw [c6, d6, b6]) c7
      (by rw [c8, d6, b6]) (by rw [c9, hN]) hr3 rfl bs3 (by omega) (by omega) hn hes ⟨by omega, by omega⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨Nat.le_refl _, by unfold S1; omega⟩ (Or.inl (by omega)) dR0 dR8
      (by rw [hLd, Memory.readN_congr (fun j hj => b3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]; exact hpd) with
    ⟨s', ω5, μ5, q, cs, qs, run5, hq, v0, v1, v5', v6', vc, vp, vl, vR0, vR8, H5, keep, kd5, hcs, hrep, vfr, vlo, vgl, vwr⟩ |
    ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run04 ex).mono (by omega))
  rw [hLd, hN] at vR0 vR8
  rw [hN] at vc vl
  -- the copy into the slot and the return
  have hfrH : ∀ a, F - 24 ≤ a → a < F + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))).trans
      (dfr a (by omega) (by omega) (Or.inl (by omega)))
  sorry

end Services.Bootstrap.Decode.VecVecElem
