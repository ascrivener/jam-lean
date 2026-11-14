import Services.Bootstrap.Encode.VariantsVecVec
import Services.Bootstrap.Encode.VariantsVec2Segs

/-!
# `Instruction::encode_to`: `DeleteItems` (dispatch index 5), a `Vec<Vec<u8>>`

`DeleteItems { items }` holds a `Vec<Vec<u8>>` `{cap m, ptr q, len m}` at S + 8, its m items the
24-octet `Vec<u8>`s `{cap nⱼ, ptr qⱼ, len nⱼ}` at q + 24 j, item j's nⱼ octets at qⱼ (as
`Decode.VecVecElem` writes it for tag 5: `VecVecRep (2^63 + 4)`, here with q and the qⱼ explicit,
`DeleteItemsRepAt`; `deleteItemsRep_iff` is the bridge). The arm (19117, the code of `Imported`'s arm
at other addresses, `Encode.VariantsVecVec`) appends 5 and ℰ(m), then loops over the items
(19193 … 19250), appending ℰ(nⱼ) and the octets of each (GP v0.8.0 Appendix C: a sequence of
sequences, each with its length prefix): the encoding is 5 :: ℰ(m) ++ (ℰ(n₀) ++ e₀) ++ … The heap
octets read are `ImportedSrc` (the items' array [q, q + 24 m) and each item's padded stretch
`VecSrc`). The code traps (20397) on lengths of 2^32 or more, hence m < 2^32 and every nⱼ < 2^32.

`startD` is the dispatch into `StD []` for any variant with a discriminant word (index 1 … 24).
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.VecVecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- From 30145 to the arm of the variant with discriminant word 2^63 + t − 1 (1 ≤ t ≤ 24), in `StD []`,
    with the writer in ω₁₀ and the value in ω₁₁ (`Fixed.start` with the stack [F − D, F)). -/
theorem startD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t' : Nat} (L : LayD P D F S v cap ptr len N ret t' μ) (hD : 136 ≤ D)
    (t : Nat) (ht : 1 ≤ t ∧ t < 25)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a10, a11, a0', a5', a6', av, afr, ard, awr⟩ := dispatch (p := p) (P := P)
    (R := R) x ω μ F S v ret ω[5].toNat ω[6].toNat t ht ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hD8 tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', av, ?_, by simp [Memory.readN],
    fun a h0 h1 _ _ => afr a h0 (by omega), ard, awr⟩, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- **`DeleteItems { items }`'s slot, with its addresses**: `VecVecRep (2^63 + 4)` with the array q and
    the items' addresses `qs` given. -/
def DeleteItemsRepAt (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (bs : List UInt8) (μ : Memory) :
    Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775812 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 es.length ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 es.length ∧
    ∀ j (hj : j < es.length),
      μ.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j]

/-- The decode side's `VecVecRep` for `DeleteItems` (tag 5) is `DeleteItemsRepAt` for some q and qs. -/
theorem deleteItemsRep_iff (es : List (List UInt8)) (bs : List UInt8) (μ : Memory) :
    Decode.VecVecElem.VecVecRep 9223372036854775812 es bs μ ↔ ∃ q qs, DeleteItemsRepAt q qs es bs μ := by
  constructor
  · rintro ⟨h0, q, qs, h1, h2, h3, h4⟩; exact ⟨q, qs, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, qs, h0, h1, h2, h3, h4⟩; exact ⟨h0, q, qs, h1, h2, h3, h4⟩

/-- `DeleteItems`' output after the tag, the count and the first k items. -/
def preDI (es : List (List UInt8)) (k : Nat) : List UInt8 :=
  UInt8.ofNat 5 :: (Blob.encodeNat es.length ++ (encs (es.take k)).flatten)

theorem preDI_succ (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    preDI es (k + 1) = preDI es k ++ Blob.encodeNat es[k].length ++ es[k] := by
  simp [preDI, encs_take_succ es k hk]

theorem encDI_split (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8) =
      (preDI es k ++ Blob.encodeNat es[k].length) ++ es[k] ++ (encs (es.drop (k + 1))).flatten := by
  rw [encs_split es k, encs_drop es k hk]
  simp [preDI] <;> rfl

theorem preDI_len (es : List (List UInt8)) (k : Nat) :
    (preDI es k).length ≤ (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length := by
  rw [encs_split es k]; simp [preDI]

theorem preDI_all (es : List (List UInt8)) :
    preDI es es.length = (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8) := by
  simp [preDI] <;> rfl

/-- **`DeleteItems`' item loop** (19193 … 19250): from the loop's head for item k (ω₅ = q + 24 k + 16,
    ω₉ = 24 i, the octets of the i = m − k > 0 elements left) in `StD (preDI k)`, the loop encodes the
    elements k … m − 1 and reaches the end at 20118 in `StD (preDI m)`. -/
theorem delete_items_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (μ : Memory) {D F S v cap ptr len ret t r5 r6 : Nat} (q : Nat) (qs : Nat → Nat) (es : List (List UInt8))
    (L : LayD P D F S v cap ptr len (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length
      ret t μ) (hD : 192 ≤ D)
    (hsrc : ∀ a, ImportedSrc q qs es a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨
        ptr + len + (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length ≤ a) ∧
      (a < v ∨ v + 24 ≤ a))
    (arr : ∀ j (hj : j < es.length), μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j])
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j))
    (hm : es.length < 4294967296) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = es.length → 0 < i →
      StD D F v ptr len ret r5 r6 μ (preDI es k) ω μ1 → ω[5] = UInt64.ofNat (q + 24 * k + 16) →
      ω[9] = UInt64.ofNat (24 * i) →
      ∃ ω' μ', FreeStepsH p R 19193 ω μ1 x 20118 ω' μ' x
          (2000 * ((5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length -
            (preDI es k).length)) ∧
        StD D F v ptr len ret r5 r6 μ (preDI es es.length) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h9
    have hk : k < es.length := by omega
    have hpk := preDI_len es k
    -- the element's words in the array, as at entry
    have hA : ∀ a, q + 24 * k + 8 ≤ a → a < q + 24 * k + 24 → a < 4294967296 ∧ μ.readable a = true ∧
        (a < F - D ∨ F ≤ a) ∧ (a < ptr + len ∨
          ptr + len + (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length ≤ a) ∧
        (a < v ∨ v + 24 ≤ a) := fun a h1 h2 => hsrc a (Or.inl ⟨by omega, by omega⟩)
    have hAF := side (X := F - D) (Y := F) (by omega) (show q + 24 * k + 8 < q + 24 * k + 24 by omega)
      (fun a h1 h2 => (hA a h1 h2).2.2.1)
    have hA32 := (hA (q + 24 * k + 23) (by omega) (by omega)).1
    have kA : ∀ a, q + 24 * k + 8 ≤ a → a < q + 24 * k + 24 → μ1.read a = μ.read a := fun a h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hA a h1 h2
      have := (preDI_len es k)
      exact st.keep a a0 a2 (by omega) (by omega)
    obtain ⟨ar8, ar16, arb⟩ := arr k hk
    have hn := hlens k hk
    obtain ⟨hqk, hqk'⟩ := hqs k hk
    have hlenk := preDI_len es (k + 1)
    rw [preDI_succ es k hk] at hlenk
    simp only [List.length_append] at hlenk
    have hE := encodeNat_pos es[k].length
    -- the element's length prefix
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, be, br, bn, bfr, brd, bwr⟩ := seg_19193 (p := p) (P := P)
      (R := R) x ω μ1 (F - 56) v (q + 24 * k + 16) (qs k) es[k].length (24 * (i + 1)) (by omega) (by omega)
      ⟨by omega, by omega⟩ hqk hn (by omega) st.h1 h5 h9
      (by rw [Memory.readN_congr (fun j hj => kA _ (by omega) (by omega))]; exact ar16)
      (by rw [show q + 24 * k + 16 - 8 = q + 24 * k + 8 by omega,
        Memory.readN_congr (fun j hj => kA _ (by omega) (by omega))]; exact ar8)
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun a h1 h2 => by rw [st.rd]; exact (hA a (by omega) (by omega)).2.1) (by omega)
      (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
    have st2 := st.scratch L (by omega) (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
    obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := prefixD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2
      es[k].length 824 19227 b0 (by rw [b7]; congr 1; omega) b8
      (by rw [show F - 32 = F - 56 + 24 by omega]; exact bn) ⟨by decide, by decide, by decide⟩ jte_411
      bs_19227 (by omega)
    -- the element's octets
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := seg_19227 (p := p) (P := P) (R := R) x ω3 μ3 (F - 56) v
      (qs k) es[k].length (by omega) (by omega) hqk (by omega) st3.h1 (by rw [c6, b6])
      (by rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact be)
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
      (fun a h1 h2 => by rw [st3.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    have L' := L
    rw [encDI_split es k hk] at L'
    obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := heapD (p := p) (P := P) (R := R) x ω4 μ3 μ L' (by omega)
      ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.sv, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩ (qs k)
      es[k].length 826 19241 rfl arb d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_412 bs_19241 hqk'
      (fun a ha => by rw [← encDI_split es k hk]; exact hsrc a (Or.inr ⟨k, hk, ha⟩))
    have st5' := st5.cast (preDI_succ es k hk).symm
    have r8 : μ5.readN (F - 56 + 8) 8 = Num.encodeLE 8 (24 * (i + 1)) := by
      rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact br
    have h5' : ω5[5] = UInt64.ofNat (q + 24 * k + 16) := by rw [e5, d5, c5, b5]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- the last element
      obtain ⟨ω6, run6, f1⟩ := seg_19241_last (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) (by omega) st5'.h1 r8
        (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      have hkm : k + 1 = es.length := by omega
      refine ⟨ω6, μ5, (run2.trans (run3.trans (run4.trans (run5.trans run6)))).mono ?_,
        StD.cast (by rw [hkm])
          ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩⟩
      omega
    · obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_19241_more (p := p) (P := P) (R := R) x ω5 μ5 (F - 56)
        (q + 24 * k + 16) (24 * (i + 1)) (by omega) (by omega) ⟨by omega, by omega⟩ st5'.h1 h5' r8
        (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      obtain ⟨ω7, μ7, run7, st7⟩ := ih (k + 1) ω6 μ5 (by omega) hi
        ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
        (by rw [f5]; congr 1 <;> omega) (by rw [f9]; congr 1 <;> omega)
      refine ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono ?_, st7⟩
      rw [preDI_succ es k hk]
      simp only [List.length_append]
      have := preDI_len es k
      omega


/-- **`DeleteItems { items }`** (tag 5): a value holding the discriminant 2^63 + 4 and the `Vec<Vec<u8>>`
    `{cap m, ptr q, len m}` whose elements at q + 24 j are `{cap nⱼ, ptr qs j, len nⱼ}` with the octets
    eⱼ at qs j (`DeleteItemsRepAt`), m < 2^32 and every nⱼ < 2^32, encodes to
    5 :: ℰ(m) ++ (ℰ(n₀) ++ e₀) ++ … ++ (ℰ(nₘ₋₁) ++ eₘ₋₁) (GP v0.8.0 Appendix C), reading the heap octets
    `ImportedSrc`. -/
theorem delete_items {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j)) :
    EncOkMD p P 192 (5 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (DeleteItemsRepAt q qs es)
      (ImportedSrc q qs es) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 5) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 es.length := by
    rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hp0 := preDI_len es 0
  have hl0 : (preDI es 0).length = 1 + (Blob.encodeNat es.length).length := by simp [preDI, encs] <;> omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD (p := p) (P := P) (R := R) x ω μ L (by decide) 5
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 5 = 19117 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19117 (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 5] 1 820 19140 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_409 bs_19140
    (by simp <;> omega) bt
  -- the count's length prefix
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dq, dn, dfr, drd, dwr⟩ := seg_19140 (p := p) (P := P)
    (R := R) x ω3 μ3 (F - 56) v S q es.length (by omega) (by omega) (by omega) hq64 hm st3.h1
    (by rw [c5, b5]) (by rw [c6, b6])
    (by rw [st3.slot L (by simp <;> omega) 16 8 (by decide)]; exact c16)
    (by rw [st3.slot L (by simp <;> omega) 24 8 (by decide)]; exact c24)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega) (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := prefixD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    es.length 822 19173 d0 (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
    ⟨by decide, by decide, by decide⟩ jte_410 bs_19173 (by simp <;> omega)
  have st5' := st5.cast (show [] ++ [UInt8.ofNat 5] ++ Blob.encodeNat es.length = preDI es 0 by simp [preDI, encs])
  have h5 : ω5[5] = UInt64.ofNat es.length := by rw [e5, d5]
  rcases Nat.eq_zero_or_pos es.length with hm0 | hm0
  · -- no elements
    obtain ⟨ω6, run6, rfl⟩ := seg_19173_zero (p := p) (P := P) (R := R) x ω5 μ5 (by rw [h5, hm0])
    exact closeD L (by decide) 20118 _ (by decide) (by omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      (st5'.cast (by rw [show (0 : Nat) = es.length from hm0.symm, preDI_all]))
  · have hq32 := (hsrc q (Or.inl ⟨Nat.le_refl _, by omega⟩)).1
    obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_19173_pos (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) q es.length
      (by omega) (by omega) ⟨hm0, hm⟩ st5'.h1 h5
      (by rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact dq)
      (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    obtain ⟨ω7, μ7, run7, st7⟩ := delete_items_loop (p := p) (P := P) (R := R) x μ q qs es L (by decide) hsrc
      (fun j hj => ⟨(rarr j hj).2.1, (rarr j hj).2.2.1, (rarr j hj).2.2.2⟩) hlens hqs hm es.length 0 ω6 μ5
      (by omega) hm0
      ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
      (by rw [f5]) (by rw [f9])
    exact closeD L (by decide) 20118 _ (by decide) (by omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
      (st7.cast (preDI_all es))

/-- `delete_items` at the depth 232. -/
theorem delete_items_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j)) :
    EncOkMD p P 232 (5 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (DeleteItemsRepAt q qs es)
      (ImportedSrc q qs es) :=
  (delete_items q qs es hm hq64 hlens hqs).mono (by decide)

end Services.Bootstrap.Encode.Enc
