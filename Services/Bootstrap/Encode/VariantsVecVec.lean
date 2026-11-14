import Services.Bootstrap.Encode.VariantsVec
import Services.Bootstrap.Decode.VecVecElem

/-!
# `Instruction::encode_to`: `Imported` (19), a `Vec<Vec<u8>>`

`Imported { data }` holds a `Vec<Vec<u8>>` `{cap m, ptr q, len m}` at S + 8, its m elements the
24-octet `Vec<u8>`s `{cap nⱼ, ptr qⱼ, len nⱼ}` at q + 24 j, element j's nⱼ octets at qⱼ (as
`Decode.VecVecElem` writes it: `VecVecRep`, here with q and the qⱼ explicit, `ImportedRepAt`). The arm
(19983) appends 19 and ℰ(m), then loops over the elements (20058 … 20115), appending ℰ(nⱼ) and the
octets of each (GP v0.8.0 Appendix C: a sequence of sequences, each with its length prefix): the encoding
is 19 :: ℰ(m) ++ (ℰ(n₀) ++ e₀) ++ … The heap octets read (`ImportedSrc`) are the elements' array
[q, q + 24 m) and each element's padded stretch (`VecSrc`). The code traps on lengths of 2^32 or more.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.VecVecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Imported { data }`'s slot, with its addresses**: `VecVecRep (2^63 + 18)` with the array q and the
    elements' addresses `qs` given. -/
def ImportedRepAt (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775826 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 es.length ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 es.length ∧
    ∀ j (hj : j < es.length),
      μ.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j]

/-- The decode side's `VecVecRep` for `Imported` is `ImportedRepAt` for some q and qs. -/
theorem vecVecRep_iff (es : List (List UInt8)) (bs : List UInt8) (μ : Memory) :
    Decode.VecVecElem.VecVecRep 9223372036854775826 es bs μ ↔ ∃ q qs, ImportedRepAt q qs es bs μ := by
  constructor
  · rintro ⟨h0, q, qs, h1, h2, h3, h4⟩; exact ⟨q, qs, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, qs, h0, h1, h2, h3, h4⟩; exact ⟨h0, q, qs, h1, h2, h3, h4⟩

/-- **`Imported`'s heap octets**: the elements' array and each element's padded stretch. -/
def ImportedSrc (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (a : Nat) : Prop :=
  (q ≤ a ∧ a < q + 24 * es.length) ∨ ∃ j, ∃ hj : j < es.length, VecSrc (qs j) es[j].length a

theorem encodeNat_pos (n : Nat) : 1 ≤ (Blob.encodeNat n).length := by
  unfold Blob.encodeNat
  split
  · simp
  · split <;> simp

/-- The encodings of the first k elements, and of the rest. -/
theorem encs_split (es : List (List UInt8)) (k : Nat) :
    (encs es).flatten = (encs (es.take k)).flatten ++ (encs (es.drop k)).flatten := by
  rw [← List.flatten_append, encs, encs, encs, ← List.map_append, List.take_append_drop]

theorem encs_take_succ (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    (encs (es.take (k + 1))).flatten =
      (encs (es.take k)).flatten ++ (Blob.encodeNat es[k].length ++ es[k]) := by
  unfold encs
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.map_append, List.flatten_append]
  simp

theorem encs_drop (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    (encs (es.drop k)).flatten =
      (Blob.encodeNat es[k].length ++ es[k]) ++ (encs (es.drop (k + 1))).flatten := by
  unfold encs
  rw [List.drop_eq_getElem_cons hk, List.map_cons, List.flatten_cons]

/-- The output after the tag, the count and the first k elements. -/
def preI (es : List (List UInt8)) (k : Nat) : List UInt8 :=
  UInt8.ofNat 19 :: (Blob.encodeNat es.length ++ (encs (es.take k)).flatten)

theorem preI_succ (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    preI es (k + 1) = preI es k ++ Blob.encodeNat es[k].length ++ es[k] := by
  simp [preI, encs_take_succ es k hk]

theorem enc_split (es : List (List UInt8)) (k : Nat) (hk : k < es.length) :
    (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8) =
      (preI es k ++ Blob.encodeNat es[k].length) ++ es[k] ++ (encs (es.drop (k + 1))).flatten := by
  rw [encs_split es k, encs_drop es k hk]
  simp [preI] <;> rfl

theorem preI_len (es : List (List UInt8)) (k : Nat) :
    (preI es k).length ≤ (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length := by
  rw [encs_split es k]; simp [preI]

theorem preI_all (es : List (List UInt8)) :
    preI es es.length = (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8) := by
  simp [preI] <;> rfl

/-- **`Imported`'s element loop** (20058 … 20115): from the loop's head for element k (ω₅ = q + 24 k + 16,
    ω₉ = 24 i, the octets of the i = m − k > 0 elements left) in `StD (preI k)`, the loop encodes the
    elements k … m − 1 and reaches the end at 20118 in `StD (preI m)`. -/
theorem imported_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (μ : Memory) {D F S v cap ptr len ret t r5 r6 : Nat} (q : Nat) (qs : Nat → Nat) (es : List (List UInt8))
    (L : LayD P D F S v cap ptr len (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length
      ret t μ) (hD : 192 ≤ D)
    (hsrc : ∀ a, ImportedSrc q qs es a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨
        ptr + len + (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length ≤ a) ∧
      (a < v ∨ v + 24 ≤ a))
    (arr : ∀ j (hj : j < es.length), μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j])
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j))
    (hm : es.length < 4294967296) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = es.length → 0 < i →
      StD D F v ptr len ret r5 r6 μ (preI es k) ω μ1 → ω[5] = UInt64.ofNat (q + 24 * k + 16) →
      ω[9] = UInt64.ofNat (24 * i) →
      ∃ ω' μ', FreeStepsH p R 20058 ω μ1 x 20118 ω' μ' x
          (2000 * ((19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length -
            (preI es k).length)) ∧
        StD D F v ptr len ret r5 r6 μ (preI es es.length) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h9
    have hk : k < es.length := by omega
    have hpk := preI_len es k
    -- the element's words in the array, as at entry
    have hA : ∀ a, q + 24 * k + 8 ≤ a → a < q + 24 * k + 24 → a < 4294967296 ∧ μ.readable a = true ∧
        (a < F - D ∨ F ≤ a) ∧ (a < ptr + len ∨
          ptr + len + (19 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length ≤ a) ∧
        (a < v ∨ v + 24 ≤ a) := fun a h1 h2 => hsrc a (Or.inl ⟨by omega, by omega⟩)
    have hAF := side (X := F - D) (Y := F) (by omega) (show q + 24 * k + 8 < q + 24 * k + 24 by omega)
      (fun a h1 h2 => (hA a h1 h2).2.2.1)
    have hA32 := (hA (q + 24 * k + 23) (by omega) (by omega)).1
    have kA : ∀ a, q + 24 * k + 8 ≤ a → a < q + 24 * k + 24 → μ1.read a = μ.read a := fun a h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hA a h1 h2
      have := (preI_len es k)
      exact st.keep a a0 a2 (by omega) (by omega)
    obtain ⟨ar8, ar16, arb⟩ := arr k hk
    have hn := hlens k hk
    obtain ⟨hqk, hqk'⟩ := hqs k hk
    have hlenk := preI_len es (k + 1)
    rw [preI_succ es k hk] at hlenk
    simp only [List.length_append] at hlenk
    have hE := encodeNat_pos es[k].length
    -- the element's length prefix
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, be, br, bn, bfr, brd, bwr⟩ := seg_20058 (p := p) (P := P)
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
      es[k].length 898 20092 b0 (by rw [b7]; congr 1; omega) b8
      (by rw [show F - 32 = F - 56 + 24 by omega]; exact bn) ⟨by decide, by decide, by decide⟩ jte_448
      bs_20092 (by omega)
    -- the element's octets
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := seg_20092 (p := p) (P := P) (R := R) x ω3 μ3 (F - 56) v
      (qs k) es[k].length (by omega) (by omega) hqk (by omega) st3.h1 (by rw [c6, b6])
      (by rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact be)
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
      (fun a h1 h2 => by rw [st3.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    have L' := L
    rw [enc_split es k hk] at L'
    obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := heapD (p := p) (P := P) (R := R) x ω4 μ3 μ L' (by omega)
      ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.sv, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩ (qs k)
      es[k].length 900 20106 rfl arb d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_449 bs_20106 hqk'
      (fun a ha => by rw [← enc_split es k hk]; exact hsrc a (Or.inr ⟨k, hk, ha⟩))
    have st5' := st5.cast (preI_succ es k hk).symm
    have r8 : μ5.readN (F - 56 + 8) 8 = Num.encodeLE 8 (24 * (i + 1)) := by
      rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact br
    have h5' : ω5[5] = UInt64.ofNat (q + 24 * k + 16) := by rw [e5, d5, c5, b5]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- the last element
      obtain ⟨ω6, run6, f1⟩ := seg_20106_last (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) (by omega) st5'.h1 r8
        (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      have hkm : k + 1 = es.length := by omega
      refine ⟨ω6, μ5, (run2.trans (run3.trans (run4.trans (run5.trans run6)))).mono ?_,
        StD.cast (by rw [hkm])
          ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩⟩
      omega
    · obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_20106_more (p := p) (P := P) (R := R) x ω5 μ5 (F - 56)
        (q + 24 * k + 16) (24 * (i + 1)) (by omega) (by omega) ⟨by omega, by omega⟩ st5'.h1 h5' r8
        (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      obtain ⟨ω7, μ7, run7, st7⟩ := ih (k + 1) ω6 μ5 (by omega) hi
        ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
        (by rw [f5]; congr 1 <;> omega) (by rw [f9]; congr 1 <;> omega)
      refine ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono ?_, st7⟩
      rw [preI_succ es k hk]
      simp only [List.length_append]
      have := preI_len es k
      omega


/-- **`Imported { data }`** (tag 19): a value holding the discriminant 2^63 + 18 and the `Vec<Vec<u8>>`
    `{cap m, ptr q, len m}` whose elements at q + 24 j are `{cap nⱼ, ptr qs j, len nⱼ}` with the octets
    eⱼ at qs j (`ImportedRepAt`), m < 2^32 and every nⱼ < 2^32, encodes to
    19 :: ℰ(m) ++ (ℰ(n₀) ++ e₀) ++ … ++ (ℰ(nₘ₋₁) ++ eₘ₋₁) (GP v0.8.0 Appendix C), reading the heap octets
    `ImportedSrc`. -/
theorem imported {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j)) :
    EncOkMD p P 192 (19 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (ImportedRepAt q qs es)
      (ImportedSrc q qs es) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 19) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 es.length := by
    rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hp0 := preI_len es 0
  have hl0 : (preI es 0).length = 1 + (Blob.encodeNat es.length).length := by simp [preI, encs] <;> omega
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startV (p := p) (P := P) (R := R) x ω μ L (by decide) 19
    (Or.inr rfl) h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 19 = 19983 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_tag5 (p := p) (P := P) (R := R)
    x ω1 μ1 19983 19 894 (F - 56) v S (Or.inr ⟨rfl, rfl, rfl⟩) (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 19] 1 894 20006 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_446 bs_20006
    (by simp <;> omega) bt
  -- the count's length prefix
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dq, dn, dfr, drd, dwr⟩ := seg_20006 (p := p) (P := P)
    (R := R) x ω3 μ3 (F - 56) v S q es.length (by omega) (by omega) (by omega) hq64 hm st3.h1
    (by rw [c5, b5]) (by rw [c6, b6])
    (by rw [st3.slot L (by simp <;> omega) 16 8 (by decide)]; exact c16)
    (by rw [st3.slot L (by simp <;> omega) 24 8 (by decide)]; exact c24)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega) (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := prefixD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    es.length 896 20039 d0 (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
    ⟨by decide, by decide, by decide⟩ jte_447 bs_20039 (by simp <;> omega)
  have st5' := st5.cast (show [] ++ [UInt8.ofNat 19] ++ Blob.encodeNat es.length = preI es 0 by simp [preI, encs])
  have h5 : ω5[5] = UInt64.ofNat es.length := by rw [e5, d5]
  rcases Nat.eq_zero_or_pos es.length with hm0 | hm0
  · -- no elements
    obtain ⟨ω6, run6, rfl⟩ := seg_20039_zero (p := p) (P := P) (R := R) x ω5 μ5 (by rw [h5, hm0])
    exact closeD L (by decide) 20118 _ (by decide) (by omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      (st5'.cast (by rw [show (0 : Nat) = es.length from hm0.symm, preI_all]))
  · have hq32 := (hsrc q (Or.inl ⟨Nat.le_refl _, by omega⟩)).1
    obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_20039_pos (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) q es.length
      (by omega) (by omega) ⟨hm0, hm⟩ st5'.h1 h5
      (by rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact dq)
      (fun a h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    obtain ⟨ω7, μ7, run7, st7⟩ := imported_loop (p := p) (P := P) (R := R) x μ q qs es L (by decide) hsrc
      (fun j hj => ⟨(rarr j hj).2.1, (rarr j hj).2.2.1, (rarr j hj).2.2.2⟩) hlens hqs hm es.length 0 ω6 μ5
      (by omega) hm0
      ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
      (by rw [f5]) (by rw [f9])
    exact closeD L (by decide) 20118 _ (by decide) (by omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
      (st7.cast (preI_all es))

/-- `imported` at the depth 232. -/
theorem imported_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616 ∧ (0 < es[j].length → 65536 ≤ qs j)) :
    EncOkMD p P 232 (19 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (ImportedRepAt q qs es)
      (ImportedSrc q qs es) :=
  (imported q qs es hm hq64 hlens hqs).mono (by decide)

end Services.Bootstrap.Encode.Enc
