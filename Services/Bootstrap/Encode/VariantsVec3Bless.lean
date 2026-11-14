import Services.Bootstrap.Encode.VariantsVec3Core
import Services.Bootstrap.Encode.VariantsVec3Segs
import Services.Bootstrap.Decode.BlessHeap
import Services.Bootstrap.Encode.VariantsVecVec

/-!
# `Instruction::encode_to`: `Bless` (11)

`Bless { manager, assigner, designator, registrar: u32, always_acc: Vec<(u32, u64)> }` (dispatch index
11, discriminant word 2^63 + 10) holds the four `u32`s' octets m, a, d, r at S + 32, S + 36, S + 40,
S + 44 and the `Vec` `{cap n, ptr q, len n}` at S + 8, its n elements 16 octets each at q + 16 j (the
`u32` at + 0, the `u64` at + 8), as `Decode.BlessHeap` writes it (`BlessRep`, here with q explicit:
`BlessRepAt`). The arm (18163) appends 11, m, a, d, r, ℰ(n) and then each element's 4 + 8 octets
(GP v0.8.0 Appendix C: fixed-width integers little-endian, the sequence with its length prefix), so the
encoding is 11 :: m ++ a ++ d ++ r ++ ℰ(n) ++ items, items the 12 n octets of the pairs: exactly the
octets `Decode.Bless.bless_elem` decodes. The elements are read through registers (no copy from the
heap), so the heap octets `Src` are the elements' array [q, q + 16 n). The code traps (18276 → 20397)
when n ≥ 2^32.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Bless`'s slot, with the elements at q**: `Decode.Bless.BlessRep` with its q given. -/
def BlessRepAt (q : Nat) (m a d r : List UInt8) (n : Nat) (items : List UInt8) (bs : List UInt8)
    (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775818 ∧ (bs.drop 32).take 4 = m ∧ (bs.drop 36).take 4 = a ∧
  (bs.drop 40).take 4 = d ∧ (bs.drop 44).take 4 = r ∧
  (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧
    ∀ j, j < n → μ.readN (q + 16 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ.readN (q + 16 * j + 8) 8 = (items.drop (12 * j + 4)).take 8

/-- The decode side's `BlessRep` is `BlessRepAt` for some q. -/
theorem blessRep_iff (m a d r : List UInt8) (n : Nat) (items bs : List UInt8) (μ : Memory) :
    Decode.Bless.BlessRep m a d r n items bs μ ↔ ∃ q, BlessRepAt q m a d r n items bs μ := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, q, h5, h6, h7, h8⟩; exact ⟨q, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨q, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩; exact ⟨h0, h1, h2, h3, h4, q, h5, h6, h7, h8⟩

/-- **`Bless`'s heap octets**: the elements' array [q, q + 16 n). -/
def BlessSrc (q n : Nat) (a : Nat) : Prop := q ≤ a ∧ a < q + 16 * n

theorem take12_succ (items : List UInt8) (k : Nat) :
    items.take (12 * (k + 1)) =
      items.take (12 * k) ++ (items.drop (12 * k)).take 4 ++ (items.drop (12 * k + 4)).take 8 := by
  rw [show 12 * (k + 1) = 12 * k + 4 + 8 by omega, List.take_add, List.take_add]

/-- **`Bless`'s element loop** (18315 … 18363): from the loop's head for element k (ω₅ = q + 16 k, the
    writer in ω₆, the end q + 16 n at sp + 8) in `StD (pre0 ++ items.take (12 k))`, with i = n − k > 0
    elements left, the loop appends each element's `u32` and `u64` and reaches the end at 20118 in
    `StD (pre0 ++ items)`. -/
theorem bless_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    (μ : Memory) {D F S v cap ptr len ret t r5 r6 : Nat} (q n : Nat) (pre0 items : List UInt8)
    (hi : items.length = 12 * n)
    (L : LayD P D F S v cap ptr len (pre0 ++ items).length ret t μ) (hD : 136 ≤ D)
    (hsrc : ∀ a, BlessSrc q n a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + (pre0 ++ items).length ≤ a) ∧ (a < v ∨ v + 24 ≤ a))
    (arr : ∀ j, j < n → μ.readN (q + 16 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ.readN (q + 16 * j + 8) 8 = (items.drop (12 * j + 4)).take 8) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StD D F v ptr len ret r5 r6 μ (pre0 ++ items.take (12 * k)) ω μ1 →
      ω[5] = UInt64.ofNat (q + 16 * k) → ω[6] = UInt64.ofNat v →
      μ1.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 16 * n) →
      ∃ ω' μ', FreeStepsH p R 18315 ω μ1 x 20118 ω' μ' x (2000 * (12 * i)) ∧
        StD D F v ptr len ret r5 r6 μ (pre0 ++ items) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 hz
    have hk : k < n := by omega
    have hA : ∀ b, q + 16 * k ≤ b → b < q + 16 * k + 16 → b < 4294967296 ∧ μ.readable b = true ∧
        (b < F - D ∨ F ≤ b) ∧ (b < ptr + len ∨ ptr + len + (pre0 ++ items).length ≤ b) ∧
        (b < v ∨ v + 24 ≤ b) := fun b h1 h2 => hsrc b ⟨by omega, by omega⟩
    have hA32 := (hA (q + 16 * k + 15) (by omega) (by omega)).1
    have hqn := (hsrc (q + 16 * n - 1) ⟨by omega, by omega⟩).1
    have hlenk : (items.take (12 * k)).length = 12 * k := by simp [hi]; omega
    have hlenk1 : (items.take (12 * (k + 1))).length = 12 * (k + 1) := by simp [hi]; omega
    have hNl : (pre0 ++ items).length = pre0.length + 12 * n := by simp [hi]
    have kA : ∀ b, q + 16 * k ≤ b → b < q + 16 * k + 16 → μ1.read b = μ.read b := fun b h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hA b h1 h2
      exact st.keep b a0 a2 (by simp [hlenk] at a3 ⊢; omega) (by omega)
    obtain ⟨ar4, ar8⟩ := arr k hk
    -- the element's u32
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18315 (p := p) (P := P)
      (R := R) x ω μ1 (F - 56) v (q + 16 * k) (by omega) (by omega) (by omega) st.h1 h5 h6
      (fun b h1 h2 => by rw [st.rd]; exact (hA b (by omega) (by omega)).2.1)
      (fun b h1 h2 => by rw [st.wr]; exact L.hwF b (by omega) (by omega))
    have st2 := st.scratch L hD (by simp [hlenk, hNl]; omega) b1 (fun b h0 h1 => bfr b h0 (by omega)) brd bwr
    obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2
      ((items.drop (12 * k)).take 4) 4 740 18336 (by simp [hi]; omega) (by decide) b0 b7 b8 b9
      ⟨by decide, by decide, by decide⟩ jte_369 bs_18336 (by simp [hlenk, hNl]; omega)
      (by rw [bt, Memory.readN_congr (fun j hj => kA _ (by omega) (by omega))]; exact ar4)
    -- the element's u64
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_18336 (p := p) (P := P)
      (R := R) x ω3 μ3 (F - 56) v (q + 16 * k) (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5, h5])
      (by rw [c6, b6, h6])
      (fun b h1 h2 => by rw [st3.rd]; exact (hA b (by omega) (by omega)).2.1)
      (fun b h1 h2 => by rw [st3.wr]; exact L.hwF b (by omega) (by omega))
    have st4 := st3.scratch L hD (by simp [hlenk, hNl]; omega) d1 (fun b h0 h1 => dfr b h0 (by omega)) drd dwr
    have kA3 : ∀ b, q + 16 * k + 8 ≤ b → b < q + 16 * k + 16 → μ3.read b = μ.read b := fun b h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hA b (by omega) h2
      exact st3.keep b a0 a2 (by simp [hlenk] at a3 ⊢; omega) (by omega)
    obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L hD st4
      ((items.drop (12 * k + 4)).take 8) 8 742 18357 (by simp [hi]; omega) (by decide) d0 d7 d8 d9
      ⟨by decide, by decide, by decide⟩ jte_370 bs_18357 (by simp [hlenk, hNl]; omega)
      (by rw [dt, Memory.readN_congr (fun j hj => kA3 _ (by omega) (by omega))]; exact ar8)
    have st5' := st5.cast (show pre0 ++ items.take (12 * k) ++ (items.drop (12 * k)).take 4 ++
      (items.drop (12 * k + 4)).take 8 = pre0 ++ items.take (12 * (k + 1)) by
        rw [take12_succ]; simp [List.append_assoc])
    have hz5 : μ5.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 16 * n) := by
      rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hz
    have h5' : ω5[5] = UInt64.ofNat (q + 16 * k) := by rw [e5, d5, c5, b5, h5]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω6, run6, f1⟩ := seg_18357_last (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) (q + 16 * k)
        (by omega) (by omega) st5'.h1 h5' (by rw [show q + 16 * k + 16 = q + 16 * n by omega]; exact hz5)
        (fun b h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF b (by omega) (by omega)))
      have hkn : 12 * (k + 1) = items.length := by omega
      refine ⟨ω6, μ5, (run2.trans (run3.trans (run4.trans (run5.trans run6)))).mono (by omega),
        StD.cast (by rw [hkn, List.take_length])
          ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩⟩
    · obtain ⟨ω6, run6, f1, f5, f6⟩ := seg_18357_more (p := p) (P := P) (R := R) x ω5 μ5 (F - 56)
        (q + 16 * k) (q + 16 * n) (by omega) (by omega) (by omega) (by omega) st5'.h1 h5' hz5
        (fun b h1 h2 => by rw [st5'.rd]; exact Memory.readable_of_writable (L.hwF b (by omega) (by omega)))
      obtain ⟨ω7, μ7, run7, st7⟩ := ih (k + 1) ω6 μ5 (by omega) hi0
        ⟨f1.trans st5'.h1, st5'.s0, st5'.s5, st5'.s6, st5'.sv, st5'.vl, st5'.out, st5'.keep, st5'.rd, st5'.wr⟩
        (by rw [f5]; congr 1) (by rw [f6, e6, d6, c6, b6, h6]) hz5
      exact ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono (by omega),
        st7⟩

/-- **A tag piece** of `Bless` (18163) or `Assign` (18429): from `StD pre` at the arm, `StD (pre ++ [tag])`
    at the call's return e', with S in ω₅ and the writer in ω₆. -/
theorem pieceTagD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ μ0 : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8}
    (L : LayD P D F S v cap ptr len N ret t μ0) (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ)
    (e tag r e' : Nat) (he : (e = 18163 ∧ tag = 11 ∧ r = 728) ∨ (e = 18429 ∧ tag = 12 ∧ r = 752))
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S) (hn : pre.length + 1 ≤ N) :
    ∃ ω' μ', FreeStepsH p R e ω μ x e' ω' μ' x 377 ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ [UInt8.ofNat tag]) ω' μ' ∧
      ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS' := L.hS'
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_tagB (p := p) (P := P) (R := R)
    x ω μ e tag r (F - 56) v S he (by omega) (by omega) (by omega) st.h1 h10 h11
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ0 L hD st2
    [UInt8.ofNat tag] 1 r e' rfl (by decide) b0 b7 b8 b9 hr hje hbe hn bt
  exact ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6⟩

/-- **A `u32` piece** of `Bless` (18186, 18207, 18228, 18249): from `StD pre` with S in ω₅ and the
    writer in ω₆, `StD (pre ++ field)` at the call's return e', the field the 4 octets at S + off at
    entry. -/
theorem pieceU32D {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ μ0 : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8}
    (L : LayD P D F S v cap ptr len N ret t μ0) (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ)
    (e r off e' : Nat)
    (he : (e = 18186 ∧ r = 730 ∧ off = 32) ∨ (e = 18207 ∧ r = 732 ∧ off = 36) ∨
      (e = 18228 ∧ r = 734 ∧ off = 40) ∨ (e = 18249 ∧ r = 736 ∧ off = 44))
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v) (hn : pre.length + 4 ≤ N) :
    ∃ ω' μ', FreeStepsH p R e ω μ x e' ω' μ' x 400 ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ μ0.readN (S + off) 4) ω' μ' ∧
      ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS' := L.hS'; have hS := L.hS
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by omega
  have hoff : off + 4 ≤ 232 := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_u32B (p := p) (P := P) (R := R)
    x ω μ e r off (F - 56) v S he (by omega) (by omega) (by omega) st.h1 h5 h6
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ0 L hD st2
    (μ0.readN (S + off) 4) 4 r e' (by simp [Memory.readN]) (by decide) b0 b7 b8 b9 hr hje hbe hn
    (by rw [bt, st.slot L (by omega) off 4 hoff])
  exact ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans (b5.trans h5), c6.trans (b6.trans h6)⟩

/-- **`Bless`** (dispatch index 11): a value holding the discriminant 2^63 + 10, the four `u32`s' octets
    m, a, d, r at S + 32 … S + 44 and the `Vec<(u32, u64)>` `{cap n, ptr q, len n}` at S + 8 whose n
    elements at q + 16 j hold pair j of the 12 n octets `items` (`BlessRepAt`), n < 2^32, encodes to
    11 :: m ++ a ++ d ++ r ++ ℰ(n) ++ items (GP v0.8.0 Appendix C), reading the heap octets
    `BlessSrc q n` = [q, q + 16 n). The callee frames reach F − 192 (the length prefix). -/
theorem bless {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (m a d r : List UInt8) (n : Nat) (items : List UInt8)
    (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4) (hr4 : r.length = 4)
    (hi : items.length = 12 * n) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMD p P 192 (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items)) (BlessRepAt q m a d r n items)
      (BlessSrc q n) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, rm, ra, rd, rr, r8, r16, r24, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 11) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have cm : μ.readN (S + 32) 4 = m := by rw [← slot_take μ S 32 4 (by decide)]; exact rm
  have ca : μ.readN (S + 36) 4 = a := by rw [← slot_take μ S 36 4 (by decide)]; exact ra
  have cd : μ.readN (S + 40) 4 = d := by rw [← slot_take μ S 40 4 (by decide)]; exact rd
  have cr : μ.readN (S + 44) 4 = r := by rw [← slot_take μ S 44 4 (by decide)]; exact rr
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hE := encodeNat_pos n
  have hN : (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items) : List UInt8).length =
      17 + (Blob.encodeNat n).length + 12 * n := by
    simp [hm4, ha4, hd4, hr4, hi] <;> omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD (p := p) (P := P) (R := R) x ω μ L (by decide) 11
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 11 = 18163 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b5, b6⟩ := pieceTagD (p := p) (P := P) (R := R) x ω1 μ1 μ L (by decide) st1
    18163 11 728 18186 (Or.inl ⟨rfl, rfl, rfl⟩) jte_363 bs_18186 a10 a11 (by simp <;> omega)
  obtain ⟨ω3, μ3, run3, st3, c5, c6⟩ := pieceU32D (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    18186 730 32 18207 (Or.inl ⟨rfl, rfl, rfl⟩) jte_364 bs_18207 b5 b6 (by simp <;> omega)
  obtain ⟨ω4, μ4, run4, st4, d5, d6⟩ := pieceU32D (p := p) (P := P) (R := R) x ω3 μ3 μ L (by decide) st3
    18207 732 36 18228 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) jte_365 bs_18228 c5 c6 (by simp [hm4] <;> omega)
  obtain ⟨ω5, μ5, run5, st5, e5, e6⟩ := pieceU32D (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    18228 734 40 18249 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) jte_366 bs_18249 d5 d6
    (by simp [hm4] <;> omega)
  obtain ⟨ω6, μ6, run6, st6, f5, f6⟩ := pieceU32D (p := p) (P := P) (R := R) x ω5 μ5 μ L (by decide) st5
    18249 736 44 18270 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) jte_367 bs_18270 e5 e6
    (by simp [hm4] <;> omega)
  rw [cm, ca, cd, cr] at st6
  have hl6 : ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r : List UInt8).length = 17 := by
    simp [hm4, ha4, hd4, hr4]
  -- the length prefix
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, g7, g8, gn, gfr, grd, gwr⟩ := seg_18270 (p := p) (P := P) (R := R)
    x ω6 μ6 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st6.h1 f5
    (by rw [st6.slot L (by omega) 16 8 (by decide)]; exact c16)
    (by rw [st6.slot L (by omega) 24 8 (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st6.sv)
    (fun a h1 h2 => by rw [st6.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st6.wr]; exact L.hwF a (by omega) (by omega))
  have st7 := st6.scratch L (by decide) (by omega) g1 (fun a h0 h1 => gfr a h0 (by omega)) grd gwr
  obtain ⟨ω8, μ8, run8, st8, k5, k6, kF⟩ := prefixD (p := p) (P := P) (R := R) x ω7 μ7 μ L (by decide) st7
    n 738 18298 g0 (by rw [g7]; congr 1; omega) g8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact gn)
    ⟨by decide, by decide, by decide⟩ jte_368 bs_18298 (by rw [hl6]; omega)
  have hpre0 : ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n : List UInt8).length =
      17 + (Blob.encodeNat n).length := by simp [hm4, ha4, hd4, hr4] <;> omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no elements
    subst hn0
    have hi0 : items = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hi0
    obtain ⟨ω9, run9, rfl⟩ := seg_18298_zero (p := p) (P := P) (R := R) x ω8 μ8 (by rw [k6, g6])
    exact closeD L (by decide) 20118 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        run9))))))))
      (st8.cast (by simp))
  · have hqn := (hsrc (q + 16 * n - 1) ⟨by omega, by omega⟩).1
    obtain ⟨ω9, μ9, run9, h91, h95, h96, h9z, h9fr, h9rd, h9wr⟩ := seg_18298_pos (p := p) (P := P) (R := R)
      x ω8 μ8 (F - 56) v q n (by omega) (by omega) (by omega) hn0 st8.h1 (by rw [k5, g5]) (by rw [k6, g6])
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st8.sv)
      (fun a h1 h2 => by rw [st8.wr]; exact L.hwF a (by omega) (by omega))
    have st9 := st8.scratch L (by decide) (by rw [hpre0, hN]; omega) h91
      (fun a h0 h1 => h9fr a h0 (by omega)) h9rd h9wr
    have henc : (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items) : List UInt8) =
        ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n) ++ items := by
      simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl
    have L' := L; rw [henc] at L'
    obtain ⟨ω10, μ10, run10, st10⟩ := bless_loop (p := p) (P := P) (R := R) x μ q n
      ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n) items hi L' (by decide)
      (fun b hb => by rw [← henc]; exact hsrc b hb) rarr n 0 ω9 μ9 (by omega) hn0
      (st9.cast (by simp)) (by rw [h95]; congr 1) h96 h9z
    exact closeD L (by decide) 20118 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        (run9.trans run10)))))))))
      (st10.cast henc.symm)

/-- `bless` at the depth 232. -/
theorem bless_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (m a d r : List UInt8) (n : Nat) (items : List UInt8)
    (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4) (hr4 : r.length = 4)
    (hi : items.length = 12 * n) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMD p P 232 (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items)) (BlessRepAt q m a d r n items)
      (BlessSrc q n) :=
  (bless q m a d r n items hm4 ha4 hd4 hr4 hi hn hq64).mono (by decide)

end Services.Bootstrap.Encode.Enc
