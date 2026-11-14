import Services.Bootstrap.Encode.VariantsVec3Bless
import Services.Bootstrap.Encode.VariantsVec3Segs2
import Services.Bootstrap.Decode.Assign

/-!
# `Instruction::encode_to`: `Assign` (12)

`Assign { core: u16, queue: [Hash; 𝖰], assigner: u32 }` (dispatch index 12, discriminant word
2^63 + 11) holds the queue as a `Vec` `{cap n, ptr q, len n}` at S + 8 whose n hashes are 32 octets
each at q + 32 k, the assigner's four octets w4 at S + 32 and the core's two c2 at S + 36, as
`Decode.Assign` writes it (`AssignRep`, here with q explicit: `AssignRepAt`). The arm (18429) appends 12,
c2, the n hashes (32 octets each, straight from the heap, no length prefix: the queue is a fixed-length
sequence, GP v0.8.0 Appendix C) and w4: the encoding is 12 :: c2 ++ hb ++ w4, hb the 32 n octets of the
hashes, exactly the octets `Decode.Assign.assign_elem` decodes (with n = 𝖰). The code takes n from the
`Vec`'s length (S + 24) and does not compare it with 𝖰. The heap octets `Src` are the padded stretch
`VecSrc q (32 n)`. The arm calls only `Vec<u8>::extend_from_slice`, so its callees stay in
[F − 136, F) (`EncOkMD 136`).
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Assign`'s slot, with the queue at q**: `Decode.Assign.AssignRep` with its q given. -/
def AssignRepAt (q n : Nat) (c2 hb w4 : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775819 ∧
  (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ (bs.drop 32).take 4 = w4 ∧ (bs.drop 36).take 2 = c2 ∧
    ∀ k, k < n → μ.readN (q + 32 * k) 32 = (hb.drop (32 * k)).take 32

/-- The decode side's `AssignRep` is `AssignRepAt` for some q. -/
theorem assignRep_iff (n : Nat) (c2 hb w4 bs : List UInt8) (μ : Memory) :
    Decode.Assign.AssignRep n c2 hb w4 bs μ ↔ ∃ q, AssignRepAt q n c2 hb w4 bs μ := by
  constructor
  · rintro ⟨h0, q, h1, h2, h3, h4, h5, h6⟩; exact ⟨q, h0, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨q, h0, h1, h2, h3, h4, h5, h6⟩; exact ⟨h0, q, h1, h2, h3, h4, h5, h6⟩

/-- **`Assign`'s queue loop** (18492 … 18513): from the loop's head for hash k (ω₈ = q + 32 k, ω₅ = 32 i
    with i = n − k > 0 hashes left) in `StD (pre0 ++ hb.take (32 k))`, the loop appends each hash's 32
    octets from the heap and reaches 18752 in `StD (pre0 ++ hb)`, the frame [F − 56, F) kept. -/
theorem assign_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    (μ : Memory) {D F S v cap ptr len ret t r5 r6 : Nat} (q n : Nat) (pre0 hb post : List UInt8)
    (hhb : hb.length = 32 * n)
    (L : LayD P D F S v cap ptr len (pre0 ++ hb ++ post).length ret t μ) (hD : 136 ≤ D)
    (hq : 65536 ≤ q)
    (hsrc : ∀ a, VecSrc q (32 * n) a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + (pre0 ++ hb ++ post).length ≤ a) ∧ (a < v ∨ v + 24 ≤ a))
    (arr : ∀ k, k < n → μ.readN (q + 32 * k) 32 = (hb.drop (32 * k)).take 32) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StD D F v ptr len ret r5 r6 μ (pre0 ++ hb.take (32 * k)) ω μ1 →
      ω[5] = UInt64.ofNat (32 * i) → ω[8] = UInt64.ofNat (q + 32 * k) →
      ∃ ω' μ', FreeStepsH p R 18492 ω μ1 x 18752 ω' μ' x (2000 * (32 * i)) ∧
        StD D F v ptr len ret r5 r6 μ (pre0 ++ hb) ω' μ' ∧
        (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ1.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h8
    have hk : k < n := by omega
    have hqn := (hsrc (q + 32 * n + 23) ⟨by omega, by omega, by omega⟩).1
    have hlenk : (hb.take (32 * k)).length = 32 * k := by simp [hhb]; omega
    have hNl : (pre0 ++ hb ++ post).length = pre0.length + 32 * n + post.length := by simp [hhb]; omega
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := seg_18492 (p := p) (P := P) (R := R) x ω μ1 (F - 56) v
      (q + 32 * k) (by omega) (by omega) (by omega) st.h1 h8
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun b h1 h2 => by rw [st.rd]; exact Memory.readable_of_writable (L.hwF b (by omega) (by omega)))
    obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := ext_srcD (p := p) (P := P) (R := R) x ω2 μ1 μ L hD
      ⟨b1.trans st.h1, st.s0, st.s5, st.s6, st.sv, st.vl, st.out, st.keep, st.rd, st.wr⟩ (q + 32 * k) 32 756
      18508 q (q + 32 * n) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_377 bs_18508
      (by simp [hlenk]; omega) (by decide) ⟨by omega, by omega⟩ hq
      (fun a h1 h2 => hsrc a ⟨by omega, h1, h2⟩)
    rw [arr k hk] at st3
    have st3' := st3.cast (show pre0 ++ hb.take (32 * k) ++ (hb.drop (32 * k)).take 32 =
      pre0 ++ hb.take (32 * (k + 1)) by rw [show 32 * (k + 1) = 32 * k + 32 by omega, List.take_add]; simp)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω4, run4, d1⟩ := seg_18508_last (p := p) (P := P) (R := R) x ω3 μ3 (by rw [c5, b5, h5])
      have hkn : 32 * (k + 1) = hb.length := by omega
      exact ⟨ω4, μ3, (run2.trans (run3.trans run4)).mono (by omega),
        StD.cast (by rw [hkn, List.take_length])
          ⟨d1.trans st3'.h1, st3'.s0, st3'.s5, st3'.s6, st3'.sv, st3'.vl, st3'.out, st3'.keep, st3'.rd, st3'.wr⟩,
        cF⟩
    · obtain ⟨ω4, run4, d1, d5, d8⟩ := seg_18508_more (p := p) (P := P) (R := R) x ω3 μ3 (i + 1)
        (q + 32 * k + 32) ⟨by omega, by omega⟩ (by omega) (by rw [c5, b5, h5]) (by rw [c6, b6])
      obtain ⟨ω5, μ5, run5, st5, kF5⟩ := ih (k + 1) ω4 μ3 (by omega) hi0
        ⟨d1.trans st3'.h1, st3'.s0, st3'.s5, st3'.s6, st3'.sv, st3'.vl, st3'.out, st3'.keep, st3'.rd, st3'.wr⟩
        (by rw [d5]; congr 1) (by rw [d8]; congr 1)
      exact ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by omega), st5,
        fun a h1 h2 => by rw [kF5 a h1 h2, cF a h1 h2]⟩

/-- **`Assign`'s end** (18752 … 18774 and the call): with S parked at sp = F − 56, the assigner's four
    octets w4 (S + 32) are appended; the call returns to 20383, the function's end. -/
theorem assign_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ μ0 : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8}
    (L : LayD P D F S v cap ptr len N ret t μ0) (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ)
    (w4 : List UInt8) (hw4 : μ0.readN (S + 32) 4 = w4)
    (s0 : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hn : pre.length + 4 ≤ N) :
    ∃ ω' μ', FreeStepsH p R 18752 ω μ x 20383 ω' μ' x 400 ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ w4) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS' := L.hS'; have hS := L.hS
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18752 (p := p) (P := P) (R := R)
    x ω μ (F - 56) v S (by omega) (by omega) (by omega) st.h1 s0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, _, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ0 L hD st2
    w4 4 918 20383 (by rw [← hw4]; simp [Memory.readN]) (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩
    jte_458 bs_20383 hn (by rw [bt, st.slot L (by omega) 32 4 (by decide), hw4])
  exact ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3⟩

/-- **`Assign`** (dispatch index 12): a value holding the discriminant 2^63 + 11, the queue `Vec`
    `{cap n, ptr q, len n}` at S + 8 whose n hashes at q + 32 k are the 32-octet pieces of hb, the
    assigner's four octets w4 at S + 32 and the core's two c2 at S + 36 (`AssignRepAt`) encodes to
    12 :: c2 ++ hb ++ w4 (GP v0.8.0 Appendix C), reading the heap octets `VecSrc q (32 n)`. -/
theorem assign {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P]
    (q n : Nat) (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * n)
    (hw4 : w4.length = 4) (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 136 (12 :: (c2 ++ hb ++ w4)) (AssignRepAt q n c2 hb w4) (VecSrc q (32 * n)) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, r32, r36, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 12) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have c32 : μ.readN (S + 32) 4 = w4 := by rw [← slot_take μ S 32 4 (by decide)]; exact r32
  have c36 : μ.readN (S + 36) 2 = c2 := by rw [← slot_take μ S 36 2 (by decide)]; exact r36
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hSF := L.hSF; have hd' := L.hd'
  have hN : (12 :: (c2 ++ hb ++ w4) : List UInt8).length = 7 + 32 * n := by
    simp [hc2, hhb, hw4]; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD (p := p) (P := P) (R := R) x ω μ L (by decide) 12
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 12 = 18429 from rfl] at run1
  obtain ⟨ω2, μ2, run2, st2, b5, b6⟩ := pieceTagD (p := p) (P := P) (R := R) x ω1 μ1 μ L (by decide) st1
    18429 12 752 18452 (Or.inr ⟨rfl, rfl, rfl⟩) jte_375 bs_18452 a10 a11 (by simp <;> omega)
  -- the core
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, ct, cfr, crd, cwr⟩ := seg_18452 (p := p) (P := P)
    (R := R) x ω2 μ2 (F - 56) v S (by omega) (by omega) (by omega) st2.h1 b5 b6
    (fun a h1 h2 => by rw [st2.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st2.wr]; exact L.hwF a (by omega) (by omega))
  have st3 := st2.scratch L (by decide) (by simp <;> omega) c1 (fun a h0 h1 => cfr a h0 (by omega)) crd cwr
  obtain ⟨ω4, μ4, run4, st4, d5, d6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω3 μ3 μ L (by decide) st3
    c2 2 754 18473 hc2 (by decide) c0 c7 c8 c9 ⟨by decide, by decide, by decide⟩ jte_376 bs_18473
    (by simp [hc2] <;> omega) (by rw [ct, st2.slot L (by simp <;> omega) 36 2 (by decide), c36])
  have hl4 : ([] ++ [UInt8.ofNat 12] ++ c2 : List UInt8).length = 3 := by simp [hc2]
  have h45 : ω4[5] = UInt64.ofNat S := by rw [d5, c5, b5]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- an empty queue
    subst hn0
    have hb0 : hb = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb0
    obtain ⟨ω5, μ5, run5, e1, e0, efr, erd, ewr⟩ := seg_18473_zero (p := p) (P := P) (R := R) x ω4 μ4
      (F - 56) S (by omega) (by omega) st4.h1 h45
      (by rw [st4.slot L (by omega) 24 8 (by decide)]; exact c24)
      (fun a h1 h2 => by rw [st4.rd]; exact L.hrS a (by omega) (by omega))
      (fun a h1 h2 => by rw [st4.wr]; exact L.hwF a (by omega) (by omega)) (by omega)
    have st5 := st4.scratch L (by decide) (by rw [hl4]; omega) (e1.trans st4.h1) (fun a h0 h1 => efr a h0 (by omega)) erd ewr
    obtain ⟨ω6, μ6, run6, st6⟩ := assign_tail (p := p) (P := P) (R := R) x ω5 μ5 μ L (by decide) st5 w4 c32
      e0 (by rw [hl4]; omega)
    exact closeD L (by decide) 20383 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) (st6.cast (by simp))
  · have hq' := hq hn0
    have hqn := (hsrc (q + 32 * n + 23) ⟨by omega, by omega, by omega⟩).1
    obtain ⟨ω5, μ5, run5, e1, e5, e8, e0, efr, erd, ewr⟩ := seg_18473_pos (p := p) (P := P) (R := R) x ω4 μ4
      (F - 56) S q n (by omega) (by omega) hq64 ⟨hn0, by omega⟩ st4.h1 h45
      (by rw [st4.slot L (by omega) 16 8 (by decide)]; exact c16)
      (by rw [st4.slot L (by omega) 24 8 (by decide)]; exact c24)
      (fun a h1 h2 => by rw [st4.rd]; exact L.hrS a (by omega) (by omega))
      (fun a h1 h2 => by rw [st4.wr]; exact L.hwF a (by omega) (by omega)) (by omega)
    have st5 := st4.scratch L (by decide) (by rw [hl4]; omega) (e1.trans st4.h1) (fun a h0 h1 => efr a h0 (by omega)) erd ewr
    have henc : (12 :: (c2 ++ hb ++ w4) : List UInt8) = ([] ++ [UInt8.ofNat 12] ++ c2) ++ hb ++ w4 := by
      simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl
    have L' := L; rw [henc] at L'
    obtain ⟨ω6, μ6, run6, st6, kF6⟩ := assign_loop (p := p) (P := P) (R := R) x μ q n
      ([] ++ [UInt8.ofNat 12] ++ c2) hb w4 hhb L' (by decide) hq' (fun a ha => by rw [← henc]; exact hsrc a ha)
      rarr n 0 ω5 μ5 (by omega) hn0 (st5.cast (by simp)) (by rw [e5]) (by rw [e8]; congr 1)
    obtain ⟨ω7, μ7, run7, st7⟩ := assign_tail (p := p) (P := P) (R := R) x ω6 μ6 μ L (by decide) st6 w4 c32
      (by rw [Memory.readN_congr (fun j hj => kF6 _ (by omega) (by omega))]; exact e0)
      (by simp [hc2, hhb] <;> omega)
    exact closeD L (by decide) 20383 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
      (st7.cast henc.symm)

/-- `assign` at the depth 232. -/
theorem assign_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P]
    (q n : Nat) (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * n)
    (hw4 : w4.length = 4) (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 232 (12 :: (c2 ++ hb ++ w4)) (AssignRepAt q n c2 hb w4) (VecSrc q (32 * n)) :=
  (assign q n c2 hb w4 hc2 hhb hw4 hq64 hq).mono (by decide)

end Services.Bootstrap.Encode.Enc
