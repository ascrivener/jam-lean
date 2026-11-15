import Services.Bootstrap.Encode.VariantsVec3Core
import Services.Bootstrap.Encode.VariantsVec3Segs3
import Services.Bootstrap.Encode.VariantsVecVec
import Services.Bootstrap.Decode.DesignateHeap

/-!
# `Instruction::encode_to`: `Designate` (13)

`Designate { keys }` (dispatch index 13, discriminant word 2^63 + 12) holds the `Vec` `{cap n, ptr q,
len n}` at S + 8 whose 336 n octets at q are the n keys in their in-memory layout, each key rotated
(`Decode.VecKey336.keysRot`: a key's last 128 octets, then its first 208), as `Decode.DesignateHeap`
writes it (`DesignateRep`, here with q explicit: `DesignateRepAt`). The arm (19322) appends 13 and ℰ(n),
then for each key at a its octets [a + 128, a + 160), [a + 160, a + 192), [a + 192, a + 336) and
[a, a + 128): the inverse rotation, so each key goes out in the paper's order (GP v0.8.0 Appendix C; the
validator key of §6.3: Bandersnatch, Ed25519, BLS, metadata). The encoding is 13 :: ℰ(n) ++ ks, exactly
the octets `Decode.Designate.designate_elem` decodes. The code checks n only against 2^32 (a trap,
19351 → 20397), not against 3·𝖢 (the decoder's bound, quirk Q16). The heap octets `Src` are the padded
stretch `VecSrc q (336 n)`.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.VecKey336

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Designate`'s slot, with the keys at q**: `Decode.Designate.DesignateRep` with its q given. -/
def DesignateRepAt (q n : Nat) (ks : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775820 ∧
  (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (336 * n) = keysRot n ks

/-- The decode side's `DesignateRep` is `DesignateRepAt` for some q. -/
theorem designateRep_iff (n : Nat) (ks bs : List UInt8) (μ : Memory) :
    Decode.Designate.DesignateRep n ks bs μ ↔ ∃ q, DesignateRepAt q n ks bs μ := by
  constructor
  · rintro ⟨h0, q, h1, h2, h3, h4⟩; exact ⟨q, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, h0, h1, h2, h3, h4⟩; exact ⟨h0, q, h1, h2, h3, h4⟩

theorem keyRot_length (e : List UInt8) : (keyRot e).length = e.length := by
  unfold keyRot; simp; omega

theorem keysRot_length : ∀ n (ks : List UInt8), ks.length = 336 * n → (keysRot n ks).length = 336 * n := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro ks hk
    rw [keysRot, List.length_append, keyRot_length, ih _ (by simp; omega)]
    simp; omega

/-- Key k of the in-memory layout: the 336 octets at q + 336 k are the rotation of the k-th key. -/
theorem keysRot_elem (μ : Memory) : ∀ n q (ks : List UInt8), ks.length = 336 * n →
    μ.readN q (336 * n) = keysRot n ks →
    ∀ k, k < n → μ.readN (q + 336 * k) 336 = keyRot ((ks.drop (336 * k)).take 336) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ k hk; omega
  | succ n ih =>
    intro q ks hk h k hkn
    rw [show 336 * (n + 1) = 336 + 336 * n by omega, Memory.readN_split, keysRot] at h
    have hl : (μ.readN q 336).length = (keyRot (ks.take 336)).length := by
      rw [keyRot_length]; simp; omega
    obtain ⟨h1, h2⟩ := List.append_inj h hl
    rcases k with _ | k
    · simpa using h1
    · have := ih (q + 336) (ks.drop 336) (by simp; omega) h2 k (by omega)
      rw [show q + 336 + 336 * k = q + 336 * (k + 1) by omega, List.drop_drop,
        show 336 + 336 * k = 336 * (k + 1) by omega] at this
      exact this

/-- A key at a in its in-memory layout, read in the encoder's four pieces, is the key. -/
theorem keyRot_parts (μ : Memory) (a : Nat) (key : List UInt8) (hk : key.length = 336)
    (h : μ.readN a 336 = keyRot key) :
    μ.readN (a + 128) 32 ++ μ.readN (a + 160) 32 ++ μ.readN (a + 192) 144 ++ μ.readN a 128 = key := by
  rw [show (336 : Nat) = 128 + 208 from rfl, Memory.readN_split] at h
  unfold keyRot at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp; omega)
  have h3 : μ.readN (a + 128) 208 = μ.readN (a + 128) 32 ++ μ.readN (a + 160) 32 ++ μ.readN (a + 192) 144 := by
    rw [show (208 : Nat) = 32 + (32 + 144) from rfl, Memory.readN_split, Memory.readN_split,
      show a + 128 + 32 = a + 160 by omega, show a + 160 + 32 = a + 192 by omega, List.append_assoc]
  rw [← h3, h1, h2, List.take_append_drop]

theorem take336_succ (ks : List UInt8) (k : Nat) :
    ks.take (336 * (k + 1)) = ks.take (336 * k) ++ (ks.drop (336 * k)).take 336 := by
  rw [show 336 * (k + 1) = 336 * k + 336 by omega, List.take_add]

/-- **`Designate`'s key loop** (19385 … 19467): from the loop's head for key k (ω₆ = q + 336 k, ω₇ =
    336 i with i = n − k > 0 keys left, the writer in ω₅) in `StD (pre0 ++ ks.take (336 k))`, the loop
    appends each key in the paper's order and reaches the end at 20118 in `StD (pre0 ++ ks)`. -/
theorem designate_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    (μ : Memory) {D F S v cap ptr len ret t r5 r6 : Nat} (q n : Nat) (pre0 ks : List UInt8)
    (hks : ks.length = 336 * n)
    (L : LayD P D F S v cap ptr len (pre0 ++ ks).length ret t μ) (hD : 136 ≤ D) (hq : 65536 ≤ q)
    (hsrc : ∀ a, VecSrc q (336 * n) a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + (pre0 ++ ks).length ≤ a) ∧ (a < v ∨ v + 24 ≤ a))
    (hkeys : μ.readN q (336 * n) = keysRot n ks) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StD D F v ptr len ret r5 r6 μ (pre0 ++ ks.take (336 * k)) ω μ1 →
      ω[5] = UInt64.ofNat v → ω[6] = UInt64.ofNat (q + 336 * k) → ω[7] = UInt64.ofNat (336 * i) →
      ∃ ω' μ', FreeStepsH p R 19385 ω μ1 x 20118 ω' μ' x (2000 * (336 * i)) ∧
        StD D F v ptr len ret r5 r6 μ (pre0 ++ ks) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 h7
    have hk : k < n := by omega
    have hqn := (hsrc (q + 336 * n + 23) ⟨by omega, by omega, by omega⟩).1
    have hlenk : (ks.take (336 * k)).length = 336 * k := by simp [hks]; omega
    have hNl : (pre0 ++ ks).length = pre0.length + 336 * n := by simp [hks]
    have hsrc' := fun b h1 h2 => hsrc b ⟨by omega, h1, h2⟩
    have hkey := keysRot_elem μ n q ks hks hkeys k hk
    have hkl : ((ks.drop (336 * k)).take 336).length = 336 := by simp [hks]; omega
    -- the first piece
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bs0, bs8, bfr, brd, bwr⟩ := seg_19385 (p := p) (P := P)
      (R := R) x ω μ1 (F - 56) v (q + 336 * k) (336 * (i + 1)) (by omega) (by omega) (by omega) (by omega)
      st.h1 h5 h6 h7 (fun b h1 h2 => by rw [st.wr]; exact L.hwF b (by omega) (by omega))
    have st2 := st.scratch L hD (by simp [hlenk, hNl]; omega) b1 (fun b h0 h1 => bfr b h0 (by omega)) brd bwr
    obtain ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ := ext_srcD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2
      (q + 336 * k + 128) 32 840 19410 q (q + 336 * n) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩
      jte_419 bs_19410 (by simp [hlenk]; omega) (by decide) ⟨by omega, by omega⟩ hq hsrc'
    -- the second
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := seg_keyD (p := p) (P := P) (R := R) x ω3 μ3 19410 842 160
      32 v (q + 336 * k) (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by omega) (by omega) (by rw [c5, b5, h5])
      (by rw [c6, b6, h6])
    obtain ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ := ext_srcD (p := p) (P := P) (R := R) x ω4 μ3 μ L hD
      ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.sv, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩
      (q + 336 * k + 160) 32 842 19426 q (q + 336 * n) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩
      jte_420 bs_19426 (by simp [hlenk]; omega) (by decide) ⟨by omega, by omega⟩ hq hsrc'
    -- the third
    obtain ⟨ω6, run6, f0, f1, f5, f6, f7, f8, f9⟩ := seg_keyD (p := p) (P := P) (R := R) x ω5 μ5 19426 844 192
      144 v (q + 336 * k) (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by omega) (by omega)
      (by rw [e5, d5, c5, b5, h5]) (by rw [e6, d6, c6, b6, h6])
    obtain ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ := ext_srcD (p := p) (P := P) (R := R) x ω6 μ5 μ L hD
      ⟨f1.trans st5.h1, st5.s0, st5.s5, st5.s6, st5.sv, st5.vl, st5.out, st5.keep, st5.rd, st5.wr⟩
      (q + 336 * k + 192) 144 844 19443 q (q + 336 * n) f0 f7 f8 f9 ⟨by decide, by decide, by decide⟩
      jte_421 bs_19443 (by simp [hlenk]; omega) (by decide) ⟨by omega, by omega⟩ hq hsrc'
    -- the fourth
    obtain ⟨ω8, run8, k0, k1, k5, k6, k7, k8, k9⟩ := seg_keyD (p := p) (P := P) (R := R) x ω7 μ7 19443 846 0
      128 v (q + 336 * k) (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)) (by omega) (by omega)
      (by rw [g5, f5, e5, d5, c5, b5, h5]) (by rw [g6, f6, e6, d6, c6, b6, h6])
    rw [Nat.add_zero] at k8
    obtain ⟨ω9, μ9, run9, st9, m5, m6, mF⟩ := ext_srcD (p := p) (P := P) (R := R) x ω8 μ7 μ L hD
      ⟨k1.trans st7.h1, st7.s0, st7.s5, st7.s6, st7.sv, st7.vl, st7.out, st7.keep, st7.rd, st7.wr⟩
      (q + 336 * k) 128 846 19458 q (q + 336 * n) k0 k7 k8 k9 ⟨by decide, by decide, by decide⟩
      jte_422 bs_19458 (by simp [hlenk]; omega) (by decide) ⟨by omega, by omega⟩ hq hsrc'
    have st9' := st9.cast (show pre0 ++ ks.take (336 * k) ++ μ.readN (q + 336 * k + 128) 32 ++
        μ.readN (q + 336 * k + 160) 32 ++ μ.readN (q + 336 * k + 192) 144 ++ μ.readN (q + 336 * k) 128 =
        pre0 ++ ks.take (336 * (k + 1)) by
      rw [take336_succ, ← keyRot_parts μ (q + 336 * k) _ hkl hkey]; simp [List.append_assoc])
    have fr : ∀ b, F - 56 ≤ b → b < F → μ9.read b = μ2.read b := fun b h1 h2 => by
      rw [mF b h1 h2, gF b h1 h2, eF b h1 h2, cF b h1 h2]
    have s0' : μ9.readN (F - 56) 8 = Num.encodeLE 8 (q + 336 * k + 336) := by
      rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega))]; exact bs0
    have s8' : μ9.readN (F - 56 + 8) 8 = Num.encodeLE 8 (336 * (i + 1)) := by
      rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega))]; exact bs8
    have hrd : ∀ c, F - 56 ≤ c → c < F - 56 + 16 → μ9.readable c = true := fun c h1 h2 => by
      rw [st9'.rd]; exact Memory.readable_of_writable (L.hwF c (by omega) (by omega))
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω10, run10, n1⟩ := seg_19458_last (p := p) (P := P) (R := R) x ω9 μ9 (F - 56) (q + 336 * k + 336)
        (by omega) (by omega) st9'.h1 s0' s8' hrd
      have hkn : 336 * (k + 1) = ks.length := by omega
      refine ⟨ω10, μ9, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        (run9.trans run10)))))))).mono (by omega),
        StD.cast (by rw [hkn, List.take_length])
          ⟨n1.trans st9'.h1, st9'.s0, st9'.s5, st9'.s6, st9'.sv, st9'.vl, st9'.out, st9'.keep, st9'.rd,
            st9'.wr⟩⟩
    · obtain ⟨ω10, run10, n1, n5, n6, n7⟩ := seg_19458_more (p := p) (P := P) (R := R) x ω9 μ9 (F - 56)
        (336 * (i + 1)) (q + 336 * k + 336) (by omega) ⟨by omega, by omega⟩ (by omega) st9'.h1 s0' s8' hrd
      obtain ⟨ω11, μ11, run11, st11⟩ := ih (k + 1) ω10 μ9 (by omega) hi0
        ⟨n1.trans st9'.h1, st9'.s0, st9'.s5, st9'.s6, st9'.sv, st9'.vl, st9'.out, st9'.keep, st9'.rd, st9'.wr⟩
        (by rw [n5, m5, k5, g5, f5, e5, d5, c5, b5, h5]) (by rw [n6]; congr 1)
        (by rw [n7]; congr 1)
      exact ⟨ω11, μ11, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        (run9.trans (run10.trans run11))))))))).mono (by omega), st11⟩

/-- **`Designate`** (dispatch index 13): a value holding the discriminant 2^63 + 12 and the `Vec`
    `{cap n, ptr q, len n}` at S + 8 whose 336 n octets at q are the keys ks in their in-memory layout
    (`keysRot`, `DesignateRepAt`), n < 2^32, encodes to 13 :: ℰ(n) ++ ks (GP v0.8.0 Appendix C, the keys
    in the paper's order), reading the heap octets `VecSrc q (336 n)`. The callee frames reach F − 192
    (the length prefix). -/
theorem designate {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (ks : List UInt8) (hks : ks.length = 336 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 192 (13 :: (Blob.encodeNat n ++ ks)) (DesignateRepAt q n ks) (VecSrc q (336 * n)) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rkeys⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 13) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hE := encodeNat_pos n
  have hN : (13 :: (Blob.encodeNat n ++ ks) : List UInt8).length = 1 + (Blob.encodeNat n).length + 336 * n := by
    simp [hks]; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD (p := p) (P := P) (R := R) x ω μ L (by decide) 13
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 13 = 19322 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19322 (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 13] 1 836 19343 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_417
    bs_19343 (by simp <;> omega) bt
  -- the length prefix
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dn, dfr, drd, dwr⟩ := seg_19343 (p := p) (P := P) (R := R)
    x ω3 μ3 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st3.h1 (by rw [c5, b5])
    (by rw [st3.slot L (by simp <;> omega) 16 8 (by decide)]; exact c16)
    (by rw [st3.slot L (by simp <;> omega) 24 8 (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, _⟩ := prefixD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    n 838 19373 d0 (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
    ⟨by decide, by decide, by decide⟩ jte_418 bs_19373 (by simp <;> omega)
  have hpre : ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n : List UInt8).length =
      1 + (Blob.encodeNat n).length := by simp <;> omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no keys
    subst hn0
    have hk0 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hk0
    obtain ⟨ω6, run6, rfl⟩ := seg_19373_zero (p := p) (P := P) (R := R) x ω5 μ5 (by rw [e5, d5])
    exact closeD L (by decide) 20118 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) (st5.cast (by simp))
  · have hq' := hq hn0
    have hqn := (hsrc (q + 336 * n + 23) ⟨by omega, by omega, by omega⟩).1
    obtain ⟨ω6, run6, f1, f5, f6, f7⟩ := seg_19373_pos (p := p) (P := P) (R := R) x ω5 μ5 (F - 56) v n
      (by omega) (by omega) ⟨hn0, by omega⟩ st5.h1 (by rw [e5, d5])
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
      (fun a h1 h2 => by rw [st5.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    have henc : (13 :: (Blob.encodeNat n ++ ks) : List UInt8) = ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n) ++ ks := by
      simp only [List.nil_append, List.cons_append] <;> rfl
    have L' := L; rw [henc] at L'
    obtain ⟨ω7, μ7, run7, st7⟩ := designate_loop (p := p) (P := P) (R := R) x μ q n
      ([] ++ [UInt8.ofNat 13] ++ Blob.encodeNat n) ks hks L' (by decide) hq'
      (fun a ha => by rw [← henc]; exact hsrc a ha) rkeys n 0 ω6 μ5 (by omega) hn0
      (StD.cast (by simp)
        ⟨f1.trans st5.h1, st5.s0, st5.s5, st5.s6, st5.sv, st5.vl, st5.out, st5.keep, st5.rd, st5.wr⟩)
      f5 (by rw [f6, e6, d6]; congr 1) f7
    exact closeD L (by decide) 20118 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
      (st7.cast henc.symm)

/-- `designate` at the depth 232. -/
theorem designate_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (ks : List UInt8) (hks : ks.length = 336 * n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 232 (13 :: (Blob.encodeNat n ++ ks)) (DesignateRepAt q n ks) (VecSrc q (336 * n)) :=
  (designate q n ks hks hn hq64 hq).mono (by decide)

end Services.Bootstrap.Encode.Enc
