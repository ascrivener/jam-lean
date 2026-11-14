import Services.Bootstrap.Encode.VariantsVec2
import Services.Bootstrap.Encode.VariantsVec2GasSegs
import Services.Bootstrap.Decode.AssignGas

/-!
# `Instruction::encode_to`: `AssignForGasCost` (dispatch index 24)

`AssignForGasCost { core: u16, queue: Vec<Hash>, assigner: u32 }` holds the discriminant 2^63 + 23,
the queue `{cap n, ptr q, len n}` at S + 8, the assigner's 4 octets g at S + 32 and the core's 2
octets c at S + 36; the queue's n hashes are the 32 n octets hs at q (as `Decode.AssignGas` writes it:
`AssignGasRep`, here with q explicit, `AssignGasRepAt`; `assignGasRep_iff` is the bridge). The arm
(18639) appends 24, c, ℰ(n), then each hash in a loop (18722 … 18749, one 32-octet call each, straight
from the heap), then g (GP v0.8.0 Appendix C: the fields in order, the sequence of hashes with its
length prefix): the encoding is 24 :: (c ++ ℰ(n) ++ hs ++ g), the same octets the decoder reads. The
heap octets read are the padded stretch `VecSrc q (32 n)`. The code traps (20397) on n ≥ 2^32.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`AssignForGasCost`'s slot, with the queue's address q**: `AssignGasRep` with its q given. -/
def AssignGasRepAt (q : Nat) (c : List UInt8) (n : Nat) (hs g : List UInt8) (bs : List UInt8) (μ : Memory) :
    Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775831 ∧ (bs.drop 32).take 4 = g ∧ (bs.drop 36).take 2 = c ∧
    (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (32 * n) = hs

/-- The decode side's `AssignGasRep` is `AssignGasRepAt` for some q. -/
theorem assignGasRep_iff (c : List UInt8) (n : Nat) (hs g bs : List UInt8) (μ : Memory) :
    Decode.AssignGas.AssignGasRep c n hs g bs μ ↔ ∃ q, AssignGasRepAt q c n hs g bs μ := by
  constructor
  · rintro ⟨h0, h1, h2, q, h3, h4, h5, h6⟩; exact ⟨q, h0, h1, h2, h3, h4, h5, h6⟩
  · rintro ⟨q, h0, h1, h2, h3, h4, h5, h6⟩; exact ⟨h0, h1, h2, q, h3, h4, h5, h6⟩

/-- `AssignForGasCost`'s output after the tag, the core, the count and the first k hashes. -/
def preG (c : List UInt8) (n : Nat) (hs : List UInt8) (k : Nat) : List UInt8 :=
  UInt8.ofNat 24 :: (c ++ Blob.encodeNat n ++ hs.take (32 * k))

theorem preG_len (c : List UInt8) (n : Nat) (hs : List UInt8) (k : Nat) (hk : 32 * k ≤ hs.length) :
    (preG c n hs k).length = 1 + c.length + (Blob.encodeNat n).length + 32 * k := by
  simp [preG, List.length_take] <;> omega

/-- The first k + 1 hashes are the first k and the 32 octets at q + 32 k. -/
theorem hs_chunk (μ : Memory) (q n : Nat) (hs : List UInt8) (h : μ.readN q (32 * n) = hs) (k : Nat)
    (hk : k < n) : hs.take (32 * (k + 1)) = hs.take (32 * k) ++ μ.readN (q + 32 * k) 32 := by
  subst h
  rw [readN_take μ q (32 * n) (32 * (k + 1)) (by omega), readN_take μ q (32 * n) (32 * k) (by omega),
    show 32 * (k + 1) = 32 * k + 32 by omega, readN_add']

theorem preG_succ (μ : Memory) (q : Nat) (c : List UInt8) (n : Nat) (hs : List UInt8)
    (h : μ.readN q (32 * n) = hs) (k : Nat) (hk : k < n) :
    preG c n hs (k + 1) = preG c n hs k ++ μ.readN (q + 32 * k) 32 := by
  simp [preG, hs_chunk μ q n hs h k hk]

theorem preG_all (c : List UInt8) (n : Nat) (hs g : List UInt8) (hh : hs.length = 32 * n) :
    preG c n hs n ++ g = (24 :: (c ++ Blob.encodeNat n ++ hs ++ g) : List UInt8) := by
  simp [preG, ← hh] <;> rfl

/-- **`AssignForGasCost`'s hash loop** (18722 … 18749): from the loop's head for hash k (ω₆ = q + 32 k,
    ω₅ = 32 i, the octets of the i = n − k > 0 hashes left) in `StD (preG k)` with S at sp, the loop
    appends the hashes k … n − 1 and reaches the assigner's piece at 18752 in `StD (preG n)`, S kept at
    sp. -/
theorem gas_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    (μ : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} (q : Nat) (c : List UInt8) (n : Nat)
    (hs : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n)
    (L : LayD P D F S v cap ptr len N ret t μ) (hD : 136 ≤ D)
    (hNk : (preG c n hs n).length ≤ N)
    (hsrc : ∀ a, VecSrc q (32 * n) a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + N ≤ a) ∧ (a < v ∨ v + 24 ≤ a))
    (rh : μ.readN q (32 * n) = hs) (hq : 0 < n → 65536 ≤ q) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StD D F v ptr len ret r5 r6 μ (preG c n hs k) ω μ1 → ω[5] = UInt64.ofNat (32 * i) →
      ω[6] = UInt64.ofNat (q + 32 * k) → μ1.readN (F - 56) 8 = Num.encodeLE 8 S →
      ∃ ω' μ', FreeStepsH p R 18722 ω μ1 x 18752 ω' μ' x (2000 * (N - (preG c n hs k).length)) ∧
        StD D F v ptr len ret r5 r6 μ (preG c n hs n) ω' μ' ∧ μ'.readN (F - 56) 8 = Num.encodeLE 8 S := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hd := L.hd
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 hS0
    have hk : k < n := by omega
    have hlk := preG_len c n hs k (by omega)
    have hln := preG_len c n hs n (by omega)
    have hq' := hq (by omega)
    -- the hash's octets lie in the padded stretch
    have hs' := fun a (h1 : q ≤ a + 24) (h2 : a < q + 32 * n + 24) => hsrc a ⟨by omega, h1, h2⟩
    have hlo : q - 24 < q + 32 * n + 24 := by omega
    have s1 := side (X := F - D) (Y := F) (by omega) hlo (fun a h1 h2 => (hs' a (by omega) h2).2.2.1)
    have s2 := side (X := ptr + len) (Y := ptr + len + N) (by have := L.hd; omega) hlo
      (fun a h1 h2 => (hs' a (by omega) h2).2.2.2.1)
    have s3 := (hs' (q + 32 * n + 23) (by omega) (by omega)).1
    -- the hash's address to sp + 8 and the call
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bm, bfr, brd, bwr⟩ := seg_18722 (p := p) (P := P)
      (R := R) x ω μ1 (F - 56) v (q + 32 * k) (by omega) (by omega) (by omega) st.h1 h6
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
    have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
    have kq : ∀ a, q + 32 * k ≤ a → a < q + 32 * k + 32 → μ2.read a = μ.read a := fun a h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hs' a (by omega) (by omega)
      rw [bfr a a0 (by omega)]
      exact st.keep a a0 a2 (by omega) (by omega)
    obtain ⟨ω3, μ3, run3, st3, c5, c6, kF⟩ := ext_stepD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2
      (q + 32 * k) 32 776 18743 b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_387 bs_18743 (by omega)
      ⟨by omega, by omega⟩ (by omega) (by omega)
      (fun a h1 h2 => by rw [brd, st.rd]; exact (hs' a (by omega) (by omega)).2.1)
    rw [Memory.readN_congr (fun j hj => kq _ (by omega) (by omega)), ← preG_succ μ q c n hs rh k hk] at st3
    have m8 : μ3.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 32 * k + 32) := by
      rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact bm
    have m0 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
      rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hS0
    have h5' : ω3[5] = UInt64.ofNat (32 * (i + 1)) := by rw [c5, b5, h5]
    have hlk1 := preG_len c n hs (k + 1) (by omega)
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · obtain ⟨ω4, run4, d1⟩ := seg_18743_last (p := p) (P := P) (R := R) x ω3 μ3 (F - 56) (q + 32 * k + 32)
        (by omega) (by omega) st3.h1 (by rw [h5']) m8
        (fun a h1 h2 => by rw [st3.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      have hkn : k + 1 = n := by omega
      refine ⟨ω4, μ3, (run2.trans (run3.trans run4)).mono ?_,
        StD.cast (by rw [hkn])
          ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.sv, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩, m0⟩
      omega
    · obtain ⟨ω4, run4, d1, d5, d6⟩ := seg_18743_more (p := p) (P := P) (R := R) x ω3 μ3 (F - 56)
        (q + 32 * k + 32) (32 * (i + 1)) (by omega) (by omega) ⟨by omega, by omega⟩ st3.h1 h5' m8
        (fun a h1 h2 => by rw [st3.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
      obtain ⟨ω5, μ5, run5, st5, m5⟩ := ih (k + 1) ω4 μ3 (by omega) hi
        ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.sv, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩
        (by rw [d5, show 32 * (i + 1) - 32 = 32 * i by omega])
        (by rw [d6, show q + 32 * k + 32 = q + 32 * (k + 1) by omega]) m0
      refine ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono ?_, st5, m5⟩
      omega

/-- **`AssignForGasCost`'s end** (18752 … 18774, then the call): the assigner's 4 octets g (S + 32, S at
    sp) appended, at 20383. -/
theorem gas_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ μ1 : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (g : List UInt8)
    (hg : g.length = 4) (L : LayD P D F S v cap ptr len N ret t μ) (hD : 136 ≤ D)
    (st : StD D F v ptr len ret r5 r6 μ pre ω μ1) (hN : pre.length + 4 ≤ N)
    (hS0 : μ1.readN (F - 56) 8 = Num.encodeLE 8 S) (c32 : μ.readN (S + 32) 4 = g) :
    ∃ ω' μ', FreeStepsH p R 18752 ω μ1 x 20383 ω' μ' x 400 ∧
      StD D F v ptr len ret r5 r6 μ (pre ++ g) ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS := L.hS; have hS' := L.hS'
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18752g (p := p) (P := P) (R := R)
    x ω μ1 (F - 56) v S (by omega) (by omega) (by omega) st.h1 hS0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => by rw [st.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st.scratch L hD (by omega) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rw [st.slot L (by omega) 32 4 (by decide), c32] at bt
  obtain ⟨ω3, μ3, run3, st3, _, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L hD st2 g 4 918 20383
    hg (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_458 bs_20383 (by omega) bt
  exact ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3⟩

/-- **`AssignForGasCost { core, queue, assigner }`** (tag 24): a value holding the discriminant
    2^63 + 23, the queue `{cap n, ptr q, len n}` at S + 8 whose 32 n octets at q are the hashes hs, the
    assigner's 4 octets g at S + 32 and the core's 2 octets c at S + 36 (`AssignGasRepAt`), n < 2^32,
    encodes to 24 :: (c ++ ℰ(n) ++ hs ++ g) (GP v0.8.0 Appendix C), reading the heap octets
    `VecSrc q (32 n)`. -/
theorem assign_gas {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (c : List UInt8) (n : Nat) (hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n)
    (hg : g.length = 4) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 192 (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)) (AssignGasRepAt q c n hs g)
      (VecSrc q (32 * n)) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r32, r36, -, r16, r24, rh⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 24) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have c32 : μ.readN (S + 32) 4 = g := by rw [← slot_take μ S 32 4 (by decide)]; exact r32
  have c36 : μ.readN (S + 36) 2 = c := by rw [← slot_take μ S 36 2 (by decide)]; exact r36
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hE := encodeNat_pos n
  have hN : (24 :: (c ++ Blob.encodeNat n ++ hs ++ g) : List UInt8).length =
      7 + (Blob.encodeNat n).length + 32 * n := by simp [hc, hh, hg] <;> omega
  have hln := preG_len c n hs n (by omega)
  have hl0 := preG_len c n hs 0 (by omega)
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD2 (p := p) (P := P) (R := R) x ω μ L (by decide) 24
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 24 = 18639 from rfl] at run1
  -- the tag, and S to sp
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bS, bfr, brd, bwr⟩ := seg_18639 (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, _, cF⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 24] 1 770 18662 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_384 bs_18662
    (by simp [hc, hh, hg] <;> omega) bt
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact bS
  -- the core
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d7, d8, d9, dc, dfr, drd, dwr⟩ := seg_18662 (p := p) (P := P) (R := R)
    x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5]) m3
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp [hc, hh, hg] <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rw [st3.slot L (by simp [hc, hh, hg] <;> omega) 36 2 (by decide), c36] at dc
  have m4 : μ4.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega))]; exact m3
  obtain ⟨ω5, μ5, run5, st5, _, _, eF⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    c 2 772 18685 hc (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_385 bs_18685
    (by simp [hc, hh, hg] <;> omega) dc
  have m5 : μ5.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact m4
  -- the queue's count
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, fn, ffr, frd, fwr⟩ := seg_18685 (p := p) (P := P) (R := R)
    x ω5 μ5 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st5.h1 m5
    (by rw [st5.slot L (by simp [hc, hh, hg] <;> omega) 16 8 (by decide)]; exact c16)
    (by rw [st5.slot L (by simp [hc, hh, hg] <;> omega) 24 8 (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
    (fun a h1 h2 => by rw [st5.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st5.wr]; exact L.hwF a (by omega) (by omega))
  have st6 := st5.scratch L (by decide) (by simp [hc, hh, hg] <;> omega) f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  have m6 : μ6.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact m5
  obtain ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ := prefixD (p := p) (P := P) (R := R) x ω6 μ6 μ L (by decide) st6 n 774
    18715 f0 (by rw [f7]; congr 1; omega) f8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact fn)
    ⟨by decide, by decide, by decide⟩ jte_386 bs_18715 (by simp [hc, hh, hg] <;> omega)
  have st7' := st7.cast (show [] ++ [UInt8.ofNat 24] ++ c ++ Blob.encodeNat n = preG c n hs 0 by simp [preG])
  have m7 : μ7.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => gF _ (by omega) (by omega))]; exact m6
  have henc := preG_all c n hs g hh
  have L' := L; rw [← henc] at L'
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no hashes
    subst hn0
    obtain ⟨ω8, run8, e8⟩ := seg_18715_zero (p := p) (P := P) (R := R) x ω7 μ7 (by rw [g5, f5])
    rw [← e8] at st7'
    obtain ⟨ω9, μ9, run9, st9⟩ := gas_tail (p := p) (P := P) (R := R) x ω8 μ μ7 g hg L' (by decide)
      st7' (by simp [hg]) m7 c32
    exact closeD L (by decide) 20383 _ (by decide) (by rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        run9))))))))
      (st9.cast henc)
  · have hq' := hq hn0
    obtain ⟨ω8, run8, k1, k5, k6⟩ := seg_18715_pos (p := p) (P := P) (R := R) x ω7 μ7 n ⟨hn0, hn⟩
      (by rw [g5, f5])
    obtain ⟨ω9, μ9, run9, st9, m9⟩ := gas_loop (p := p) (P := P) (R := R) x μ q c n hs hc hh L' (by decide)
      (by simp [hg]) (fun a ha => by rw [henc]; exact hsrc a ha) rh hq n 0 ω8 μ7 (by omega) hn0
      ⟨k1.trans st7'.h1, st7'.s0, st7'.s5, st7'.s6, st7'.sv, st7'.vl, st7'.out, st7'.keep, st7'.rd, st7'.wr⟩
      (by rw [k5]) (by rw [k6, g6, f6]; congr 1) m7
    obtain ⟨ω10, μ10, run10, st10⟩ := gas_tail (p := p) (P := P) (R := R) x ω9 μ μ9 g hg L' (by decide) st9
      (by simp [hg]) m9 c32
    have hNN : (preG c n hs n ++ g).length = (24 :: (c ++ Blob.encodeNat n ++ hs ++ g) : List UInt8).length := by
      rw [henc]
    exact closeD L (by decide) 20383 _ (by decide) (by omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        (run9.trans run10)))))))))
      (st10.cast henc)

/-- `assign_gas` at the depth 232. -/
theorem assign_gas_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q : Nat) (c : List UInt8) (n : Nat) (hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n)
    (hg : g.length = 4) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 232 (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)) (AssignGasRepAt q c n hs g)
      (VecSrc q (32 * n)) :=
  (assign_gas q c n hs g hc hh hg hn hq64 hq).mono (by decide)

end Services.Bootstrap.Encode.Enc
