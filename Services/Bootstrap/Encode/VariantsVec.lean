import Services.Bootstrap.Encode.VecCore
import Services.Bootstrap.Encode.VecSegs3
import Services.Bootstrap.Encode.Fixed
import Services.Bootstrap.Decode.LookupProvideElem

/-!
# `Instruction::encode_to`: `LookedUp` (18) and `Provide { Hash }` (17)

* `looked_up_some`: `LookedUp { data: Some(bytes) }`, its slot as `Decode.LookupProvideElem` writes it
  (`LookedUpSomeRep`, here with the heap address q of the octets explicit: `LookedUpSomeRepAt`), encodes
  to 18 :: 1 :: ℰ(n) ++ bytes (GP v0.8.0 Appendix C: the `Option` tag, then the sequence with its length
  prefix), n = |bytes| < 2^32. The heap octets `Src` are the padded stretch [q − 24, q + n + 24)
  (`VecSrc`; `HeapPad.pad_readable` gives their readability from the allocator's context). The arm
  calls the length prefix from its frame, so it is an `EncOkMD 192` element.
* `looked_up_none`: `LookedUp { data: None }` (the `None` niche 2^64 − 1 at S + 8) encodes to [18, 0]
  (`EncOkMD 136`).
* `provide_hash`: `Provide { service, preimage: Hash(h) }` encodes to 17 :: s ++ 0 :: h (`EncOk`).

Each is lifted to `EncOkMD 232` (`*_232`), the depth `EncMD.LayLMD` asks.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD Services.Bootstrap.Encode.EncM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The heap octets of a `Vec` of n octets at q**: for n > 0, the stretch [q − 24, q + n + 24) (the
    octets and the 24 on each side that `Vec<u8>::extend_from_slice`'s copy is proved apart from); none
    for n = 0. -/
def VecSrc (q n : Nat) (a : Nat) : Prop := 0 < n ∧ q ≤ a + 24 ∧ a < q + n + 24

/-- **`LookedUp { data: Some(bytes) }`'s slot, with the octets at q**: `LookedUpSomeRep` with its q
    given. -/
def LookedUpSomeRepAt (q n : Nat) (bytes : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 n ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes

/-- The decode side's `LookedUpSomeRep` is `LookedUpSomeRepAt` for some q. -/
theorem lookedUpSomeRep_iff (n : Nat) (bytes bs : List UInt8) (μ : Memory) :
    Decode.LookupProvideElem.LookedUpSomeRep n bytes bs μ ↔ ∃ q, LookedUpSomeRepAt q n bytes bs μ := by
  constructor
  · rintro ⟨h0, q, h1, h2, h3, h4⟩; exact ⟨q, h0, h1, h2, h3, h4⟩
  · rintro ⟨q, h0, h1, h2, h3, h4⟩; exact ⟨h0, q, h1, h2, h3, h4⟩

/-- A piece from the scratch word: the call of `Vec<u8>::extend_from_slice` (58508, returning to e) for
    k ≤ 8 octets `bs` at F − 32: `StD pre` becomes `StD (pre ++ bs)`. -/
theorem scratchD {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (bs : List UInt8) (k r e : Nat)
    (hk : bs.length = k) (hk8 : k ≤ 8)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat (F - 56 + 24))
    (h9 : ω[9] = UInt64.ofNat k) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hn : pre.length + k ≤ N) (hbs : μ.readN (F - 56 + 24) k = bs) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x (7 * k + 360) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ bs) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hdF := L.hdF
  obtain ⟨ω', μ', run, st', c5, c6, kF⟩ := ext_stepD (p := p) (P := P) (R := R) x ω μ μ0 L hD st (F - 56 + 24)
    k r e h0 h7 h8 h9 hr hje hbe hn ⟨by omega, by omega⟩ (by omega) (Or.inl (by omega))
    (fun a h1 h2 => by rw [st.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
  rw [hbs] at st'
  exact ⟨ω', μ', run, st', c5, c6, kF⟩

/-- **`LookedUp { data: None }`** (tag 18): a value holding the discriminant 2^63 + 17 and the `None`
    niche 2^64 − 1 at S + 8 (as `Decode.LookupProvideElem.looked_up_noneF` writes it) encodes to [18, 0]. -/
theorem looked_up_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] :
    EncOkMD p P 136 [18, 0] (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
      (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615) (fun _ => False) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt _
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 18) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 18446744073709551615 := by
    rw [← slot_take μ S 8 8 (by decide)]; exact rep.2
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hN : ([18, 0] : List UInt8).length = 2 := rfl
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startV (p := p) (P := P) (R := R) x ω μ L (by decide) 18
    (Or.inl rfl) h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 18 = 19538 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19538 (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 18] 1 856 19559 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_427 bs_19559
    (by simp [hN] <;> omega) bt
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19559_none (p := p) (P := P)
    (R := R) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5, a5]) (by rw [c6, b6])
    (by rw [st3.slot L (by simp [hN] <;> omega) 8 8 (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp [hN] <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, _, _, _⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    [UInt8.ofNat 0] 1 918 20383 rfl (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_458 bs_20383
    (by simp [hN] <;> omega) dt
  exact closeD L (by decide) 20383 _ (by decide) (by simp)
    (run1.trans (run2.trans (run3.trans (run4.trans run5)))) (st5.cast rfl)

/-- `looked_up_none` at the depth 232. -/
theorem looked_up_none_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] :
    EncOkMD p P 232 [18, 0] (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
      (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615) (fun _ => False) :=
  looked_up_none.mono (by decide)


/-- **`LookedUp { data: Some(bytes) }`** (tag 18): a value holding the discriminant 2^63 + 17 and the
    `Vec` `{cap n, ptr q, len n}` at S + 8 whose n < 2^32 octets at q are `bytes` (`LookedUpSomeRepAt`)
    encodes to 18 :: 1 :: ℰ(n) ++ bytes (GP v0.8.0 Appendix C), reading the heap octets `VecSrc q n`.
    The `Vec`'s length is checked against 2^32 by the code (a trap otherwise), hence n < 2^32. -/
theorem looked_up_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 192 (18 :: 1 :: (Blob.encodeNat n ++ bytes)) (LookedUpSomeRepAt q n bytes) (VecSrc q n) := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rb⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 18) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  have hN : (18 :: 1 :: (Blob.encodeNat n ++ bytes) : List UInt8).length = 2 + (Blob.encodeNat n).length + n := by
    simp [hbn] <;> omega
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startV (p := p) (P := P) (R := R) x ω μ L (by decide) 18
    (Or.inl rfl) h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 18 = 19538 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19538 (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by decide) (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω2 μ2 μ L (by decide) st2
    [UInt8.ofNat 18] 1 856 19559 rfl (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_427 bs_19559
    (by simp [hN] <;> omega) bt
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19559_some (p := p) (P := P)
    (R := R) x ω3 μ3 (F - 56) v S n (by omega) (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5, a5])
    (by rw [c6, b6])
    (by rw [st3.slot L (by simp [hN] <;> omega) 8 8 (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by decide) (by simp [hN] <;> omega) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, _⟩ := scratchD (p := p) (P := P) (R := R) x ω4 μ4 μ L (by decide) st4
    [UInt8.ofNat 1] 1 858 19586 rfl (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_428 bs_19586
    (by simp [hN] <;> omega) dt
  -- the length prefix
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, fq, fn, fv, ffr, frd, fwr⟩ := seg_19586 (p := p) (P := P)
    (R := R) x ω5 μ5 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st5.h1
    (by rw [e6, d6, c6, b6])
    (by rw [st5.slot L (by simp [hN] <;> omega) 16 8 (by decide)]; exact c16)
    (by rw [st5.slot L (by simp [hN] <;> omega) 24 8 (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
    (fun a h1 h2 => by rw [st5.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st5.wr]; exact L.hwF a (by omega) (by omega))
  have st6 := st5.scratch L (by decide) (by simp [hN] <;> omega) f1 (fun a h0 h1 => ffr a h0 (by omega) (by omega)) frd fwr
  obtain ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ := prefixD (p := p) (P := P) (R := R) x ω6 μ6 μ L (by decide) st6 n 860
    19622 f0 (by rw [f7]; congr 1; omega) f8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact fn)
    ⟨by decide, by decide, by decide⟩ jte_429 bs_19622 (by simp [hN] <;> omega)
  -- the octets
  obtain ⟨ω8, run8, h80, h81, h85, h86, h87, h88, h89⟩ := seg_19622 (p := p) (P := P) (R := R) x ω7 μ7 (F - 56)
    v q n (by omega) hq64 (by omega) (by omega) st7.h1 (by rw [g5, f5]) (by rw [g6, f6])
    (by rw [Memory.readN_congr (fun j hj => gF _ (by omega) (by omega))]; exact fq)
    (fun a h1 h2 => by rw [st7.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
  have henc : (18 :: 1 :: (Blob.encodeNat n ++ bytes) : List UInt8) =
      ([] ++ [UInt8.ofNat 18] ++ [UInt8.ofNat 1] ++ Blob.encodeNat n) ++ bytes ++ [] := by
    simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc, List.append_nil] <;> rfl
  have L' := L; rw [henc] at L'
  obtain ⟨ω9, μ9, run9, st9, _, _, _⟩ := heapD (p := p) (P := P) (R := R) x ω8 μ7 μ L' (by decide)
    ⟨h81.trans st7.h1, st7.s0, st7.s5, st7.s6, st7.sv, st7.vl, st7.out, st7.keep, st7.rd, st7.wr⟩ q n 862
    19636 hbn rb h80 h87 h88 h89 ⟨by decide, by decide, by decide⟩ jte_430 bs_19636 hq
    (fun a ha => by rw [← henc]; exact hsrc a ha)
  exact closeD L (by decide) 19636 _ (by decide) (by rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9))))))))
    (st9.cast (by rw [henc]; simp))

/-- `looked_up_some` at the depth 232. -/
theorem looked_up_some_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) (hq : 0 < n → 65536 ≤ q) :
    EncOkMD p P 232 (18 :: 1 :: (Blob.encodeNat n ++ bytes)) (LookedUpSomeRepAt q n bytes) (VecSrc q n) :=
  (looked_up_some q n bytes hbn hn hq64 hq).mono (by decide)

/-- **`Provide { service, preimage: Hash(h) }`** (tag 17): a value holding the discriminant 2^63 + 16,
    the `Hash` tag 0 at S + 8, h, the 32 octets of the hash, at S + 9 and s, the 4 octets of the
    service, at S + 48 (as `Decode.LookupProvideElem.provide_hashF` writes it) encodes to
    17 :: s ++ 0 :: h. -/
theorem provide_hash {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (s h : List UInt8)
    (hs : s.length = 4) (hh : h.length = 32) :
    EncOk p P (17 :: (s ++ 0 :: h)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧
      (bs.drop 8).take 1 = [0] ∧ (bs.drop 9).take 32 = h ∧ (bs.drop 48).take 4 = s) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hN : (17 :: (s ++ 0 :: h) : List UInt8).length = 38 := by simp [hs, hh]
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 17) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c8 : μ.readN (S + 8) 1 = [0] := by rw [← slot_take μ S 8 1 (by decide)]; exact rep.2.1
  have c9 : μ.readN (S + 9) 32 = h := by rw [← slot_take μ S 9 32 (by decide)]; exact rep.2.2.1
  have c48 : μ.readN (S + 48) 4 = s := by rw [← slot_take μ S 48 4 (by decide)]; exact rep.2.2.2
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hv := L.hv
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 17 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 17 = 18990 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_tag5 (p := p) (P := P) (R := R)
    x ω1 μ1 18990 17 806 (F - 56) v S (Or.inl ⟨rfl, rfl, rfl⟩) (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 (F - 32) 1 806
    19013 b0 b7 (by rw [b8]; congr 1; omega) b9 ⟨by decide, by decide, by decide⟩ jte_402 bs_19013
    (by simp [hs, hh]) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, bt] at st3
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19013 (p := p) (P := P) (R := R)
    x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5]) (by rw [c6, b6])
    (fun a h1 h2 => by rw [st3.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st3.wr]; exact L.hwF a (by omega) (by omega))
  have st4 := st3.scratch L (by simp [hs, hh]) d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  obtain ⟨ω5, μ5, run5, st5, e5, e6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω4 μ4 μ L st4 (F - 32) 4 808
    19034 d0 d7 (by rw [d8]; congr 1; omega) d9 ⟨by decide, by decide, by decide⟩ jte_403 bs_19034
    (by simp [hs, hh]) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, dt, st3.slot L (by simp [hs, hh]) 48 4 (by decide), c48] at st5
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ft, ffr, frd, fwr⟩ := seg_19034_hash (p := p) (P := P)
    (R := R) x ω5 μ5 (F - 56) v S (by omega) (by omega) (by omega) st5.h1 (by rw [e5, d5, c5, b5])
    (by rw [e6, d6, c6, b6])
    (by show Num.decodeLE _ = _; rw [st5.slot L (by simp [hs, hh]) 8 1 (by decide), c8]; rfl)
    (fun a h1 h2 => by rw [st5.rd]; exact L.hrS a (by omega) (by omega))
    (fun a h1 h2 => by rw [st5.wr]; exact L.hwF a (by omega) (by omega))
  have st6 := st5.scratch L (by simp [hs, hh]) f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  obtain ⟨ω7, μ7, run7, st7, g5, g6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω6 μ6 μ L st6 (F - 32) 1 906
    20190 f0 f7 (by rw [f8]; congr 1; omega) f9 ⟨by decide, by decide, by decide⟩ jte_452 bs_20190
    (by simp [hs, hh]) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, ft] at st7
  obtain ⟨ω8, run8, k0, k1, k5, k6, k7, k8, k9⟩ := seg_20190 (p := p) (P := P) (R := R) x ω7 μ7 v (S + 9)
    (by omega) (by omega) (by rw [g5, f5]) (by rw [g6, f6, e6, d6, c6, b6])
  obtain ⟨ω9, μ9, run9, st9, _, _⟩ := ext_step (p := p) (P := P) (R := R) x ω8 μ7 μ L
    ⟨k1.trans st7.h1, st7.s0, st7.s5, st7.s6, st7.vl, st7.out, st7.keep, st7.rd, st7.wr⟩ (S + 9) 32 908 20204
    k0 k7 k8 k9 ⟨by decide, by decide, by decide⟩ jte_453 bs_20204 (by simp [hs, hh])
    (Or.inr ⟨by omega, by omega⟩)
  rw [st7.slot L (by simp [hs, hh]) 9 32 (by decide), c9] at st9
  exact close L 20204 _ (by decide) (by simp [hs, hh])
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9))))))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append, List.append_assoc]; rfl) st9)

/-- `provide_hash` as an `EncOkMD 232` element (it reads no heap octets). -/
theorem provide_hash_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (s h : List UInt8)
    (hs : s.length = 4) (hh : h.length = 32) :
    EncOkMD p P 232 (17 :: (s ++ 0 :: h)) (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧
      (bs.drop 8).take 1 = [0] ∧ (bs.drop 9).take 32 = h ∧ (bs.drop 48).take 4 = s) (fun _ => False) :=
  EncOkM.toMD232 (EncOkM.of_encOk (provide_hash s h hs hh))

end Services.Bootstrap.Encode.Enc
