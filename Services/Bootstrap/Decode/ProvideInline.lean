import Services.Bootstrap.Decode.Provide
import Services.Bootstrap.Decode.LookedUpBig

/-!
# `Instruction::decode`: `Provide { service: u32, preimage: Inline(bytes) }`

Tag 1 of the preimage (`Inline`): `Provide`'s helper (frame H = A − 152, as in `Provide`) keeps the
tag word 1 at H, decodes the length with `decodeU32` and reads the bytes with `read_vec` into a
`Vec` at H + 80; it then moves the `Vec` to H + 23 … H + 47 (with unaligned stores) and stores the
variant as for `Hash`: the `Vec` lands at O + 16.
-/

namespace Services.Bootstrap.Decode.Provide

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem enc_rdN8 (ν : Memory) (a : Nat) : Num.encodeLE 8 (rdN ν a 8 % 18446744073709551616) = ν.readN a 8 := by
  have hlt : rdN ν a 8 < 18446744073709551616 := by
    unfold rdN; have := decodeLE_lt (ν.readN a 8); simpa [Memory.length_readN] using this
  rw [Nat.mod_eq_of_lt hlt]; unfold rdN
  have := encodeLE_decodeLE (ν.readN a 8); rw [Memory.length_readN] at this; exact this

theorem readN_getElem (ν : Memory) (a n k : Nat) (hk : k < n) {h : k < (ν.readN a n).length} :
    (ν.readN a n)[k] = ν.read (a + k) := by
  simp [Memory.readN]

theorem readN_getElem! (ν : Memory) (a n k : Nat) (hk : k < n) : (ν.readN a n)[k]! = ν.read (a + k) := by
  rw [getElem!_pos _ _ (by simp [hk])]; simp [Memory.readN]

/-- 25041 … 25123: the tag read succeeded (ω₇ = 0) and is 1 (`Inline`): the helper keeps the tag
    word 1 at H and calls `decodeU32` on the reader (ω₇ = ω₆, return address 1166). -/
theorem q3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (H + 48) = 1)
    (hw0 : ∀ a, H ≤ a → a < H + 8 → μ.writable a = true)
    (hr : μ.readable (H + 48) = true) :
    ∃ ω' μ', FreeStepsH p R 25041 ω μ x 31894 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1166 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] ∧
      μ'.readN H 8 = Num.encodeLE 8 1 ∧
      (∀ a, a < 4294967296 → (a < H ∨ H + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rb : rdN μ (H + 48) 1 = 1 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hH, hw0, hr, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 25129 … 25147: `decodeU32` returned n (ω₇ = 0, ω₈ = n): the helper calls `read_vec` (3473) for n
    octets from the reader (ω₈ = ω₆ = rd) into the `Vec` slot H + 80 (return address 1168). -/
theorem q4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H rd n : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) (hn : n < 4294967296)
    (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 25129 ω μ x 3473 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 1168 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (H + 80) ∧ ω'[8] = UInt64.ofNat rd ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, h7, h8, hH, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try (congr 1; exact Nat.mod_eq_of_lt hrd)

/-- 25153 … 25208: `read_vec` returned the `Vec` `{cap, ptr q, len n}` at H + 80 (cap not the error
    marker 2⁶⁴ − 1): the helper moves it, with unaligned stores, so that H + 23, H + 31 and H + 39
    hold cap, q and n, and goes on to the variant's store (25209). -/
theorem q5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H cap q n : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H)
    (hcap : cap < 18446744073709551615) (hq : q < 18446744073709551616) (hn : n < 18446744073709551616)
    (s80 : μ.readN (H + 80) 8 = Num.encodeLE 8 cap) (s88 : μ.readN (H + 88) 8 = Num.encodeLE 8 q)
    (s96 : μ.readN (H + 96) 8 = Num.encodeLE 8 n)
    (hw : ∀ a, H + 16 ≤ a → a < H + 128 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 25153 ω μ x 25209 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (H + 23) 8 = Num.encodeLE 8 cap ∧ μ'.readN (H + 31) 8 = Num.encodeLE 8 q ∧
      μ'.readN (H + 39) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < H + 16 ∨ H + 128 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, H + 16 ≤ a → a < H + 128 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hw a h1 h2)
  have rc := rd8 (by omega) s80
  have rq := rd8 hq s88
  have rn := rd8 hn s96
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hH, hw, hr, rc, rq, rn, hcap, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try simp only [enc_rdN8]
    all_goals try (
      apply List.ext_getElem (by simp)
      intro k hk1 hk2
      simp only [Memory.length_readN] at hk1
      rw [readN_getElem _ _ _ _ hk1]
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      all_goals
        simp (disch := first | omega | (simp [two32]; omega)) only [Memory.read_writeN, Num.length_encodeLE,
        Memory.length_readN, Nat.add_sub_add_left, readN_getElem!, Nat.add_assoc, Nat.reduceAdd,
        Nat.add_le_add_iff_left, Nat.add_lt_add_iff_left, Nat.reduceLeDiff, Nat.reduceLT, and_self,
        and_true, true_and, false_and, and_false, ↓reduceIte, Nat.reduceSub, Nat.add_zero, Nat.le_refl,
        getElem!_pos, List.getElem_map])

/-- 25209 … 25272 (as `p5`, for the tag word 1): the helper stores the variant into O: the discriminant word 2^63 + 16, the low
    octet of the tag word at H (1, `Inline`) at O + 8, the hash (H + 16) at O + 9 and the low four octets of the
    word w at H + 8 at O + 48; it restores ω₀, ω₅, ω₆ from H + 144, H + 136, H + 128 and returns to
    982's entry, 21463. -/
theorem p5i {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H O w o6 : Nat) (hH : H + 152 < 4294967296) (hO : O + 52 ≤ 4294967296)
    (hOH : O + 52 ≤ H ∨ H + 152 ≤ O)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat O)
    (hw64 : w < 18446744073709551616) (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (st : μ.readN H 8 = Num.encodeLE 8 1) (sw : μ.readN (H + 8) 8 = Num.encodeLE 8 w)
    (sr : μ.readN (H + 144) 8 = Num.encodeLE 8 982) (sO : μ.readN (H + 136) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (H + 128) 8 = Num.encodeLE 8 o6)
    (hw : ∀ x, O ≤ x → x < O + 52 → μ.writable x = true)
    (hr : ∀ x, H ≤ x → x < H + 152 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 25209 ω μ x 21463 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 982 ∧ ω'[1] = UInt64.ofNat (H + 152) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat o6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 9) 32 = μ.readN (H + 16) 32 ∧ μ'.readN (O + 48) 4 = Num.encodeLE 4 w ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 52 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rt := rd8 (by decide) st
  have rw0 := rd8 hw64 sw
  have rr := rd8 (by decide) sr
  have rO := rd8 hOv sO
  have ro6 := rd8 ho6 so6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hH, hO, hOH, hw, hr, rt, rw0, rr, rO, ro6, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try exact encodeLE_mod 4 w
    all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])
    all_goals try (rw [show O + 17 = O + 9 + 8 by omega, show O + 25 = O + 9 + 16 by omega,
      show O + 33 = O + 9 + 24 by omega, show H + 24 = H + 16 + 8 by omega, show H + 32 = H + 16 + 16 by omega,
      show H + 40 = H + 16 + 24 by omega]; exact copy4g μ _ (H + 16) (O + 9) (by omega))
    all_goals try decide

/-- **`Provide`'s `Inline` path up to `read_vec`** (20626 … 3473): from 20626, with tag 17 read without
    error and the reader `{ptr, len}` at rd (ω₆) holding the `u32` service (4 octets), the preimage tag
    1 (`Inline`) at ptr + 4 and ℰ(n) (w octets) at ptr + 5: the helper's frame is at H = A − 152, the
    tag word 1 at H, the service parked at H + 8, the return address 982, O and rd at H + 144, H + 136,
    H + 128, and `read_vec` is called for n octets into the slot H + 80 (ω₀ = 1168, ω₇ = H + 80,
    ω₈ = rd, ω₉ = n), the reader advanced by 5 + w. Memory changes only in A − 280 … A and the
    reader. -/
theorem pi_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len n : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 280 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 5 + (Blob.encodeNat n).length + 32 < 4294967296) (hn : n < 4294967296)
    (hlen : 5 + (Blob.encodeNat n).length ≤ len ∧ len < 4294967296) (hinl : μ.read (ptr + 4) = 1)
    (henc : μ.readN (ptr + 5) (Blob.encodeNat n).length = Blob.encodeNat n)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 280 ∨ A + 56 ≤ rd)
    (hpA : ptr + 5 + (Blob.encodeNat n).length + 32 ≤ A - 280 ∨ A + 56 ≤ ptr)
    (hpr : ptr + 5 + (Blob.encodeNat n).length + 32 ≤ rd ∨ rd + 16 ≤ ptr) (hO64 : O < 18446744073709551616)
    (hws : ∀ a, A - 280 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 5 + (Blob.encodeNat n).length → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 3473 ω' μ' x 1000 ∧
      ω'[0] = UInt64.ofNat 1168 ∧ ω'[1] = UInt64.ofNat (A - 152) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (A - 152 + 80) ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat n ∧
      μ'.readN (A - 152) 8 = Num.encodeLE 8 1 ∧ (μ'.readN (A - 152 + 8) 8).take 4 = μ.readN ptr 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 982 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 5 + (Blob.encodeNat n).length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 5 - (Blob.encodeNat n).length) ∧
      (∀ a, a < 4294967296 → (a < A - 280 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hrd64 : rd < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  generalize hW : (Blob.encodeNat n).length = w at *
  have hv : Num.decodeLE (μ.readN ptr 4) < 4294967296 := by
    have := decodeLE_lt (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) = μ.readN ptr 4 := by
    have := encodeLE_decodeLE (μ.readN ptr 4); simpa [Memory.length_readN] using this
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 17 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, ffr, frd, fwr⟩ :=
    p1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the u32, into H + 48
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1160 25012 (A - 152) rd (A - 104) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_579 bs_25012 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- parked at H + 8, and the tag's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    p2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 152) (Num.decodeLE (μ.readN ptr 4)) (by omega) (g1.trans f1) g7 hv
      (by rw [show A - 152 + 48 = A - 104 by omega, gbuf, ev]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- the tag, into H + 48
  obtain ⟨ω5, μ5, run5, m0, m1, -, -, -, m5, m6, -, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1162 25041 (A - 152) rd (A - 104) (ptr + 4) (len - 4) 1 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 152 + 48 = A - 104 by omega]) k9
      (by decide) jte_580 bs_25041 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have pay4 : ∀ q, ptr ≤ q → q < ptr + 5 + w → μ4.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega) (by omega)).trans ((gfr q (by omega) (by omega) (by omega) (by omega)).trans
      (ffr q (by omega) (by omega)))
  have htag5 : μ5.read (A - 152 + 48) = 1 := by
    have := congrArg List.head? mbuf
    simp only [Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.head?_cons,
      Option.some.injEq] at this
    rw [show A - 152 + 48 = A - 104 by omega, this, pay4 _ (by omega) (by omega)]; exact hinl
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, ntag, nfr, nrd, nwr⟩ :=
    q3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 152) (by omega) (m1.trans (k1.trans (g1.trans f1))) m7 htag5
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (by rw [mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have h6' : ω6[6] = UInt64.ofNat rd := n6.trans (m6.trans (k6.trans (g6.trans f6)))
  have h1' : ω6[1] = UInt64.ofNat (A - 152) := n1.trans (m1.trans (k1.trans (g1.trans f1)))
  -- the length
  have pay5 : ∀ q, ptr + 5 ≤ q → q < ptr + 5 + w → μ6.read q = μ.read q := fun q h1 h2 =>
    (nfr q (by omega) (by omega)).trans ((mfr q (by omega) (by omega) (by omega) (by omega)).trans
      (pay4 q (by omega) h2))
  obtain ⟨ω7, μ7, run7, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω6 μ6 1166 25129 (A - 152) rd (ptr + 5) (len - 4 - 1) n0 h1'
      (n7.trans (m6.trans (k6.trans (g6.trans f6)))) (by decide) jte_582 bs_25129 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩
      (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega))]; exact mR8) n hn
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay5 _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω8, run8, c0, c1, c5, c6, c7, c8, c9⟩ :=
    q4 (p := p) (P := P) (R := R) x ω7 μ7 (A - 152) rd n (by omega) (d1.trans h1') (d6.trans h6') d7 d8 hn hrd64
  have run := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8))))))
  have b7 : ∀ a, a < 4294967296 → (a < A - 280 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((nfr a h0 (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega) (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))))
  have b7s : ∀ a, A - 24 ≤ a → a < A → μ7.read a = μ2.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((nfr a (by omega) (by omega)).trans
      ((mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))))
  refine ⟨ω8, μ7, run.mono (by omega), c0, c1.trans (d1.trans h1'), c5.trans (d5.trans (n5.trans (m5.trans
    (k5.trans (g5.trans f5))))), c6.trans (d6.trans h6'), c7, c8, c9, ?_, ?_, ?_, ?_, ?_, dR0,
    by rw [← show len - 4 - 1 - w = len - 5 - w by omega]; exact dR8, b7, fun a => by rw [drd, nrd, mrd, krd, grd, frd],
    fun a => by rw [dwr, nwr, mwr, kwr, gwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega) (by omega))]; exact ntag
  · rw [Memory.readN_congr (fun j hj => (dfr _ (by omega) (by omega) (by omega)).trans
      ((nfr _ (by omega) (by omega)).trans (mfr _ (by omega) (by omega) (by omega) (by omega)))), kpark, ev]
  · rw [Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f88
  · rw [Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f80
  · rw [Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f72

theorem readN_slice {μ μ' : Memory} {a b m i k : Nat} (h : μ'.readN a m = μ.readN b m) (hk : i + k ≤ m) :
    μ'.readN (a + i) k = μ.readN (b + i) k := by
  apply readN_congr2; intro j hj
  have := congrArg (fun l => l[i + j]?) h
  simp only [Memory.readN, List.getElem?_map, List.getElem?_range (show i + j < m by omega),
    Option.map_some, Option.some.injEq] at this
  simpa [Nat.add_assoc] using this

/-- **`Provide`'s `Inline` path from `read_vec`'s return** (25153 … t): with the `Vec`
    `{cap, ptr q, len n}` at H + 80 (H = A − 152, cap not 2⁶⁴ − 1), the tag word 1 at H, the parked
    word w at H + 8, the return address 982, O and o6 at H + 144, H + 136, H + 128, and
    `Instruction::decode`'s frame at A: the helper stores `Provide { service, preimage: Inline(bytes) }`
    into O (the discriminant word 2^63 + 16, the tag 1 at O + 8, the `Vec` at O + 16, the service's
    four octets at O + 48) and `Instruction::decode` returns to t. Memory changes only in
    H + 16 … H + 128 and O … O + 52. -/
theorem pi_post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 cap q n w o6 : Nat) (hA : 65536 + 280 ≤ A ∧ A + 56 < 4294967296)
    (hO : O + 52 ≤ 4294967296) (hOA : O + 52 ≤ A - 152 ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat (A - 152)) (h5 : ω[5] = UInt64.ofNat O)
    (hcap : cap < 18446744073709551615) (hq : q < 18446744073709551616) (hn : n < 18446744073709551616)
    (hw64 : w < 18446744073709551616) (ho6 : o6 < 18446744073709551616)
    (s80 : μ.readN (A - 152 + 80) 8 = Num.encodeLE 8 cap) (s88 : μ.readN (A - 152 + 88) 8 = Num.encodeLE 8 q)
    (s96 : μ.readN (A - 152 + 96) 8 = Num.encodeLE 8 n)
    (st : μ.readN (A - 152) 8 = Num.encodeLE 8 1) (sw : μ.readN (A - 152 + 8) 8 = Num.encodeLE 8 w)
    (sr : μ.readN (A - 8) 8 = Num.encodeLE 8 982) (sO : μ.readN (A - 16) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (A - 24) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hws : ∀ a, A - 152 ≤ a → a < A → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 52 → μ.writable a = true)
    (hrA : ∀ a, A + 32 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 25153 ω μ x t ω' μ' x 60 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 32) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 48) 4 = Num.encodeLE 4 w ∧
      (∀ a, a < 4294967296 → (a < A - 152 + 16 ∨ A - 152 + 128 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a1, a5, a6, c23, c31, c39, fr1, rd1, wr1⟩ :=
    q5 (p := p) (P := P) (R := R) x ω μ (A - 152) cap q n (by omega) h1 hcap hq hn s80 s88 s96
      (fun a h1 h2 => hws a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < A - 152 + 16 ∨ A - 152 + 128 ≤ a) → μ1.read a = μ.read a := fr1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bO, bO8, bO9, bO48, fr2, rd2, wr2⟩ :=
    p5i (p := p) (P := P) (R := R) x ω1 μ1 (A - 152) O w o6 (by omega) hO (by omega) (a1.trans h1) (a5.trans h5)
      hw64 ho6 (by omega)
      (by rw [Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact st)
      (by rw [Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact sw)
      (by rw [show A - 152 + 144 = A - 8 by omega, Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact sr)
      (by rw [show A - 152 + 136 = A - 16 by omega, Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact sO)
      (by rw [show A - 152 + 128 = A - 24 by omega, Memory.readN_congr (fun j hj => k1 _ (by omega) (by omega))]; exact so6)
      (fun a h1 h2 => by rw [wr1]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have k2 : ∀ a, a < 4294967296 → (a < A - 152 + 16 ∨ A - 152 + 128 ≤ a) → (a < O ∨ O + 52 ≤ a) →
      μ2.read a = μ.read a := fun a h0 h1 h2 => (fr2 a h0 h2).trans (k1 a h0 h1)
  obtain ⟨ω3, run3, d0, d1, d5, d6⟩ :=
    p6 (p := p) (P := P) (R := R) x ω2 μ2 A ret t v5 v6 ⟨by omega, by omega⟩
      (by rw [b1]; congr 1; omega) hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s6)
      hret hjt hbt (fun a h1 h2 => by rw [rd2, rd1]; exact hrA a h1 h2)
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), d0, d1, d5, d6, bO, bO8, ?_, ?_, ?_, bO48, k2,
    fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  · rw [show O + 16 = O + 9 + 7 by omega, readN_slice bO9 (by omega), show A - 152 + 16 + 7 = A - 152 + 23 by omega]
    exact c23
  · rw [show O + 24 = O + 9 + 15 by omega, readN_slice bO9 (by omega), show A - 152 + 16 + 15 = A - 152 + 31 by omega]
    exact c31
  · rw [show O + 32 = O + 9 + 23 by omega, readN_slice bO9 (by omega), show A - 152 + 16 + 23 = A - 152 + 39 by omega]
    exact c39

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.VecU8 Services.Bootstrap.CodeX

/-- **`Provide { service, preimage: Inline(bytes) }`, 1 ≤ n = |bytes| ≤ 16384**: from 20626, with tag 17
    read without error and the reader `{ptr, len}` at rd (ω₆) holding the service (4 octets), the
    preimage tag 1 at ptr + 4, ℰ(n) (w octets) at ptr + 5 and n more octets, and the model's `alloc`
    (the host's `growTo pb`) returning q for ⌈n/32⌉ units, `Instruction::decode` returns
    `Provide { service, preimage: Inline(bytes) }` in O: the discriminant word 2^63 + 16, the tag 1 at
    O + 8, the `Vec` `{cap n, ptr q, len n}` at O + 16, the service's four octets at O + 48, and the n
    octets (from ptr + 5 + w) at q. The reader is advanced by 5 + w + n. The heap holds the model's
    state after the `alloc` (as `vec_u8_small`); from A up, memory changes only in the reader and
    O … O + 52. -/
theorem provide_inline_small {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State)
    (A O ret t v5 v6 rd ptr len n q pb ph : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s'))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hS : S0 + 472 ≤ A ∧ A + 56 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) (hS1 : S1 < 4294967296)
    (hA8 : 2147484120 ≤ A ∧ A % 8 = 0) (hn : 1 ≤ n ∧ n ≤ 16384)
    (hlen : 5 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 52 ≤ S1) (hOr : O + 52 ≤ rd ∨ rd + 16 ≤ O)
    (hptr : A + 56 ≤ ptr ∧ ptr + 5 + (Blob.encodeNat n).length + n + 32 < 4294967296)
    (hpr : ptr + 5 + (Blob.encodeNat n).length + n + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hinl : μ.read (ptr + 4) = 1) (henc : μ.readN (ptr + 5) (Blob.encodeNat n).length = Blob.encodeNat n)
    (hra : ∀ a, ptr ≤ a → a < ptr + 5 + (Blob.encodeNat n).length + n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 20626 ω μ x t ω' μ' x (2 * n + 2200) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 32) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 48) 4 = μ.readN ptr 4 ∧
      μ'.readN q n = μ.readN (ptr + 5 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 5 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 5 - (Blob.encodeNat n).length - n) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hqT := (alloc_block hwf hbT h).2.2.2.2
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, atag, apark, a982, aO, ard, aR0, aR8, afr, ard', awr⟩ :=
    pi_pre (p := p) (P := P) (R := refineContract env) x ω μ A O ret t v5 v6 rd ptr len n F ⟨by omega, hA8.2⟩
      h6 h7 tag tab hrt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, hlen.2⟩ hinl henc hR0 hR8
      (Or.inr hrd.1) (Or.inr hptr.1) (by omega) hO64 (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hra a h1 (by omega))
  generalize hW : (Blob.encodeNat n).length = w at *
  have b1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h0 => afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => b1 a ha2
  have hl1 : rdN μ1 206848 1 = 0 := by rw [rdN_frame (fun j hj => b1 _ (by omega))]; exact hl
  obtain ⟨ω2, μ2, run2, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, rep2, wf2, fo2, cl2, cm2, hp2, hst2, pg2,
      vfr⟩ :=
    vec_u8_small (p := p) (P := P) env x ω1 μ1 s s' (A - 152) (A - 152 + 80) rd (ptr + 5 + w) (len - 5 - w) n 1168
      25153 O rd q pb ph hwf rep1 hbd h48 hhb hbs hcost h hb0 hbT hA hfo hl1 (S0 := S0) (S1 := S1) hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp awr) (fun a h1 h2 => by rw [awr]; exact hst a h1 h2) hHT hS1
      ⟨by omega, by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by decide) jte_583 bs_25153 hO64 (by omega) hn
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ aR0 aR8
      (fun a h1 h2 => by rw [ard']; exact hra a (by omega) (by omega))
  have hS2 : ∀ a, A - 152 ≤ a → a < 4294967296 → (a < A - 152 + 80 ∨ A - 152 + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ2.read a = μ1.read a := fun a h1 h2 h3 h4 => vfr a h2 h1 h4 (by omega)
  obtain ⟨hp2', hHT2, hph, hpb⟩ := hp2.choose_spec
  obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO48, zfr, zrd, zwr⟩ :=
    pi_post (p := p) (P := P) (R := refineContract env) x ω2 μ2 A O ret t v5 v6 n q n (rdN μ1 (A - 152 + 8) 8) rd
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) (rdN_lt64 _ _) (by omega)
      vc (by rw [show A - 152 + 88 = A - 152 + 80 + 8 by omega]; exact vp)
      (by rw [show A - 152 + 96 = A - 152 + 80 + 16 by omega]; exact vl)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact atag)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]
          exact (encodeLE_rdN _ _ _).symm)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact a982)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact aO)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact ard)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s6)
      F.hret F.hjt F.hbt F.hv5 F.hv6
      (fun a h1 h2 => hst2 a (by omega) (by omega)) (fun a h1 h2 => hst2 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
  have hlow : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a h0 => zfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hbase' : s'.base = s.base := (alloc_block hwf hbT h).1
  have hb0' : 206864 ≤ s'.base := by rw [hbase']; exact hb0
  have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase']; exact hbT
  have run := run1.trans (run2.trans run3)
  have wr3 : ∀ a, μ3.writable a = μ2.writable a := zwr
  refine ⟨ω3, μ3, run.mono (by omega), z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, ?_, ?_, ?_, ?_,
    rep2.congr_lock wf2 hb0' hbT' (fun a ha1 ha2 ha3 => hlow a ha2), wf2, fo2,
    by rw [rdN_frame (fun j hj => hlow _ (by omega))]; exact cl2, cm2,
    ⟨hp2.choose, HeapPages.of_eq hp2' wr3, hHT2, hph, hpb⟩, fun a h1 h2 => by rw [wr3]; exact hst2 a h1 h2,
    FreeStepsH.pagesOut hbd run, ?_⟩
  · rw [zO48, ← take_encodeLE, encodeLE_rdN]; exact apark
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR0
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR8
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) h3, vfr a h0 (by omega) h2 (by omega)]; exact afr a h0 (Or.inr h1) h2

/-- **`Provide { service, preimage: Inline(bytes) }`, 16384 < n = |bytes| < 2³⁰ − 64**: as
    `provide_inline_small`, the bytes read through `read_vec`'s chunk loop (`vec_u8_big`): from 20626, with tag 17
    read without error and the reader `{ptr, len}` at rd (ω₆) holding the service (4 octets), the
    preimage tag 1 at ptr + 4, ℰ(n) (w octets) at ptr + 5 and n more octets, and the model's `alloc`
    returning q₀ for the first chunk's 512 units, either `Instruction::decode` returns
    `Provide { service, preimage: Inline(bytes) }` in O (the `Vec` `{cap n, ptr q, len n}` at O + 16,
    the n octets at q, q an allocated chunk of ⌈n/32⌉ + 1 units of the model's state after the
    `realloc`s), or the run reaches `finish_grow`'s return point from a `realloc` that the model fails
    (33055, ω₇ = 0). -/
theorem provide_inline_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State)
    (A O ret t v5 v6 rd ptr len n q0 pb ph : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 512 s = some (q0, s1))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hS : S0 + 608 ≤ A ∧ A + 56 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) (hS1 : S1 < 4294967296)
    (hA8 : 2147484256 ≤ A ∧ A % 8 = 0) (hn : 16384 < n ∧ n < 1073741760)
    (hlen : 5 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 52 ≤ S1) (hOr : O + 52 ≤ rd ∨ rd + 16 ≤ O)
    (hptr : A + 56 ≤ ptr ∧ ptr + 5 + (Blob.encodeNat n).length + n + 32 < 4294967296)
    (hpr : ptr + 5 + (Blob.encodeNat n).length + n + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hinl : μ.read (ptr + 4) = 1) (henc : μ.readN (ptr + 5) (Blob.encodeNat n).length = Blob.encodeNat n)
    (hra : ∀ a, ptr ≤ a → a < ptr + 5 + (Blob.encodeNat n).length + n → μ.readable a = true) :
    (∃ ω' μ' s' q h', FreeStepsH p (refineContract env) 20626 ω μ x t ω' μ' x
        (35200 + loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 32) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 48) 4 = μ.readN ptr 4 ∧
      μ'.readN q n = μ.readN (ptr + 5 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 5 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 5 - (Blob.encodeNat n).length - n) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (∃ c ∈ chunks s', c.addr + 32 = q ∧ c.used = true ∧ c.size = (n + 31) / 32 + 1) ∧ s'.base = s.base ∧
      HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ' s'' q'' n'', FreeStepsH p (refineContract env) 20626 ω μ x 33055 ω' μ' x
        (35200 + loopSteps 16384 (n - 16384)) ∧
      ω'[7] = UInt64.ofNat 0 ∧ realloc (growTo pb) hb s'' q'' 1 n'' = none ∧ Rep μ' s'' ∧ WF s'') := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, atag, apark, a982, aO, ard, aR0, aR8, afr, ard', awr⟩ :=
    pi_pre (p := p) (P := P) (R := refineContract env) x ω μ A O ret t v5 v6 rd ptr len n F ⟨by omega, hA8.2⟩
      h6 h7 tag tab hrt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, hlen.2⟩ hinl henc hR0 hR8
      (Or.inr hrd.1) (Or.inr hptr.1) (by omega) hO64 (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hra a h1 (by omega))
  generalize hW : (Blob.encodeNat n).length = w at *
  have b1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h0 => afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => b1 a ha2
  have hl1 : rdN μ1 206848 1 = 0 := by rw [rdN_frame (fun j hj => b1 _ (by omega))]; exact hl
  have hbig := vec_u8_big (p := p) (P := P) env x ω1 μ1 s s1 (A - 152) (A - 152 + 80) rd (ptr + 5 + w) (len - 5 - w) n
      1168 25153 O rd q0 pb ph hwf rep1 hbd h48 hhb hbs hcost h hb0 hbT hA hfo hl1 (S0 := S0) (S1 := S1) hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp awr) (fun a h1 h2 => by rw [awr]; exact hst a h1 h2) hHT hS1
      ⟨by omega, by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by decide) jte_583 bs_25153 hO64 (by omega) hn
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩ (by omega)
      aR0 aR8 (fun a h1 h2 => by rw [ard']; exact hra a (by omega) (by omega))
  rcases hbig with ⟨ω2, μ2, s', q, h', run2, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, rep2, wf2, fo2, cl2, cm2,
      hbase', hp2', hHT2, hph, hpb, hst2, pg2, vfr⟩ | ⟨ω2, μ2, s'', q'', n'', run2, f7, fR, frep, fwf⟩
  rotate_left
  · exact Or.inr ⟨ω2, μ2, s'', q'', n'', (run1.trans run2).mono (by omega), f7, fR, frep, fwf⟩
  have hqT : q + n < 2147483648 := by
    obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := cm2
    have := chunk_in wf2 hcrm hcru; rw [hcrs] at this; omega
  have hS2 : ∀ a, A - 152 ≤ a → a < 4294967296 → (a < A - 152 + 80 ∨ A - 152 + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ2.read a = μ1.read a := fun a h1 h2 h3 h4 => vfr a h2 h1 h4 (by omega)
  obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO48, zfr, zrd, zwr⟩ :=
    pi_post (p := p) (P := P) (R := refineContract env) x ω2 μ2 A O ret t v5 v6 n q n (rdN μ1 (A - 152 + 8) 8) rd
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) (rdN_lt64 _ _) (by omega)
      vc (by rw [show A - 152 + 88 = A - 152 + 80 + 8 by omega]; exact vp)
      (by rw [show A - 152 + 96 = A - 152 + 80 + 16 by omega]; exact vl)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact atag)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]
          exact (encodeLE_rdN _ _ _).symm)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact a982)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact aO)
      (by rw [Memory.readN_congr (fun j hj => hS2 _ (by omega) (by omega) (by omega) (by omega))]; exact ard)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => (hS2 _ (by omega) (by omega) (by omega) (by omega)).trans
            (afr _ (by omega) (by omega) (by omega)))]; exact F.s6)
      F.hret F.hjt F.hbt F.hv5 F.hv6
      (fun a h1 h2 => hst2 a (by omega) (by omega)) (fun a h1 h2 => hst2 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
  have hlow : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a h0 => zfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hb0' : 206864 ≤ s'.base := by rw [hbase']; exact hb0
  have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase']; exact hbT
  have run := run1.trans (run2.trans run3)
  have wr3 : ∀ a, μ3.writable a = μ2.writable a := zwr
  refine Or.inl ⟨ω3, μ3, s', q, h', run.mono (by omega), z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, ?_, ?_, ?_, ?_,
    rep2.congr_lock wf2 hb0' hbT' (fun a ha1 ha2 ha3 => hlow a ha2), wf2, fo2,
    by rw [rdN_frame (fun j hj => hlow _ (by omega))]; exact cl2, cm2, hbase',
    HeapPages.of_eq hp2' wr3, hHT2, hph, hpb, fun a h1 h2 => by rw [wr3]; exact hst2 a h1 h2,
    FreeStepsH.pagesOut hbd run, ?_⟩
  · rw [zO48, ← take_encodeLE, encodeLE_rdN]; exact apark
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR0
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR8
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) h3, vfr a h0 (by omega) h2 (by omega)]; exact afr a h0 (Or.inr h1) h2

end Services.Bootstrap.Decode.Provide
