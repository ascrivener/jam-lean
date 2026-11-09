import Services.Bootstrap.Decode.U32Hash

/-!
# `Instruction::decode`: `RandomStorageRefine { seed: u64, n: u8 }`

`RandomStorageRefine` (tag 21, encoded as `[21] ++ u64 ++ u8`) is decoded by the decoder's own frame at
S = A − 56 and a shared helper (at 35406, the jump-table entry 825) that decodes a `(u64, u8)` pair
into a result at A: the `u64` is read into S + 16 and parked at S, the `u8` read into S + 31, and the
helper writes `Ok` (the word 0) at A, the `u64` at A + 8 and the `u8` at A + 16. The decoder then
stores the variant: the discriminant word 2^63 + 20 at O, the `u64` at O + 8 and the `u8` at O + 16.
-/

namespace Services.Bootstrap.Decode.RandomStorageRefine

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21569 … 21609: the decoder opens its frame at S = A − 56 saving the return address 994, O and the
    reader at S + 48, S + 40, S + 32 and the result's address A at S + 8, zeroes S + 16 … S + 24 and calls
    the reader for 8 octets into S + 16 (return address 1652). -/
theorem r1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 56 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 56 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21569 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1652 ∧ ω'[1] = UInt64.ofNat (A - 56) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 40) ∧
      ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 994 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧ μ'.readN (A - 48) 8 = Num.encodeLE 8 A ∧
      (∀ a, a < 4294967296 → (a < A - 56 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show A - 56 + 48 = A - 8 by omega, show A - 56 + 40 = A - 16 by omega,
      show A - 56 + 32 = A - 24 by omega, show A - 56 + 8 = A - 48 by omega,
      show A - 56 + 16 = A - 40 by omega])
    all_goals post_simp
    all_goals try exact h5

/-- 35406 then 35433 … 35453: the `u64` read succeeded (ω₇ = 0): the helper parks it at S, zeroes
    S + 31 and calls the reader for 1 octet into S + 31 (return address 1654). -/
theorem r2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 16) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hw : ∀ a, S + 31 ≤ a → a < S + 32 → μ.writable a = true)
    (hr : ∀ a, S + 16 ≤ a → a < S + 24 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 35406 ω μ x 58434 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1654 ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 31) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN S 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → a ≠ S + 31 → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 16) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 35459 … 35491: the `u8` read succeeded (ω₇ = 0): the helper writes `Ok` (0) at A = S + 56, the
    `u64` (S) at A + 8 and the `u8` (S + 31) at A + 16 and returns through 994 to 21613. -/
theorem r3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O v o6 : Nat) (c : UInt8) (hA : S + 56 + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sv : μ.readN S 8 = Num.encodeLE 8 v) (sc : μ.read (S + 31) = c)
    (sA : μ.readN (S + 8) 8 = Num.encodeLE 8 (S + 56))
    (sr : μ.readN (S + 48) 8 = Num.encodeLE 8 994) (sO : μ.readN (S + 40) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 32) 8 = Num.encodeLE 8 o6)
    (hwA : ∀ x, S + 56 ≤ x → x < S + 73 → μ.writable x = true)
    (hr : ∀ x, S ≤ x → x < S + 56 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 35459 ω μ x 21613 ω' μ' x 13 ∧
      ω'[1] = UInt64.ofNat (S + 56) ∧ ω'[5] = UInt64.ofNat O ∧ ω'[6] = UInt64.ofNat o6 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 64) 8 = Num.encodeLE 8 v ∧
      μ'.read (S + 72) = c ∧
      (∀ x, x < 4294967296 → (x < S + 56 ∨ S + 73 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rv := rd _ v hv sv
  have rA := rd _ (S + 56) (by omega) sA
  have rr := rd _ 994 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have rc : rdN μ (S + 31) 1 = c.toNat := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, sc, Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hA, hwA, hr, rv, rA, rr, rO, ro6, rc, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])

/-- 21613 … 21655: the helper returned `Ok` (the word 0 at A): the decoder stores
    `RandomStorageRefine`'s discriminant word 2^63 + 20 at O, the `u64` (A + 8) at O + 8 and the `u8`
    (A + 16) at O + 16, and returns through its frame. -/
theorem r4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 v : Nat) (c : UInt8) (hA : A + 56 < 4294967296) (hO : O + 17 ≤ 4294967296)
    (hOA : O + 17 ≤ A ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (hv : v < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0w : μ.readN A 8 = Num.encodeLE 8 0) (sv : μ.readN (A + 8) 8 = Num.encodeLE 8 v) (sc : μ.read (A + 16) = c)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ x, O ≤ x → x < O + 17 → μ.writable x = true)
    (hr : ∀ x, A ≤ x → x < A + 56 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 21613 ω μ x t ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775828 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 v ∧
      μ'.read (O + 16) = c ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 17 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r00 := rd _ 0 (by decide) s0w
  have rv := rd _ v hv sv
  have r0 := rd _ ret (by omega) s0
  have r5 := rd _ v5 hv5 s5
  have r6 := rd _ v6 hv6 s6
  have rc : rdN μ (A + 16) 1 = c.toNat := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, sc, Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hA, hO, hOA, hw, hr, r00, rv, r0, r5, r6, rc, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])

/-- **`RandomStorageRefine`**: from 20626, with tag 21 read without error and the reader `{ptr, len}`
    at rd (ω₆) holding at least 9 more octets, `Instruction::decode` returns
    `RandomStorageRefine { seed, n }` in its slot O: the discriminant word 2^63 + 20 at O, the 8 octets
    of `seed` (from ptr) at O + 8 and the octet `n` (from ptr + 8) at O + 16. The reader is advanced by
    9. Memory changes only in A − 144 … A + 24 (the decoder's and the reader's frames, and the helper's
    result at A), the reader and O … O + 17. -/
theorem random_storage_refine {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 144 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 21) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 25 < 4294967296)
    (hlen : 9 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 144 ∨ A + 56 ≤ rd) (hpA : ptr + 25 ≤ A - 144 ∨ A + 56 ≤ ptr)
    (hOA' : O + 17 ≤ A - 144 ∨ A + 56 ≤ O) (hOr : O + 17 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 9 ≤ rd ∨ rd + 16 ≤ ptr) (hO17 : O + 17 ≤ 4294967296)
    (hws : ∀ a, A - 144 ≤ a → a < A + 24 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 17 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 9 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 300 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775828 ∧ μ'.readN (O + 8) 8 = μ.readN ptr 8 ∧
      μ'.read (O + 16) = μ.read (ptr + 8) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 9) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 9) ∧
      (∀ a, a < 4294967296 → (a < A - 144 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 17 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have dl : ∀ q, Num.decodeLE (μ.readN q 8) < 18446744073709551616 := fun q => by
    have := decodeLE_lt (μ.readN q 8); simpa [Memory.length_readN] using this
  have el : ∀ q, Num.encodeLE 8 (Num.decodeLE (μ.readN q 8)) = μ.readN q 8 := fun q => by
    have := encodeLE_decodeLE (μ.readN q 8); simpa [Memory.length_readN] using this
  -- the dispatch and the frame
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 21 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, f48, ffr, frd, fwr⟩ :=
    r1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) (by omega))
  -- the u64, into S + 16
  obtain ⟨ω3, μ3, run3, m0, m1, m2, m3, m4, m5, m6, m12, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1652 35406 (A - 56) rd (A - 40) ptr len 8 f0 f1 f7 f8 f9
      (by decide) jte_825 bs_35406 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have pay3 : ∀ q, ptr ≤ q → q < ptr + 9 → μ3.read q = μ.read q := fun q h1 h2 =>
    (mfr q (by omega) (by omega) (by omega) (by omega)).trans (ffr q (by omega) (by omega))
  -- parked at S; the u8's call
  obtain ⟨ω4, μ4, run4, k0, k1, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    r2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 56) (Num.decodeLE (μ.readN ptr 8)) (by omega) (m1.trans f1) m7
      (dl _) (by rw [show A - 56 + 16 = A - 40 by omega, mbuf, el]
                 exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mrd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the u8, into S + 31
  obtain ⟨ω5, μ5, run5, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1654 35459 (A - 56) rd (A - 56 + 31) (ptr + 8) (len - 8) 1 k0
      (k1.trans (m1.trans f1)) (k7.trans (m6.trans f6)) k8 k9
      (by decide) jte_826 bs_35459 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, mrd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact mR8)
  have hc5 : μ5.read (A - 56 + 31) = μ.read (ptr + 8) := by
    have := congrArg List.head? nbuf
    simp only [Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.head?_cons,
      Option.some.injEq] at this
    rw [this, kfr _ (by omega) (by omega) (by omega), pay3 _ (by omega) (by omega)]
  -- back to the frame's facts
  have b5s : ∀ a, (A - 48 ≤ a ∧ a < A - 40) ∨ (A - 24 ≤ a ∧ a < A) → μ5.read a = μ2.read a :=
    fun a h1 => (nfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((kfr a (by omega) (by omega) (by omega)).trans (mfr a (by omega) (by omega) (by omega) (by omega)))
  have b5 : ∀ a, a < 4294967296 → (a < A - 144 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (nfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega) (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))
  obtain ⟨ω6, μ6, run6, q1, q5, q6, qA0, qAv, qAc, qfr, qrd, qwr⟩ := r3 (p := p) (P := P) (R := R) x ω5 μ5
    (A - 56) O (Num.decodeLE (μ.readN ptr 8)) rd (μ.read (ptr + 8)) (by omega) (n1.trans (k1.trans (m1.trans f1))) n7
    (dl _) hrd64 hO64
    (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega) (by omega))]; exact kpark)
    hc5
    (by rw [Memory.readN_congr (fun j hj => b5s _ (by omega)),
          show A - 56 + 8 = A - 48 by omega, show A - 56 + 56 = A by omega]; exact f48)
    (by rw [Memory.readN_congr (fun j hj => b5s _ (by omega)),
          show A - 56 + 48 = A - 8 by omega]; exact f88)
    (by rw [Memory.readN_congr (fun j hj => b5s _ (by omega)),
          show A - 56 + 40 = A - 16 by omega]; exact f80)
    (by rw [Memory.readN_congr (fun j hj => b5s _ (by omega)),
          show A - 56 + 32 = A - 24 by omega]; exact f72)
    (fun a h1 h2 => by rw [nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [nrd, krd, mrd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have b6 : ∀ a, a < 4294967296 → (a < A - 144 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (qfr a h0 (by omega)).trans (b5 a h0 (by omega) h2)
  obtain ⟨ω7, μ7, run7, r0, r1', r5, r6, rO, rO8, rO16, rfr, rrd, rwr⟩ := r4 (p := p) (P := P) (R := R) x ω6 μ6
    A O ret t v5 v6 (Num.decodeLE (μ.readN ptr 8)) (μ.read (ptr + 8)) (by omega) hO17 (by omega)
    (by rw [q1]; congr 1; omega) q5 (dl _) F.hv5 F.hv6
    (by rw [show A = A - 56 + 56 by omega]; exact qA0)
    (by rw [show A + 8 = A - 56 + 64 by omega]; exact qAv)
    (by rw [show A + 16 = A - 56 + 72 by omega]; exact qAc)
    (by rw [Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [qwr, nwr, kwr, mwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [qrd, nrd, krd, mrd, frd]
      rcases Nat.lt_or_ge a (A + 24) with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a (by omega) (by omega))
  refine ⟨ω7, μ7, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    run7)))))).mono (by omega), r0, r1', r5, r6, rO, rO8.trans (el _), rO16, ?_, ?_, ?_,
    fun a => by rw [rrd, qrd, nrd, krd, mrd, frd], fun a => by rw [rwr, qwr, nwr, kwr, mwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega)).trans (qfr _ (by omega) (by omega))), nR0]
  · rw [Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega)).trans (qfr _ (by omega) (by omega)))]
    exact nR8.trans (congrArg (Num.encodeLE 8) (by omega))
  · intro a h0 h1 h2 h3
    rw [rfr a h0 h3]; exact b6 a h0 h1 h2

end Services.Bootstrap.Decode.RandomStorageRefine
