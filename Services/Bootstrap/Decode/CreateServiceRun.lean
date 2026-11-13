import Services.Bootstrap.Decode.CreateService
import Services.Bootstrap.Decode.Loop

/-!
# `Instruction::decode`: `CreateService` (tag 0), the runs

From the steps in `Services.Bootstrap.Decode.CreateService` (GP v0.8.0 B.7, the bootstrap service's
instruction list), generic in the host relation:

* `cs_head`: from 20626 to the call of `Option<Vec<u8>>::decode` (35937), the hash, the four `u64`s and
  the array read and parked in the decoder's frame;
* `cs_end`, `cs_tail`: from that call's return (24265), with the option's three words in the slot
  S + 232, through the `u64`, the `Option<u32>` (`None` or `Some`) and the stores, to the return;
* `create_service_none`: `CreateService` with `Option<Vec<u8>>` = `None`, end to end.
-/

namespace Services.Bootstrap.Decode.CreateService

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`CreateService`'s fixed-size fields, up to its `Option<Vec<u8>>`**: from 20626, with tag 0 read
    without error and the reader `{ptr, len}` at rd (ω₆) holding at least 192 more octets, the decoder
    (frame S = A − 384) reads the hash (ptr … ptr + 32) into S + 72, the four `u64`s (from ptr + 32,
    ptr + 40, ptr + 48, ptr + 56) into S + 64, S + 56, S + 48, S + 40 and the array (ptr + 64 …
    ptr + 192) into S + 104, and calls `Option<Vec<u8>>::decode` (35937) with the slot S + 232, the
    reader advanced by 192 and the return address 1130. Memory changes only in S − 88 … A and the
    reader. -/
theorem cs_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 rd ptr len : Nat) (F : Frame P (S + 384) O ret t v5 v6 ω μ)
    (hS : 65536 + 144 ≤ S ∧ S % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (S + 384) = 0) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 216 < 4294967296)
    (hlen : 192 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdS : rd + 16 ≤ S - 88 ∨ S + 384 ≤ rd) (hpS : ptr + 216 ≤ S - 88 ∨ S + 384 ≤ ptr)
    (hpr : ptr + 192 ≤ rd ∨ rd + 16 ≤ ptr)
    (hws : ∀ a, S - 88 ≤ a → a < S + 384 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 192 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x 35937 ω' μ' x 2650 ∧
      ω'[0] = UInt64.ofNat 1130 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (S + 232) ∧ ω'[8] = UInt64.ofNat rd ∧
      μ'.readN (S + 376) 8 = Num.encodeLE 8 934 ∧ μ'.readN (S + 368) 8 = Num.encodeLE 8 O ∧
      μ'.readN (S + 360) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (S + 72) 32 = μ.readN ptr 32 ∧ μ'.readN (S + 64) 8 = μ.readN (ptr + 32) 8 ∧
      μ'.readN (S + 56) 8 = μ.readN (ptr + 40) 8 ∧ μ'.readN (S + 48) 8 = μ.readN (ptr + 48) 8 ∧
      μ'.readN (S + 40) 8 = μ.readN (ptr + 56) 8 ∧ μ'.readN (S + 104) 128 = μ.readN (ptr + 64) 128 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 192) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 192) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by have := F.hO; omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have dl : ∀ (m : Memory) q, Num.decodeLE (m.readN q 8) < 18446744073709551616 := fun m q => by
    have := decodeLE_lt (m.readN q 8); simpa [Memory.length_readN] using this
  have el : ∀ (m : Memory) q, Num.encodeLE 8 (Num.decodeLE (m.readN q 8)) = m.readN q 8 := fun m q => by
    have := encodeLE_decodeLE (m.readN q 8); simpa [Memory.length_readN] using this
  -- the dispatch and the frame
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ (S + 384) 0 (by decide)
    (by omega) F.h1 h7 tag tab (F.hr _ (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f376, f368, f360, ffr, frd, fwr⟩ :=
    c1 (p := p) (P := P) (R := R) x ω1 μ S O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  have pay2 : ∀ q, ptr ≤ q → q < ptr + 192 → μ2.read q = μ.read q := fun q h1 h2 => ffr q (by omega) (by omega)
  have rd2 : ∀ q, rd ≤ q → q < rd + 16 → μ2.read q = μ.read q := fun q h1 h2 => ffr q (by omega) (by omega)
  -- the hash, into S + 232
  obtain ⟨ω3, μ3, run3, ⟨g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω2 μ2 1114 24015 S rd (S + 232) ptr len 32 f0 f1 f7 f8 f9
      (by decide) jte_556 bs_24015 ⟨by omega, by omega, hS.2⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => rd2 _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => rd2 _ (by omega) (by omega))]; exact hR8)
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [gwr, fwr]
  have rd3 : ∀ a, μ3.readable a = μ.readable a := fun a => by rw [grd, frd]
  have pay3 : ∀ q, ptr ≤ q → q < ptr + 192 → μ3.read q = μ.read q := fun q h1 h2 =>
    (gfr q (by omega) (by omega) (by omega) (by omega)).trans (pay2 q h1 h2)
  -- the hash, to S + 72; the first u64's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, khash, kfr, krd, kwr⟩ :=
    c2 (p := p) (P := P) (R := R) x ω3 μ3 S (by omega) (g1.trans f1) g7
      (fun a h1 h2 => by rw [wr3]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [kwr, wr3]
  have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [krd, rd3]
  have pay4 : ∀ q, ptr ≤ q → q < ptr + 192 → μ4.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega) (by omega)).trans (pay3 q h1 h2)
  -- the first u64
  obtain ⟨ω5, μ5, run5, n0, n1, -, -, -, n5, n6, -, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1116 24068 S rd (S + 232) (ptr + 32) (len - 32) 8 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) k8 k9
      (by decide) jte_557 bs_24068 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr4]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [wr4]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr4]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd4]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have wr5 : ∀ a, μ5.writable a = μ.writable a := fun a => by rw [nwr, wr4]
  have rd5 : ∀ a, μ5.readable a = μ.readable a := fun a => by rw [nrd, rd4]
  have pay5 : ∀ q, ptr ≤ q → q < ptr + 192 → μ5.read q = μ.read q := fun q h1 h2 =>
    (nfr q (by omega) (by omega) (by omega) (by omega)).trans (pay4 q h1 h2)
  -- parked at S + 64; the second
  obtain ⟨ω6, μ6, run6, q0, q1, q5, q6, q7, q8, q9, qv, qfr, qrd, qwr⟩ :=
    c3 (p := p) (P := P) (R := R) x ω5 μ5 24068 64 1118 S (Num.decodeLE (μ.readN (ptr + 32) 8))
      (Or.inl ⟨rfl, rfl, rfl⟩) (by omega) (n1.trans (k1.trans (g1.trans f1))) n7 (dl _ _)
      (by rw [nbuf, el]; exact Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr5]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr5]; exact hws a (by omega) (by omega))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [qwr, wr5]
  have rd6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [qrd, rd5]
  have pay6 : ∀ q, ptr ≤ q → q < ptr + 192 → μ6.read q = μ.read q := fun q h1 h2 =>
    (qfr q (by omega) (by omega) (by omega)).trans (pay5 q h1 h2)
  obtain ⟨ω7, μ7, run7, u0, u1, -, -, -, u5, u6, -, u7, uR0, uR8, ubuf, ufr, urd, uwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω6 μ6 1118 24100 S rd (S + 232) (ptr + 40) (len - 40) 8 q0
      (q1.trans (n1.trans (k1.trans (g1.trans f1)))) (q7.trans (n6.trans (k6.trans (g6.trans f6)))) q8 q9
      (by decide) jte_558 bs_24100 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr6]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [wr6]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr6]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd6]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega))]
          exact nR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega))]
          exact nR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  have wr7 : ∀ a, μ7.writable a = μ.writable a := fun a => by rw [uwr, wr6]
  have rd7 : ∀ a, μ7.readable a = μ.readable a := fun a => by rw [urd, rd6]
  have pay7 : ∀ q, ptr ≤ q → q < ptr + 192 → μ7.read q = μ.read q := fun q h1 h2 =>
    (ufr q (by omega) (by omega) (by omega) (by omega)).trans (pay6 q h1 h2)
  -- parked at S + 56; the third
  obtain ⟨ω8, μ8, run8, w0, w1, w5, w6, w7, w8, w9, wv, wfr, wrd, wwr⟩ :=
    c3 (p := p) (P := P) (R := R) x ω7 μ7 24100 56 1120 S (Num.decodeLE (μ.readN (ptr + 40) 8))
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (by omega) (u1.trans (q1.trans (n1.trans (k1.trans (g1.trans f1))))) u7
      (dl _ _)
      (by rw [ubuf, el]; exact Memory.readN_congr (fun j hj => pay6 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr7]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr7]; exact hws a (by omega) (by omega))
  have wr8 : ∀ a, μ8.writable a = μ.writable a := fun a => by rw [wwr, wr7]
  have rd8 : ∀ a, μ8.readable a = μ.readable a := fun a => by rw [wrd, rd7]
  have pay8 : ∀ q, ptr ≤ q → q < ptr + 192 → μ8.read q = μ.read q := fun q h1 h2 =>
    (wfr q (by omega) (by omega) (by omega)).trans (pay7 q h1 h2)
  have hb1 : ω8[1] = UInt64.ofNat S := w1.trans (u1.trans (q1.trans (n1.trans (k1.trans (g1.trans f1)))))
  have hb6 : ω8[6] = UInt64.ofNat rd := w6.trans (u6.trans (q6.trans (n6.trans (k6.trans (g6.trans f6)))))
  have hb5 : ω8[5] = UInt64.ofNat O := w5.trans (u5.trans (q5.trans (n5.trans (k5.trans (g5.trans f5)))))
  obtain ⟨ω9, μ9, run9, a0, a1, -, -, -, a5, a6, -, a7, aR0, aR8, abuf, afr, ard, awr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω8 μ8 1120 24131 S rd (S + 232) (ptr + 48) (len - 48) 8 w0
      hb1 (w7.trans (u6.trans (q6.trans (n6.trans (k6.trans (g6.trans f6)))))) w8 w9
      (by decide) jte_559 bs_24131 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr8]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [wr8]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr8]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd8]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => wfr _ (by omega) (by omega) (by omega))]
          exact uR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => wfr _ (by omega) (by omega) (by omega))]
          exact uR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  have wr9 : ∀ a, μ9.writable a = μ.writable a := fun a => by rw [awr, wr8]
  have rd9 : ∀ a, μ9.readable a = μ.readable a := fun a => by rw [ard, rd8]
  -- parked at S + 48; the fourth
  obtain ⟨ω10, μ10, run10, b0, b1, b5, b6, b7, b8, b9, bv, bfr, brd, bwr⟩ :=
    c3 (p := p) (P := P) (R := R) x ω9 μ9 24131 48 1122 S (Num.decodeLE (μ.readN (ptr + 48) 8))
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by omega) (a1.trans hb1) a7 (dl _ _)
      (by rw [abuf, el]; exact Memory.readN_congr (fun j hj => pay8 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr9]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr9]; exact hws a (by omega) (by omega))
  have wr10 : ∀ a, μ10.writable a = μ.writable a := fun a => by rw [bwr, wr9]
  have rd10 : ∀ a, μ10.readable a = μ.readable a := fun a => by rw [brd, rd9]
  have pay10 : ∀ q, ptr ≤ q → q < ptr + 192 → μ10.read q = μ.read q := fun q h1 h2 =>
    (bfr q (by omega) (by omega) (by omega)).trans ((afr q (by omega) (by omega) (by omega) (by omega)).trans
      (pay8 q h1 h2))
  obtain ⟨ω11, μ11, run11, d0, d1, -, -, -, d5, d6, -, d7, dR0, dR8, dbuf, dfr, drd, dwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω10 μ10 1122 24162 S rd (S + 232) (ptr + 56) (len - 56) 8 b0
      (b1.trans (a1.trans hb1)) (b7.trans (a6.trans hb6)) b8 b9
      (by decide) jte_560 bs_24162 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr10]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [wr10]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr10]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd10]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]
          exact aR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega))]
          exact aR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  have wr11 : ∀ a, μ11.writable a = μ.writable a := fun a => by rw [dwr, wr10]
  have rd11 : ∀ a, μ11.readable a = μ.readable a := fun a => by rw [drd, rd10]
  have pay11 : ∀ q, ptr ≤ q → q < ptr + 192 → μ11.read q = μ.read q := fun q h1 h2 =>
    (dfr q (by omega) (by omega) (by omega) (by omega)).trans (pay10 q h1 h2)
  have hc1 : ω11[1] = UInt64.ofNat S := d1.trans (b1.trans (a1.trans hb1))
  have hc5 : ω11[5] = UInt64.ofNat O := d5.trans (b5.trans (a5.trans hb5))
  have hc6 : ω11[6] = UInt64.ofNat rd := d6.trans (b6.trans (a6.trans hb6))
  -- parked at S + 40; memzero's call
  obtain ⟨ω12, μ12, run12, z0, z1, z5, z6, z7, z8, z9, zv, zfr, zrd, zwr⟩ :=
    c4 (p := p) (P := P) (R := R) x ω11 μ11 S (Num.decodeLE (μ.readN (ptr + 56) 8)) (by omega) hc1 d7 (dl _ _)
      (by rw [dbuf, el]; exact Memory.readN_congr (fun j hj => pay10 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr11]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd11]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the array's buffer zeroed
  obtain ⟨ω13, μ13, run13, m0, m1, m5, m6, -, mfr, mrd, mwr⟩ :=
    Memzero.memzero (p := p) (P := P) (R := R) x ω12 μ12 (S + 232) 128 1124 24190 (by omega)
      ⟨by decide, by decide⟩ (by omega) z0 z7 z8 z9 (by decide) jte_561 bs_24190
      (fun a h1 h2 => by rw [zwr, wr11]; exact hws a (by omega) (by omega))
  have wr13 : ∀ a, μ13.writable a = μ.writable a := fun a => by rw [mwr, zwr, wr11]
  have rd13 : ∀ a, μ13.readable a = μ.readable a := fun a => by rw [mrd, zrd, rd11]
  have pay13 : ∀ q, ptr ≤ q → q < ptr + 192 → μ13.read q = μ.read q := fun q h1 h2 =>
    (mfr q (by omega) (by omega)).trans ((zfr q (by omega) (by omega)).trans (pay11 q h1 h2))
  -- the array, into S + 232
  obtain ⟨ω14, run14, y0, y1, y5, y6, y7, y8, y9⟩ :=
    c5 (p := p) (P := P) (R := R) x ω13 μ13 S (by omega) (m1.trans (z1.trans hc1))
  obtain ⟨ω15, μ15, run15, ⟨h0', h1', h5', h6', h7', hR0', hR8', hbuf, hfr, hrd', hwr'⟩⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω14 μ13 1126 24207 S rd (S + 232) (ptr + 64) (len - 64) 128 y0
      (y1.trans (m1.trans (z1.trans hc1))) (y7.trans (m6.trans (z6.trans hc6))) y8 y9
      (by decide) jte_562 bs_24207 ⟨by omega, by omega, hS.2⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr13]; exact hws a h1 (by omega))
      (fun a h1 h2 => by rw [wr13]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr13]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd13]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (by omega)).trans (zfr _ (by omega) (by omega)))]
          exact dR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (by omega)).trans (zfr _ (by omega) (by omega)))]
          exact dR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  have wr15 : ∀ a, μ15.writable a = μ.writable a := fun a => by rw [hwr', wr13]
  have rd15 : ∀ a, μ15.readable a = μ.readable a := fun a => by rw [hrd', rd13]
  -- the array, to S + 104
  obtain ⟨ω16, run16, c0', c1', c5', c6', c7', c8', c9'⟩ :=
    c6 (p := p) (P := P) (R := R) x ω15 μ15 S (by omega) (h1'.trans (y1.trans (m1.trans (z1.trans hc1)))) h7'
  obtain ⟨ω17, μ17, run17, l0, l1, l5, l6, lcp, lfr, lrd, lwr⟩ :=
    memcpy_big_aligned (p := p) (P := P) (R := R) x ω16 μ15 1128 24253 S (S + 104) (S + 232) 128 c0'
      (c1'.trans (h1'.trans (y1.trans (m1.trans (z1.trans hc1))))) c7' c8' c9'
      (by decide) jte_563 bs_24253 ⟨by omega, by omega, hS.2⟩ (by decide) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [rd15]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr15]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr15]; exact hws a (by omega) (by omega))
  -- the call of Option<Vec<u8>>::decode
  obtain ⟨ω18, run18, j0, j1, j5, j6, j7, j8⟩ :=
    c7 (p := p) (P := P) (R := R) x ω17 μ17 S (by omega)
      l1
  have h17_6 : ω17[6] = UInt64.ofNat rd := l6.trans (c6'.trans (h6'.trans (y6.trans (m6.trans (z6.trans hc6)))))
  have h18_6 : ω18[6] = UInt64.ofNat rd := j6.trans h17_6
  -- what survives to μ17
  have b17 : ∀ a, a < 4294967296 → (a < S - 88 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ17.read a = μ.read a := fun a h0 h1 h2 =>
    (lfr a h0 (by omega) (by omega)).trans ((hfr a h0 (by omega) h2 (by omega)).trans
      ((mfr a h0 (by omega)).trans ((zfr a h0 (by omega)).trans ((dfr a h0 (by omega) h2 (by omega)).trans
      ((bfr a h0 (by omega) (by omega)).trans ((afr a h0 (by omega) h2 (by omega)).trans
      ((wfr a h0 (by omega) (by omega)).trans ((ufr a h0 (by omega) h2 (by omega)).trans
      ((qfr a h0 (by omega) (by omega)).trans ((nfr a h0 (by omega) h2 (by omega)).trans
      ((kfr a h0 (by omega) (by omega)).trans ((gfr a h0 (by omega) h2 (by omega)).trans
      (ffr a h0 (by omega))))))))))))))
  -- the stack slots: from S + 40 to S + 104 and from S + 360 to S + 384, nothing after the parking
  have k17 : ∀ a, S + 40 ≤ a → a < S + 104 ∨ (S + 360 ≤ a ∧ a < S + 384) → μ17.read a = μ12.read a :=
    fun a h1 h2 => (lfr a (by omega) (by omega) (by omega)).trans ((hfr a (by omega) (by omega) (by omega)
      (by omega)).trans (mfr a (by omega) (by omega)))
  have k12 : ∀ a, S + 48 ≤ a → a < S + 104 ∨ (S + 360 ≤ a ∧ a < S + 384) → μ12.read a = μ10.read a :=
    fun a h1 h2 => (zfr a (by omega) (by omega)).trans (dfr a (by omega) (by omega) (by omega) (by omega))
  have k10 : ∀ a, S + 56 ≤ a → a < S + 104 ∨ (S + 360 ≤ a ∧ a < S + 384) → μ10.read a = μ8.read a :=
    fun a h1 h2 => (bfr a (by omega) (by omega) (by omega)).trans (afr a (by omega) (by omega) (by omega) (by omega))
  have k8 : ∀ a, S + 64 ≤ a → a < S + 104 ∨ (S + 360 ≤ a ∧ a < S + 384) → μ8.read a = μ6.read a :=
    fun a h1 h2 => (wfr a (by omega) (by omega) (by omega)).trans (ufr a (by omega) (by omega) (by omega) (by omega))
  have k6 : ∀ a, S + 72 ≤ a → a < S + 104 ∨ (S + 360 ≤ a ∧ a < S + 384) → μ6.read a = μ4.read a :=
    fun a h1 h2 => (qfr a (by omega) (by omega) (by omega)).trans (nfr a (by omega) (by omega) (by omega) (by omega))
  have k4 : ∀ a, S + 360 ≤ a → a < S + 384 → μ4.read a = μ2.read a :=
    fun a h1 h2 => (kfr a (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega) (by omega) (by omega))
  have kk : ∀ a, S + 360 ≤ a → a < S + 384 → μ17.read a = μ2.read a := fun a h1 h2 =>
    (k17 a (by omega) (Or.inr ⟨h1, h2⟩)).trans ((k12 a (by omega) (Or.inr ⟨h1, h2⟩)).trans
      ((k10 a (by omega) (Or.inr ⟨h1, h2⟩)).trans ((k8 a (by omega) (Or.inr ⟨h1, h2⟩)).trans
      ((k6 a (by omega) (Or.inr ⟨h1, h2⟩)).trans (k4 a h1 h2)))))
  refine ⟨ω18, μ17, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans
    (run16.trans (run17.trans run18))))))))))))))))).mono (by omega), j0, ?_, ?_, h18_6, j7, j8.trans h17_6,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b17,
    fun a => by rw [lrd, rd15], fun a => by rw [lwr, wr15]⟩
  · exact j1.trans l1
  · exact j5.trans (l5.trans (c5'.trans (h5'.trans (y5.trans (m5.trans (z5.trans hc5))))))
  · rw [Memory.readN_congr (fun j hj => kk _ (by omega) (by omega))]; exact f376
  · rw [Memory.readN_congr (fun j hj => kk _ (by omega) (by omega))]; exact f368
  · rw [Memory.readN_congr (fun j hj => kk _ (by omega) (by omega))]; exact f360
  · rw [Memory.readN_congr (fun j hj => (k17 _ (by omega) (Or.inl (by omega))).trans ((k12 _ (by omega)
      (Or.inl (by omega))).trans ((k10 _ (by omega) (Or.inl (by omega))).trans ((k8 _ (by omega)
      (Or.inl (by omega))).trans (k6 _ (by omega) (Or.inl (by omega)))))))]
    rw [khash, gbuf]
    exact Memory.readN_congr (fun j hj => pay2 _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => (k17 _ (by omega) (Or.inl (by omega))).trans ((k12 _ (by omega)
      (Or.inl (by omega))).trans ((k10 _ (by omega) (Or.inl (by omega))).trans (k8 _ (by omega)
      (Or.inl (by omega))))))]
    rw [qv, el]
  · rw [Memory.readN_congr (fun j hj => (k17 _ (by omega) (Or.inl (by omega))).trans ((k12 _ (by omega)
      (Or.inl (by omega))).trans (k10 _ (by omega) (Or.inl (by omega)))))]
    rw [wv, el]
  · rw [Memory.readN_congr (fun j hj => (k17 _ (by omega) (Or.inl (by omega))).trans (k12 _ (by omega)
      (Or.inl (by omega))))]
    rw [bv, el]
  · rw [Memory.readN_congr (fun j hj => k17 _ (by omega) (Or.inl (by omega)))]
    rw [zv, el]
  · rw [lcp, hbuf]
    exact Memory.readN_congr (fun j hj => pay13 _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => lfr _ (by omega) (by omega) (by omega))]
    exact hR0'.trans (congrArg (Num.encodeLE 8) (by omega))
  · rw [Memory.readN_congr (fun j hj => lfr _ (by omega) (by omega) (by omega))]
    exact hR8'.trans (congrArg (Num.encodeLE 8) (by omega))

/-- **`CreateService`'s end**, from the `Option<u32>` decoder's return (24372) with its tag τ ∈ {0, 1}
    (ω₇) and value v (ω₈): `c12`, the array's copy to O + 96 (`memcpy_big_aligned`) and `c13`. Memory
    changes only in S − 48 … S + 8 and O … O + 232. -/
theorem cs_end {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O τ v ret t v5 v6 : Nat) (hS : 65536 + 48 ≤ S ∧ S % 8 = 0 ∧ S + 440 < 4294967296)
    (hO : O % 8 = 0 ∧ O + 256 ≤ 4294967296) (hOS : O + 232 ≤ S - 48 ∨ S + 440 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (h7 : ω[7] = UInt64.ofNat τ) (hτ : τ = 0 ∨ τ = 1) (h8 : ω[8] = UInt64.ofNat v)
    (hv : v < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sr : μ.readN (S + 376) 8 = Num.encodeLE 8 934)
    (s0 : μ.readN (S + 432) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 424) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 416) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hws : ∀ a, S - 48 ≤ a → a < S + 8 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 232 → μ.writable a = true)
    (hrs : ∀ a, S ≤ a → a < S + 440 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24372 ω μ x t ω' μ' x 630 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = μ.readN (S + 32) 8 ∧ μ'.readN (O + 8) 8 = μ.readN (S + 24) 8 ∧
      μ'.readN (O + 16) 8 = μ.readN (S + 16) 8 ∧ μ'.readN (O + 24) 4 = Num.encodeLE 4 τ ∧
      μ'.readN (O + 28) 4 = Num.encodeLE 4 v ∧ μ'.readN (O + 32) 32 = μ.readN (S + 72) 32 ∧
      μ'.readN (O + 64) 8 = μ.readN (S + 64) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (S + 56) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (S + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (S + 40) 8 ∧
      μ'.readN (O + 96) 128 = μ.readN (S + 104) 128 ∧ μ'.readN (O + 224) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < S - 48 ∨ S + 8 ≤ a) → (a < O ∨ O + 232 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, aS, ahash, afr, ard, awr⟩ :=
    c12 (p := p) (P := P) (R := R) x ω μ S O τ v (by omega) (by omega) (by omega) h1 h5 h7 hτ h8 hv
      (fun a h1 h2 => hws a (by omega) h2) (fun a h1 h2 => hwO a (by omega) (by omega))
      (fun a h1 h2 => hrs a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bcp, bfr, brd, bwr⟩ :=
    memcpy_big_aligned (p := p) (P := P) (R := R) x ω1 μ1 1136 24426 S (O + 96) (S + 104) 128 a0
      (a1.trans h1) a7 a8 a9 (by decide) jte_567 bs_24426 ⟨by omega, by omega, hS.2.1⟩ (by decide) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [ard]; exact hrs a (by omega) (by omega))
      (fun a h1 h2 => by rw [awr]; exact hwO a (by omega) (by omega))
      (fun a h1 h2 => by rw [awr]; exact hws a (by omega) (by omega))
  have hτ2 : τ < 2 := by omega
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, cO, cO8, cO16, cO24, cO28, cO64, cO72, cO80, cO88, cO224, cfr, crd, cwr⟩ :=
    c13 (p := p) (P := P) (R := R) x ω2 μ2 S O τ ret t v5 v6 (by omega) (by omega) (by omega) b1
      (b5.trans (a5.trans h5)) (b6.trans a6) hτ2 hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => (bfr _ (by omega) (by omega) (by omega)).trans
          (afr _ (by omega) (by omega) (by omega)))]; exact sr)
      (by rw [Memory.readN_congr (fun j hj => (bfr _ (by omega) (by omega) (by omega)).trans
          (afr _ (by omega) (by omega) (by omega)))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => (bfr _ (by omega) (by omega) (by omega)).trans
          (afr _ (by omega) (by omega) (by omega)))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => (bfr _ (by omega) (by omega) (by omega)).trans
          (afr _ (by omega) (by omega) (by omega)))]; exact s6)
      hret hjt hbt (fun a h1 h2 => by rw [bwr, awr]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [brd, ard]; exact hrs a h1 h2)
  -- the stack from S + 8 to S + 440 is as it was, through c12 and the copy
  have k : ∀ a, S + 8 ≤ a → a < S + 440 → μ2.read a = μ.read a := fun a h1 h2 =>
    (bfr a (by omega) (by omega) (by omega)).trans (afr a (by omega) (by omega) (by omega))
  refine ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), c0, c1, c5, c6, ?_, ?_, ?_, cO24, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, fun a => by rw [crd, brd, ard], fun a => by rw [cwr, bwr, awr]⟩
  · rw [cO]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO8]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO16]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO28, ← readN_take _ _ 8 4 (by decide),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega)), aS, take_encodeLE]
  · rw [Memory.readN_congr (fun j hj => (cfr _ (by omega) (by omega) (by omega) (by omega)).trans
      (bfr _ (by omega) (by omega) (by omega))), ahash]
  · rw [cO64]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO72]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO80]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [cO88]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)), bcp]
    exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega) (by omega))
  · rw [cO224]; exact Memory.readN_congr (fun j hj => k _ (by omega) (by omega))
  · intro a h0 h1 h2
    rw [cfr a h0 (by omega) (by omega) (by omega), bfr a h0 (by omega) (by omega)]
    exact afr a h0 (by omega) (by omega)

/-- **`CreateService` from its `Option<Vec<u8>>`'s return** (24265): the option's three words W (not
    the error 2^64 − 2), w₁, w₂ in the slot S + 232, the reader `{ptr, len}` at rd holding the 8 octets of
    the `u64` u₅ and then the `Option<u32>` ou ([0], or 1 :: u with u 4 octets): the decoder stores
    `CreateService` into O (see the module doc) and returns through its frame at A = S + 384. Memory
    changes only in S − 120 … A, the reader and O … O + 232. -/
theorem cs_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 rd ptr len W w1 w2 : Nat) (ou : List UInt8)
    (hS : 65536 + 120 ≤ S ∧ S % 8 = 0 ∧ S + 440 < 4294967296)
    (hO : O % 8 = 0 ∧ O + 256 ≤ 4294967296) (hOS : O + 232 ≤ S - 120 ∨ S + 440 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat rd)
    (hW : W < 18446744073709551616) (hW' : W ≠ 18446744073709551614) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616)
    (sW : μ.readN (S + 232) 8 = Num.encodeLE 8 W) (s1 : μ.readN (S + 240) 8 = Num.encodeLE 8 w1)
    (s2 : μ.readN (S + 248) 8 = Num.encodeLE 8 w2)
    (sr : μ.readN (S + 376) 8 = Num.encodeLE 8 934)
    (s0 : μ.readN (S + 432) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 424) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 416) 8 = Num.encodeLE 8 v6) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hou : ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u)
    (hlen : 8 + ou.length ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (pay : μ.readN (ptr + 8) ou.length = ou)
    (hrdS : rd + 16 ≤ S - 120 ∨ S + 440 ≤ rd) (hpS : ptr + 32 ≤ S - 120 ∨ S + 440 ≤ ptr)
    (hOr : O + 232 ≤ rd ∨ rd + 16 ≤ O) (hpr : ptr + 13 ≤ rd ∨ rd + 16 ≤ ptr)
    (hws : ∀ a, S - 120 ≤ a → a < S + 384 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 232 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 8 + ou.length → μ.readable a = true)
    (hrs : ∀ a, S + 384 ≤ a → a < S + 440 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24265 ω μ x t ω' μ' x 960 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 W ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 w2 ∧
      μ'.readN (O + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat ∧
      (ou.headD 0 = 1 → μ'.readN (O + 28) 4 = ou.tail) ∧
      μ'.readN (O + 32) 32 = μ.readN (S + 72) 32 ∧
      μ'.readN (O + 64) 8 = μ.readN (S + 64) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (S + 56) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (S + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (S + 40) 8 ∧
      μ'.readN (O + 96) 128 = μ.readN (S + 104) 128 ∧ μ'.readN (O + 224) 8 = μ.readN ptr 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 8 + ou.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 8 - ou.length) ∧
      (∀ a, a < 4294967296 → (a < S - 120 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hrs' : ∀ a, S - 120 ≤ a → a < S + 440 → μ.readable a = true := fun a h1 h2 => by
    rcases Nat.lt_or_ge a (S + 384) with h | h
    · exact Memory.readable_of_writable (hws a h1 h)
    · exact hrs a h h2
  have hol : 1 ≤ ou.length ∧ ou.length ≤ 5 := by rcases hou with rfl | ⟨u, hu, rfl⟩ <;> simp [*]
  -- the option's words parked; the u64 reader's call
  obtain ⟨ω1, μ1, run1, f0, f1, f5, f6, f7, fW, f1', f2', ffr, frd, fwr⟩ :=
    c8 (p := p) (P := P) (R := R) x ω μ S W w1 w2 (by omega) h1 hW hW' hw1 hw2 sW s1 s2
      (fun a h1 h2 => hws a (by omega) (by omega)) (fun a h1 h2 => hrs' a (by omega) (by omega))
  -- u₅
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, g7, g8, gR0, gR8, gfr, grd, gwr⟩ :=
    Fixed.read_u64 (p := p) (P := P) (R := R) x ω1 μ1 S 1132 24322 rd ptr len ⟨by omega, by omega⟩ f0
      (f1.trans h1) (f7.trans h6) (by decide) jte_565 bs_24322 hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
  have hv8 := decodeLE_lt (μ1.readN ptr 8)
  simp only [Memory.length_readN] at hv8
  have pay1 : ∀ q, ptr ≤ q → q < ptr + 8 + ou.length → μ1.read q = μ.read q := fun q h1 h2 =>
    ffr q (by omega) (by omega)
  -- the Option<u32>'s frame and its tag's read
  obtain ⟨ω3, μ3, run3, k0, k1, k5, k6, k7, k8, k9, k8', kr, kO, krd', kfr, krd, kwr⟩ :=
    c9 (p := p) (P := P) (R := R) x ω2 μ2 S O rd (Num.decodeLE (μ1.readN ptr 8)) ⟨by omega, by omega⟩ g1
      (g5.trans (f5.trans h5)) (g6.trans (f6.trans h6)) g7 g8 hO64 hrd64 (by simpa using hv8)
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [kwr, gwr, fwr]
  have rd3 : ∀ a, μ3.readable a = μ.readable a := fun a => by rw [krd, grd, frd]
  have pay3 : ∀ q, ptr ≤ q → q < ptr + 8 + ou.length → μ3.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega) (by omega)).trans ((gfr q (by omega) (by omega) (by omega)).trans (pay1 q h1 h2))
  obtain ⟨ω4, μ4, run4, ⟨m0, m1, -, -, -, m5, m6, -, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1688 36095 (S - 32) rd (S - 29) (ptr + 8) (len - 8) 1 k0 k1
      k7 k8 k9 (by decide) jte_843 bs_36095 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr3]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [mwr, wr3]
  have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [mrd, rd3]
  have htag : μ4.read (S - 32 + 3) = ou.headD 0 := by
    rw [show S - 32 + 3 = S - 29 by omega, LookedUp.read_of_readN1 mbuf, pay3 _ (by omega) (by omega)]
    have := Services.Bootstrap.Decode.Loop.read_head _ _ _ _ pay (by omega)
    rw [this]
  have hsv : ∀ a, S - 24 ≤ a → a < S → μ4.read a = μ3.read a := fun a h1 h2 =>
    mfr a (by omega) (by omega) (by omega) (by omega)
  have kr4 : μ4.readN (S - 32 + 24) 8 = Num.encodeLE 8 1134 := by
    rw [show S - 32 + 24 = S - 8 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact kr
  have kO4 : μ4.readN (S - 32 + 16) 8 = Num.encodeLE 8 O := by
    rw [show S - 32 + 16 = S - 16 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact kO
  have kd4 : μ4.readN (S - 32 + 8) 8 = Num.encodeLE 8 rd := by
    rw [show S - 32 + 8 = S - 24 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact krd'
  -- the Option<u32>: to 24372 with its tag τ and value v
  obtain ⟨ω5, μ5, τ, v, run5, e1, e5, e7, e8, hτ, hv, eτ, ev, eR0, eR8, efr, erd, ewr⟩ :
      ∃ ω5 μ5 τ v, FreeStepsH p R 36095 ω4 μ4 x 24372 ω5 μ5 x 120 ∧ ω5[1] = UInt64.ofNat S ∧
        ω5[5] = UInt64.ofNat O ∧ ω5[7] = UInt64.ofNat τ ∧ ω5[8] = UInt64.ofNat v ∧ (τ = 0 ∨ τ = 1) ∧
        v < 18446744073709551616 ∧ τ = (ou.headD 0).toNat ∧ (ou.headD 0 = 1 → Num.encodeLE 4 v = ou.tail) ∧
        μ5.readN rd 8 = Num.encodeLE 8 (ptr + 8 + ou.length) ∧
        μ5.readN (rd + 8) 8 = Num.encodeLE 8 (len - 8 - ou.length) ∧
        (∀ a, a < 4294967296 → (a < S - 120 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ4.read a) ∧
        (∀ a, μ5.readable a = μ4.readable a) ∧ (∀ a, μ5.writable a = μ4.writable a) := by
    rcases hou with rfl | ⟨u, hu, rfl⟩
    · obtain ⟨ω5, run5, e0, e1, e5, e6, e7, e8⟩ :=
        c10n (p := p) (P := P) (R := R) x ω4 μ4 (S - 32) O rd ⟨by omega, by omega⟩ (m1.trans k1) (m6.trans k6)
          m7 hO64 hrd64 (by simpa using htag) kr4 kO4 kd4
          (fun a h1 h2 => by rw [rd4]; exact hrs' a (by omega) (by omega))
      refine ⟨ω5, μ4, 0, (ω4[8]).toNat, run5.mono (by omega), by rw [e1]; congr 1; omega, e5, e7,
        by rw [e8, UInt64.ofNat_toNat], Or.inl rfl, UInt64.toNat_lt _, rfl, by simp, ?_, ?_,
        fun a _ _ _ => rfl, fun a => rfl, fun a => rfl⟩
      · simp only [List.length_singleton]; exact mR0
      · simp only [List.length_singleton]; rw [mR8]; try (congr 1; omega)
    · have hb := (htag.trans (by simp : (1 :: u).headD 0 = 1))
      obtain ⟨ω5, μ5, run5, n0, n1, n5, n6, n7, n8, n9, nfr, nrd, nwr⟩ :=
        c10s (p := p) (P := P) (R := R) x ω4 μ4 (S - 32) ⟨by omega, by omega⟩ (m1.trans k1) (m6.trans k6) m7 hb
          (by rw [rd4]; exact hrs' _ (by omega) (by omega))
          (fun a h1 h2 => by rw [wr4]; exact hws a (by omega) (by omega))
      obtain ⟨ω6, μ6, run6, ⟨q0, q1, -, -, -, q5, q6, -, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩⟩ :=
        read_ok (p := p) (P := P) (R := R) x ω5 μ5 1690 36127 (S - 32) rd (S - 32 + 4) (ptr + 8 + 1)
          (len - 8 - 1) 4 n0 (n1.trans (m1.trans k1)) (n7.trans (m5.trans k5)) n8 n9 (by decide)
          jte_844 bs_36127 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
          (by decide) (by simp only [List.length_cons, hu] at hlen; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)
          (fun a h1 h2 => by rw [nwr, wr4]; exact hws a (by omega) (by omega))
          (fun a h1 h2 => by rw [nwr, wr4]; exact hwr a h1 h2)
          (fun a h1 h2 => by rw [nwr, wr4]; exact hws a (by omega) (by omega))
          (fun a h1 h2 => by rw [nrd, rd4]; exact hrp a (by omega) (by simp; omega))
          (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega))]; exact mR0)
          (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega))]; exact mR8)
      have hu4 : μ5.readN (ptr + 8 + 1) 4 = u := by
        rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega)).trans ((mfr _ (by omega) (by omega)
          (by omega) (by omega)).trans (pay3 _ (by omega) (by simp; omega))))]
        have := Services.Bootstrap.Decode.Loop.readN_sub μ (ptr + 8) 5 1 4 _ (by simpa [hu] using pay) (by decide)
        simpa [hu, Nat.add_assoc, List.take_of_length_le (Nat.le_of_eq hu)] using this
      have hd := decodeLE_lt u
      have he := encodeLE_decodeLE u
      rw [hu] at hd he
      have hsv' : ∀ a, S - 32 + 8 ≤ a → a < S → μ6.read a = μ4.read a := fun a h1 h2 =>
        (qfr a (by omega) (by omega) (by omega) (by omega)).trans (nfr a (by omega) (by omega))
      obtain ⟨ω7, run7, c0, c1, c5, c6, c7, c8'⟩ :=
        c11 (p := p) (P := P) (R := R) x ω6 μ6 (S - 32) O rd (Num.decodeLE u) ⟨by omega, by omega⟩
          (q1.trans (n1.trans (m1.trans k1))) q7 hO64 hrd64 (by simpa using hd)
          (by rw [qbuf, hu4, he])
          (by rw [Memory.readN_congr (fun j hj => hsv' _ (by omega) (by omega))]; exact kr4)
          (by rw [Memory.readN_congr (fun j hj => hsv' _ (by omega) (by omega))]; exact kO4)
          (by rw [Memory.readN_congr (fun j hj => hsv' _ (by omega) (by omega))]; exact kd4)
          (fun a h1 h2 => by rw [qrd, nrd, rd4]; exact hrs' a (by omega) (by omega))
      refine ⟨ω7, μ6, 1, (UInt64.ofNat (sxw 4 (Num.decodeLE u))).toNat, (run5.trans (run6.trans run7)).mono
        (by omega), by rw [c1]; congr 1; omega, c5, c7, by rw [c8', UInt64.ofNat_toNat], Or.inr rfl,
        UInt64.toNat_lt _, by simp, fun _ => ?_, ?_, ?_, fun a h0 h1 h2 => ?_,
        fun a => by rw [qrd, nrd], fun a => by rw [qwr, nwr]⟩
      · simp only [List.tail_cons]
        rw [UInt64.toNat_ofNat']
        exact (encodeLE4_sxw _ (by simpa using hd)).trans he
      · simp only [List.length_cons, hu]; rw [qR0]; try exact congrArg _ (by omega)
      · simp only [List.length_cons, hu]; rw [qR8]; try exact congrArg _ (by omega)
      · rw [qfr a h0 (by omega) h2 (by omega)]; exact nfr a h0 (by omega)
  -- the end
  have b5 : ∀ a, S + 16 ≤ a → a < S + 440 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (efr a (by omega) (by omega) (by omega)).trans ((mfr a (by omega) (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega)))
  have b2 : ∀ a, S + 40 ≤ a → a < S + 440 → μ2.read a = μ.read a := fun a h1 h2 =>
    (gfr a (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, c0, c1, c5, c6, cO, cO8, cO16, cO24, cO28, cO32, cO64, cO72, cO80, cO88, cO96, cO224,
      cfr, crd, cwr⟩ :=
    cs_end (p := p) (P := P) (R := R) x ω5 μ5 S O τ v ret t v5 v6 ⟨by omega, hS.2.1, hS.2.2⟩ hO (by omega) e1 e5
      e7 hτ e8 hv hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))]; exact sr)
      (by rw [Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))]; exact s6)
      hret hjt hbt (fun a h1 h2 => by rw [ewr, wr4]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [ewr, wr4]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [erd, rd4]; exact hrs' a (by omega) h2)
  have b1 : ∀ a, S + 16 ≤ a → a < S + 40 → μ2.read a = μ1.read a := fun a h1 h2 =>
    gfr a (by omega) (by omega) (by omega)
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    c0, c1, c5, c6, ?_, ?_, ?_, by rw [cO24, eτ], fun h => by rw [cO28]; exact ev h, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun a => by rw [crd, erd, rd4], fun a => by rw [cwr, ewr, wr4]⟩
  · rw [cO, Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b1 _ (by omega) (by omega)))]
    exact fW
  · rw [cO8, Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b1 _ (by omega) (by omega)))]
    exact f1'
  · rw [cO16, Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b1 _ (by omega) (by omega)))]
    exact f2'
  · rw [cO32]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO64]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO72]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO80]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO88]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO96]; exact Memory.readN_congr (fun j hj => (b5 _ (by omega) (by omega)).trans (b2 _ (by omega) (by omega)))
  · rw [cO224, Memory.readN_congr (fun j hj => (efr _ (by omega) (by omega) (by omega)).trans
      ((mfr _ (by omega) (by omega) (by omega) (by omega)))), k8']
    have := encodeLE_decodeLE (μ1.readN ptr 8)
    simp only [Memory.length_readN] at this
    rw [this]
    exact Memory.readN_congr (fun j hj => pay1 _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega))]; exact eR0
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega))]; exact eR8
  · intro a h0 h1 h2 h3
    rw [cfr a h0 (by omega) h3, efr a h0 (by omega) h2, mfr a h0 (by omega) h2 (by omega),
      kfr a h0 (by omega) (by omega), gfr a h0 (by omega) h2]
    exact ffr a h0 (by omega)

/-- **`CreateService` with `Option<Vec<u8>>` = `None`**: from 20626, with tag 0 read without error and
    the reader `{ptr, len}` at rd (ω₆) holding the 192 octets of h, u₁ … u₄ and the array, the octet 0
    (`None`), the 8 of u₅ and the `Option<u32>` ou ([0], or 1 :: u with u 4 octets),
    `Instruction::decode` returns `CreateService` in its slot O: the niche word 2^64 − 1 at O, ou's tag
    as a `u32` at O + 24 (and, for `Some`, u at O + 28), h at O + 32, the `u64`s at O + 64 … O + 96, the
    array at O + 96 and u₅ at O + 224. The reader is advanced past all of it. Memory changes only in
    S − 144 … A (A = S + 384, the decoder's frame and its callees'), the reader and O … O + 232. -/
theorem create_service_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 rd ptr len : Nat) (ou : List UInt8) (F : Frame P (S + 384) O ret t v5 v6 ω μ)
    (hS : 65536 + 144 ≤ S ∧ S % 8 = 0) (hO8 : O % 8 = 0 ∧ O + 256 ≤ 4294967296) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (S + 384) = 0) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 240 < 4294967296)
    (hou : ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u)
    (hlen : 201 + ou.length ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hnone : μ.read (ptr + 192) = 0) (pay : μ.readN (ptr + 201) ou.length = ou)
    (hrdS : rd + 16 ≤ S - 144 ∨ S + 440 ≤ rd) (hpS : ptr + 240 ≤ S - 144 ∨ S + 440 ≤ ptr)
    (hOS : O + 232 ≤ S - 144 ∨ S + 440 ≤ O) (hOr : O + 232 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 206 ≤ rd ∨ rd + 16 ≤ ptr)
    (hws : ∀ a, S - 144 ≤ a → a < S + 384 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 232 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 201 + ou.length → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 3700 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 18446744073709551615 ∧
      μ'.readN (O + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat ∧
      (ou.headD 0 = 1 → μ'.readN (O + 28) 4 = ou.tail) ∧
      μ'.readN (O + 32) 32 = μ.readN ptr 32 ∧
      μ'.readN (O + 64) 8 = μ.readN (ptr + 32) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (ptr + 40) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (ptr + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (ptr + 56) 8 ∧
      μ'.readN (O + 96) 128 = μ.readN (ptr + 64) 128 ∧ μ'.readN (O + 224) 8 = μ.readN (ptr + 193) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 201 + ou.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 201 - ou.length) ∧
      (∀ a, a < 4294967296 → (a < S - 144 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hol : 1 ≤ ou.length ∧ ou.length ≤ 5 := by rcases hou with rfl | ⟨u, hu, rfl⟩ <;> simp [*]
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a376, a368, a360, ahash, a64, a56, a48, a40, aarr, aR0, aR8,
      afr, ard, awr⟩ :=
    cs_head (p := p) (P := P) (R := R) x ω μ S O ret t v5 v6 rd ptr len F ⟨by omega, hS.2⟩ h6 h7 tag tab hrt hrd
      ⟨hptr.1, by omega⟩ ⟨by omega, hlen.2⟩ hR0 hR8 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hws a (by omega) h2) hwr (fun a h1 h2 => hrp a h1 (by omega))
  have wr1 : ∀ a, S - 144 ≤ a → a < S + 384 → μ1.writable a = true := fun a h1 h2 => by rw [awr]; exact hws a h1 h2
  -- Option<Vec<u8>>::decode: its frame, the tag octet, None
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    LookedUp.o1 (p := p) (P := P) (R := R) x ω1 μ1 S (S + 232) rd 1130 O rd ⟨by omega, by omega⟩ (by omega)
      hrd64 (by omega) hO64 hrd64 a0 a1 a5 a6 a7 a8 (fun a h1 h2 => wr1 a (by omega) (by omega))
  obtain ⟨ω3, μ3, run3, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1682 35970 (S - 56) rd (S - 25) (ptr + 192) (len - 192) 1 g0 g1
      g7 g8 g9 (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact wr1 a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, awr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact wr1 a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd, ard]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact aR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact aR8)
  have hp3 : ∀ q, ptr ≤ q → q < ptr + 201 + ou.length → μ3.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega) (by omega) (by omega)).trans ((gfr q (by omega) (by omega)).trans
      (afr q (by omega) (by omega) (by omega)))
  have htag : μ3.read (S - 56 + 31) = 0 := by
    rw [show S - 56 + 31 = S - 25 by omega, LookedUp.read_of_readN1 kbuf, ← hnone]
    exact (gfr _ (by omega) (by omega)).trans (afr _ (by omega) (by omega) (by omega))
  have hfr3 : ∀ a, S - 56 ≤ a → a < S → a ≠ S - 25 → μ3.read a = μ2.read a :=
    fun a h1 h2 h3 => kfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω4, run4, m0, m1, m5, m6⟩ := LookedUp.o_none (p := p) (P := P) (R := R) x ω3 μ3 (S - 56) (S + 232) 1130
    24265 O rd ⟨by omega, by omega⟩ (by omega) (by omega) (by rw [k1', g1]) (by rw [k5, g5]) k7 hO64 hrd64 htag
    (by rw [Memory.readN_congr (fun j hj => hfr3 _ (by omega) (by omega) (by omega)), show S - 56 + 48 = S - 8 by omega]; exact gs0)
    (by rw [Memory.readN_congr (fun j hj => hfr3 _ (by omega) (by omega) (by omega)), show S - 56 + 40 = S - 16 by omega]; exact gs5)
    (by rw [Memory.readN_congr (fun j hj => hfr3 _ (by omega) (by omega) (by omega)), show S - 56 + 32 = S - 24 by omega]; exact gs6)
    (by decide) jte_564 bs_24265
    (fun a h1 h2 => by rw [krd, grd, ard]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [kwr, gwr, awr]; exact hws a (by omega) (by omega))
  generalize hμ4 : μ3.writeN (S + 232) (Num.encodeLE 8 18446744073709551615) = μ4 at run4
  have w4 : ∀ a, a < 4294967296 → (a < S + 232 ∨ S + 240 ≤ a) → μ4.read a = μ3.read a := fun a h1 h2 => by
    rw [← hμ4]; exact Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [← hμ4, Memory.readable_writeN, krd, grd, ard]
  have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [← hμ4, Memory.writable_writeN, kwr, gwr, awr]
  -- μ4 against μ1, and against μ
  have bk : ∀ a, a < 4294967296 → (a < S - 144 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < S + 232 ∨ S + 240 ≤ a) →
      μ4.read a = μ1.read a := fun a h0 h1 h2 h3 =>
    (w4 a h0 h3).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have bS : ∀ a, S + 40 ≤ a → a < S + 440 → (a < S + 232 ∨ S + 360 ≤ a) → μ4.read a = μ1.read a :=
    fun a h1 h2 h3 => bk a (by omega) (by omega) (by omega) (by omega)
  have b0 : ∀ a, a < 4294967296 → (a < S - 144 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ4.read a = μ.read a :=
    fun a h0 h1 h2 => (bk a h0 (by omega) h2 (by omega)).trans (afr a h0 (by omega) h2)
  obtain ⟨ω5, μ5, run5, n0, n1, n5, n6, nO, -, -, nO24, nO28, nO32, nO64, nO72, nO80, nO88, nO96, nO224,
      nR0, nR8, nfr, nrd, nwr⟩ :=
    cs_tail (p := p) (P := P) (R := R) x ω4 μ4 S O ret t v5 v6 rd (ptr + 193) (len - 193) 18446744073709551615
      (rdN μ4 (S + 240) 8) (rdN μ4 (S + 248) 8) ou ⟨by omega, hS.2, by omega⟩ hO8 (by omega)
      (by rw [m1]; congr 1; omega) m5 m6 (by decide) (by decide) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (by rw [← hμ4]; exact Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]; try omega))
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a376)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hv5 F.hv6 F.hret F.hjt F.hbt hrd ⟨by omega, by omega⟩ hou ⟨by omega, by omega⟩
      (by rw [← hμ4, Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
          exact kR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [← hμ4, Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
          exact kR8.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => (w4 _ (by omega) (by omega)).trans (hp3 _ (by omega) (by omega)))]
          rw [show ptr + 193 + 8 = ptr + 201 by omega]; exact pay)
      (by omega) (by omega) hOr (by omega)
      (fun a h1 h2 => by rw [wr4]; exact hws a (by omega) h2)
      (fun a h1 h2 => by rw [wr4]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr4]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [rd4]; exact hrp a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd4]; exact F.hr a (by omega) (by omega))
  refine ⟨ω5, μ5, (run1.trans (run2.trans (run3.trans (run4.trans run5)))).mono (by omega), n0, n1, n5, n6, nO,
    nO24, nO28, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 h3 => ?_,
    fun a => by rw [nrd, rd4], fun a => by rw [nwr, wr4]⟩
  · rw [nO32, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact ahash
  · rw [nO64, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a64
  · rw [nO72, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a56
  · rw [nO80, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a48
  · rw [nO88, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a40
  · rw [nO96, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact aarr
  · rw [nO224]; exact Memory.readN_congr (fun j hj => (w4 _ (by omega) (by omega)).trans (hp3 _ (by omega) (by omega)))
  · rw [nR0]; try exact congrArg _ (by omega)
  · rw [nR8]; try exact congrArg _ (by omega)
  · rw [nfr a h0 (by omega) h2 h3]; exact b0 a h0 h1 h2

end Services.Bootstrap.Decode.CreateService
