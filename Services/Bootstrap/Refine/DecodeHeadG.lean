import Services.Bootstrap.Refine.DecodeTail

/-!
# `Instructions::decode`'s head for every instruction count

`DecodeTail.head` with the compact length of any n < 2³² (GP v0.8.0 Appendix C, the general natural encoding
ℰ(n), one to five octets), via the general `decodeU32` in place of `decodeU32_len1`. GP v0.8.0 Appendix B.4
(Ψ_R running bootstrap's code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeTail

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Instructions::decode`'s head, any n < 2³²** (4792 … 482): refine's reader over the payload's copy (q, Ly),
    its first |ℰ(n)| octets ℰ(n); the length decoded (`decodeU32`), and `Vec<Instruction>::decode` called (return
    922 → 20420) with the output at G = M − 136, the reader at M + 272 (now past ℰ(n)) and n. Memory changes only
    at [G − 128, G), [M − 24, M) and the reader. -/
theorem headG {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M q Ly r5 n : Nat)
    (hM : 65536 + 264 ≤ M ∧ M + 296 ≤ 4294967296 ∧ M % 8 = 0) (hq : 65536 ≤ q ∧ q + 32 + 128 ≤ M - 136)
    (hLy : Ly < 4294967296) (hr5 : r5 < 18446744073709551616) (hn : n < 4294967296)
    (hlen : (Blob.encodeNat n).length ≤ Ly)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat r5) (h6 : ω[6] = UInt64.ofNat Ly)
    (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q)
    (henc : μ.readN q (Blob.encodeNat n).length = Blob.encodeNat n)
    (hrq : ∀ a, q ≤ a → a < q + (Blob.encodeNat n).length → μ.readable a = true)
    (hw : ∀ a, M - 264 ≤ a → a < M + 288 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 4792 ω μ x 482 ω' μ' x 600 ∧ ω'[0] = UInt64.ofNat 922 ∧
      ω'[1] = UInt64.ofNat (M - 136) ∧ ω'[5] = UInt64.ofNat (M + 168) ∧ ω'[6] = UInt64.ofNat (M + 272) ∧
      ω'[7] = UInt64.ofNat (M - 136) ∧ ω'[8] = UInt64.ofNat (M + 272) ∧ ω'[9] = UInt64.ofNat n ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 (q + (Blob.encodeNat n).length) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (Ly - (Blob.encodeNat n).length) ∧
      μ'.readN (M - 136 + 128) 8 = Num.encodeLE 8 158 ∧ μ'.readN (M - 136 + 120) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (M - 136 + 112) 8 = Num.encodeLE 8 Ly ∧
      (∀ a, a < 4294967296 → (a < M - 264 ∨ M ≤ a) → (a < M + 272 ∨ M + 288 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨-, hw5⟩ := encodeNat_len_le5 n hn
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a272, a280, a128, a120, a112, afr, ard, awr⟩ := dh1 (p := p) (P := P)
    (R := R) x ω μ M q Ly r5 ⟨by omega, by omega, hM8⟩ (by omega) (by omega) hr5 h1 h5 h6 s112
    (fun a h1 h2 => Memory.readable_of_writable (hw a (by omega) (by omega))) (fun a h1 h2 => hw a (by omega) (by omega))
    (fun a h1 h2 => hw a (by omega) (by omega))
  have henc1 : μ1.readN q (Blob.encodeNat n).length = Blob.encodeNat n := by
    rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]; exact henc
  obtain ⟨ω2, μ2, run2, b0, b1, -, -, -, b5, b6, -, b7, b8, bR0, bR8, bfr, brd, bwr⟩ := decodeU32 (p := p)
    (P := P) (R := R) x ω1 μ1 920 20398 (M - 136) (M + 272) q Ly a0 a1 a7 ⟨by decide, by decide, by decide⟩
    jte_459 bs_20398 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (fun a h1 h2 => by rw [awr]; exact hw a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact hw a (by omega) (by omega))
    a272 a280 n hn ⟨hlen, hLy⟩ (fun a h1 h2 => by rw [ard]; exact hrq a h1 h2) henc1
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8, c9⟩ := dh2 (p := p) (P := P) (R := R) x ω2 μ2 (M - 136) (M + 272) n
    hn (by omega) (by omega) (b1.trans a1) (b6.trans a6) b7 b8
  have k2 : ∀ a l, a + l ≤ 4294967296 → M - 136 ≤ a → a + l ≤ M → μ2.readN a l = μ1.readN a l :=
    fun a l h h0 h' => Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), c0, by rw [c1, b1, a1], by rw [c5, b5, a5],
    by rw [c6, b6, a6], c7, c8, c9, bR0, bR8, by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a128,
    by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a120,
    by rw [k2 _ _ (by omega) (by omega) (by omega)]; exact a112, fun a h0 h h' => ?_,
    fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
  rw [bfr a h0 (by omega) (by omega), afr a h0 (by omega) h']

end Services.Bootstrap.Refine.DecodeTail
