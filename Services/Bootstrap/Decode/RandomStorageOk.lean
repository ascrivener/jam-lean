import Services.Bootstrap.Decode.RandomStorage
import Services.Bootstrap.Decode.VecHash32
import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.DecodeU32

/-!
# `Instruction::decode` of `RandomStorageAccumulate(Ok(v))`, the hashes in the heap

`RandomStorageAccumulate` (tag 22; GP v0.8.0 B.7, the bootstrap service's instruction list) holds a
`Result<Vec<[u8; 32]>, ()>`. With the result's tag octet 0 (`Ok`), its decoder (after the prologue of
`RandomStorage.random_storage_err`: the 56-octet frame at F = A − 56, the tag octet read into F + 8)
decodes the length n (ℰ, `decodeU32` at 31894), calls the hash reader (907) for n elements into the
slot F + 8, checks the `Vec`'s capacity word against the `Err` niche 2^64 − 1, copies the three words
`{cap, ptr, len}` from F + 8 to its result slot A and returns; `Instruction::decode` then copies the
three words at A to O + 8 after the discriminant word 2^63 + 21 at O.

* `random_storage_ok_heap`: with 1 ≤ n ≤ 512 hashes, through `VecHash32.vec_hash32_heap`. The encoding
  lies inside an allocated chunk, the allocator's context is `HeapCtx`, and the model's `alloc`
  failing is an outcome (null at the `alloc` wrapper's return, 40611).
* `random_storage_ok_elem`: the same, as an element of the decode loop (`ElemOkAF`) at a frame base F
  with `Lay F RD`.
-/

namespace Services.Bootstrap.Decode.RandomStorage

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 35823 … 35844: the tag read succeeded (ω₇ = 0) and is 0 (`Ok`): the decoder calls `decodeU32`
    (31894) on the reader (ω₇ = ω₆) for the length, return address 1678 (ω₅ = 2^64 − 2, the error
    word kept for the error paths). -/
theorem r_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0) (tag : μ.read (F + 8) = 0)
    (hr : μ.readable (F + 8) = true) :
    ∃ ω', FreeStepsH p R 35823 ω μ x 31894 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 1678 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat 18446744073709551614 ∧
      ω'[6] = ω[6] ∧ ω'[7] = ω[6] := by
  have rb : rdN μ (F + 8) 1 = 0 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hr, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 35850 … 35867: the length n < 2^32 was decoded (ω₇ = 0, ω₈ = n): the hash reader (907) is called
    for n elements into the slot F + 8 (ω₇ = F + 8, ω₈ = the reader ω₆, ω₉ = n), return address
    1680. -/
theorem r_call {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F n : Nat) (hF : F + 8 < 4294967296) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 35850 ω μ x 907 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 1680 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (F + 8) ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h8, hF, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 35874 … 35912: the hash reader returned a `Vec` `{w₀, w₁, w₂}` at F + 8 whose capacity w₀ is not the
    `Err` niche 2^64 − 1: the decoder copies the three words to its result slot A (read from F) and
    returns, restoring ω₀, ω₅, ω₆ from F + 48, F + 40, F + 32. -/
theorem r_fin {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F A w0 w1 w2 ret t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (hA : A + 24 ≤ 4294967296) (hAF : A + 24 ≤ F ∨ F + 56 ≤ A)
    (h1 : ω[1] = UInt64.ofNat F)
    (hw0 : w0 < 18446744073709551615) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 w0) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 w1)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 w2) (sA : μ.readN F 8 = Num.encodeLE 8 A)
    (s0 : μ.readN (F + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (F + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, F ≤ a → a < F + 56 → μ.readable a = true)
    (hw : ∀ a, A ≤ a → a < A + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35874 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN A 8 = Num.encodeLE 8 w0 ∧ μ'.readN (A + 8) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (A + 16) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < A ∨ A + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r8 := rd8 (by omega) s8
  have r16 := rd8 hw1 s16
  have r24 := rd8 hw2 s24
  have rA := rd8 (by omega) sA
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  have hc : ¬ w0 = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hF, hA, hAF, hw, hr, r8, r16, r24, rA, r0, r5, r6, hc, hret, hjt, hbt, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA in
/-- **`RandomStorageAccumulate(Ok(v))` with 1 ≤ n ≤ 512 hashes, the payload in the heap** (GP v0.8.0
    B.7, tag 22): from 20626, with tag 22 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding 0 (`Ok`), ℰ(n) (w octets) and n hashes (32n octets), all inside an allocated chunk of the
    allocator's state `s` (context `HeapCtx`, under `refineContractK cap`), either the model's `alloc`
    of ⌈32n/32⌉ = n units gives `(q, s')` and `Instruction::decode` returns
    `RandomStorageAccumulate(Ok(v))` in O (the discriminant word 2^63 + 21, the `Vec` `{cap n, ptr q,
    len n}` at O + 8, the 32n octets of the hashes at q), the reader advanced by 1 + w + 32n, the
    context kept for `s'`, every allocated chunk of `s` kept with its data; or the model's `alloc` fails
    and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem random_storage_ok_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 22) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 416 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484064 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 512)
    (hlen : 1 + (Blob.encodeNat n).length + 32 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + 32 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hok : μ.read ptr = 0) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((32 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (550 * n + 2000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775829 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (32 * n) = μ.readN (ptr + 1 + (Blob.encodeNat n).length) (32 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1 + (Blob.encodeNat n).length + 32 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1 - (Blob.encodeNat n).length - 32 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (32 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (32 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((32 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (550 * n + 2000) ∧
      ω'[7] = UInt64.ofNat 0) := by
  have hA2 := F.hA
  have hst := H.st
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen henc hpay hw1 ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hra : ∀ a, ptr ≤ a → a < ptr + 1 + w + 32 * n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  have hws : ∀ a, A - 416 ≤ a → a < A + 56 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  -- the prologue, as in `random_storage_err`
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 22
    (by decide) (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gsA, gfr, grd, gwr⟩ :=
    q1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1.trans F.h1)
      (e5.trans F.h5) (e6.trans h6) hO64 (by omega) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 1676 35823 (A - 56) rd (A - 48) ptr len 1
      g0 g1 g7 g8 g9 (by decide) jte_837 bs_35823 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 8) = 0 := by
    rw [show A - 56 + 8 = A - 48 by omega, read_of_readN1 kbuf, ← hok]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := r_ok (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 (A - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have pay4 : ∀ a, ptr ≤ a → a < ptr + 1 + w + 32 * n → μ4.read a = μ.read a := fun a h1 h2 =>
    (kfr a (by omega) (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega))
  -- the length ℰ(n)
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ4 1678 35850 (A - 56) rd (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_838 bs_35850 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := r_call (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    (A - 56) n (by omega) (by omega) (by rw [d1, m1, k1', g1]) d7 d8
  -- the heap is as it was so far
  have b6 : ∀ a, a < 4294967296 → (a < A - 184 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [dwr, kwr, gwr]
  have H6 : HeapCtx env pb S0 S1 μ6 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr6
  have hv6 : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  have run07 := run1.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))
  -- the hashes
  rcases VecHash32.vec_hash32_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω7 μ6 s (A - 56) (A - 56 + 8)
      rd (ptr + 1 + w) (len - 1 - w) n 1680 35874 18446744073709551614 rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5]) hv6 o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_839 bs_35874 (by decide) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω8, μ8, ha, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, -, vfr, -,
      vgl, -⟩ | ⟨hna, ω8, μ8, run8, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω8, μ8, (run07.trans run8).mono (by omega), f7⟩
  have hst8 := H8.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 56 ≤ a → a < A + 56 → (a < A - 48 ∨ A - 24 ≤ a) → μ8.read a = μ3.read a :=
    fun a h1 h2 h3 => (vfr a (by omega) h1 (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + 32 * n < 2147483648 := by
    have := chunk_in H8.wf cm8 rfl; simp only at this; rw [hbase'] at this; omega
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    r_fin (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 (A - 56) A n q n 1018 22018 O rd
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) v1 (by omega) (by omega) (by omega) hO64 (by omega)
      vc (by rw [show A - 56 + 16 = A - 56 + 8 + 8 by omega]; exact vp)
      (by rw [show A - 56 + 24 = A - 56 + 8 + 16 by omega]; exact vl)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega))]; exact gsA)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
      (by decide) jte_508 bs_22018
      (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
      (fun a h1 h2 => hst8 a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h1 h2 => (cfr a h0 (by omega)).trans ((vfr a h0 (by omega) h2 (by omega)).trans (b6 a h0 (by omega) h2))
  obtain ⟨ω10, μ10, run10, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    q2 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 A O n q n ret t v5 v6 ⟨by omega, by omega⟩ (by omega)
      (by omega) (by rw [c1]; congr 1; omega) c5 (by omega) (by omega) (by omega) (by omega) F.hv5 F.hv6 cO cO8 cO16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt (fun a h1 h2 => Memory.readable_of_writable (by rw [cwr]; exact hst8 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [cwr]; exact hst8 a (by omega) (by omega))
  -- the heap after the copies: only the stack changed
  have hlow : ∀ a, a < 2147483648 → μ10.read a = μ8.read a := fun a h0 =>
    (nfr a (by omega) (by omega)).trans (cfr a (by omega) (by omega))
  have run := run07.trans (run8.trans (run9.trans run10))
  have wr10 : ∀ a, μ10.writable a = μ8.writable a := fun a => by rw [nwr, cwr]
  refine Or.inl ⟨q, s', ω10, μ10, ha, run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
    ctx_congr_data H8 cm8 (fun a h1 _ => hlow a h1) wr10, keep, cm8, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd8 c hc hu a ⟨hia.1, hia.2⟩]
      exact b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))
  · have e : ∀ j, j < 8 → μ10.read (rd + j) = μ8.read (rd + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (cfr _ (by omega) (by omega))
    rw [Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ10.read (rd + 8 + j) = μ8.read (rd + 8 + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (cfr _ (by omega) (by omega))
    rw [Memory.readN_congr e, vR8]
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlow a (by omega), vgl a ha']
    exact b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

/-! ## As an element of the decode loop -/

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems

/-- **`RandomStorageAccumulate(Ok(v))`'s slot** (GP v0.8.0 B.7, tag 22): the discriminant word
    2^63 + 21 and the `Vec` `{cap n, ptr q, len n}` at 8 for some q whose 32n octets (in the heap μ)
    are hs, the n hashes. -/
def RandomStorageOkRep (n : Nat) (hs : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775829 ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (32 * n) = hs

/-- **`RandomStorageAccumulate(Ok(v))`, as an element of the decode loop** (GP v0.8.0 B.7, tag 22): the
    encoding 22 :: 0 :: ℰ(n) ++ hs, with hs the 32n octets of the 1 ≤ n ≤ 512 hashes, decodes to
    `RandomStorageOkRep`, the hashes a fresh chunk of the heap; or the `alloc` fails. -/
theorem random_storage_ok_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 512) (hs : List UInt8) (hh : hs.length = 32 * n) :
    ElemOkAF env cap pb gl p P F RD (550 * n + 2000) (22 :: 0 :: (Blob.encodeNat n ++ hs))
      (RandomStorageOkRep n hs) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (22 :: 0 :: (Blob.encodeNat n ++ hs)).length - 1 = 1 + w + 32 * n := by simp [hW, hh]; omega
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have hok : μ.read ptr = 0 := by
    have := readN_sub μ ptr (1 + w + 32 * n) 0 1 _ pay (by omega)
    simpa [Memory.readN] using this
  have henc : μ.readN (ptr + 1) w = Blob.encodeNat n := by
    rw [readN_sub μ ptr (1 + w + 32 * n) 1 w _ pay (by omega), List.drop_succ_cons, List.drop_zero,
      List.take_left' hW]
  have hitems : μ.readN (ptr + 1 + w) (32 * n) = hs := by
    have := readN_sub μ ptr (1 + w + 32 * n) (w + 1) (32 * n) _ pay (by omega)
    rw [List.drop_succ_cons, List.drop_left' hW, List.take_of_length_le (by omega)] at this
    rw [show ptr + 1 + w = ptr + (w + 1) by omega]
    exact this
  rcases random_storage_ok_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hok (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1 <;> omega,
      by rw [gR8]; congr 1 <;> omega, ⟨9223372036854775829, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (32 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, ?_, ?_, ?_, ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end Services.Bootstrap.Decode.RandomStorage
