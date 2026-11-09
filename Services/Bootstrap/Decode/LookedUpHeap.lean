import Services.Bootstrap.Decode.LookedUp
import Services.Bootstrap.Decode.VecU8Heap

/-!
# `Instruction::decode` of `LookedUp { data: Some(bytes) }`, the payload in the heap

`looked_up_heap` is `looked_up_small` in the decode loop's setting, through `VecU8.vec_u8_heap`: the
encoding lies inside an allocated chunk, the allocator's context is `HeapCtx`, and the model's
`alloc` failing is an outcome (null at the `alloc` wrapper's return, 40611).
-/

namespace Services.Bootstrap.Decode.LookedUp

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`LookedUp { data: Some(bytes) }`, 1 ≤ n = |bytes| ≤ 16384, the payload in the heap**: from 20626,
    with tag 18 read without error and the reader `{ptr, len}` at rd (ω₆) holding 1 (`Some`), ℰ(n)
    (w octets) and n more octets, all inside an allocated chunk of the allocator's state `s` (context
    `HeapCtx`, under `refineContractK cap`), either the model's `alloc` of ⌈n/32⌉ units gives
    `(q, s')` and `Instruction::decode` returns `LookedUp { data: Some(bytes) }` in O (the
    discriminant word 2^63 + 17, the `Vec` `{cap n, ptr q, len n}` at O + 8, the n octets at q), the
    context kept for `s'`, every allocated chunk of `s` kept with its data; or the model's `alloc` fails
    and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem looked_up_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 18) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 400 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484048 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 16384)
    (hlen : 1 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (2 * n + 2000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775825 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q n = μ.readN (ptr + 1 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1 - (Blob.encodeNat n).length - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (2 * n + 2000) ∧
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
  have hra : ∀ a, ptr ≤ a → a < ptr + 1 + w + n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  have hws : ∀ a, A - 400 ≤ a → a < A + 56 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 18 (by decide)
    (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, run2, f0, f1, f5, f6, f7, f8⟩ := k1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ A A rd 1006 O rd ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [f0])
      (by rw [f1, e1, F.h1]) (by rw [f5, e5, F.h5]) (by rw [f6, e6, h6]) (by rw [f7, e1, F.h1])
      (by rw [f8, e6, h6]) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 1682 35970 (A - 56) rd (A - 25) ptr len 1 g0 g1
      g7 g8 g9 (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 31) = 1 := by
    rw [show A - 56 + 31 = A - 25 by omega, read_of_readN1 kbuf, ← hsome]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := o_some (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 (A - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have pay4 : ∀ a, ptr ≤ a → a < ptr + 1 + w + n → μ4.read a = μ.read a := fun a h1 h2 =>
    (kfr a (by omega) (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ4 1684 35994 (A - 56) rd (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_841 bs_35994 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := o_len (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    (A - 56) n (by omega) (by omega) (by rw [d1, m1, k1', g1]) d7 d8
  -- the heap is as it was so far
  have b6 : ∀ a, a < 4294967296 → (a < A - 400 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [dwr, kwr, gwr]
  have rd6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [drd, krd, grd]
  have H6 : HeapCtx env pb S0 S1 μ6 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr6
  have hv6 : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  have run07 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  rcases vec_u8_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω7 μ6 s (A - 56) (A - 56) rd
      (ptr + 1 + w) (len - 1 - w) n 1686 36016 A rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5, k5, g5]) hv6 o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_842 bs_36016 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω8, μ8, ha, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, pg8, vfr, -, -, -⟩ |
    ⟨hna, ω8, μ8, run8, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω8, μ8, (run07.trans run8).mono (by omega), f7⟩
  have hst8 := H8.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 32 ≤ a → a < A + 56 → a ≠ A - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + n < 2147483648 := by
    have := chunk_in H8.wf cm8 rfl; simp only at this; rw [hbase'] at this; omega
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    o_copy (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 (A - 56) A n q n 1006 21817 O rd
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
      (by decide) jte_502 bs_21817
      (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
      (fun a h1 h2 => hst8 a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h1 h2 => (cfr a h0 (by omega)).trans ((vfr a h0 (by omega) h2 (by omega)).trans (b6 a h0 (by omega) h2))
  obtain ⟨ω10, μ10, run10, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    k2 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 A O n q n ret t v5 v6 ⟨by omega, by omega⟩ (by omega)
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
    FreeStepsH.pagesOut H.bd run, ?_⟩
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

end Services.Bootstrap.Decode.LookedUp
