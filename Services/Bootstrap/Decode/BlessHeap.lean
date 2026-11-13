import Services.Bootstrap.Decode.Bless
import Services.Bootstrap.Decode.VecU32U64
import Services.Bootstrap.Decode.Elems

/-!
# `Instruction::decode` of `Bless`, the always-accumulate entries in the heap

`Bless { manager, assigner, designator, registrar: u32, always_acc: Vec<(u32, u64)> }` (tag 11; GP v0.8.0
B.7, the bootstrap service's instruction list) with 1 ≤ n ≤ 1024 always-accumulate entries:

* `bless_heap`: `Bless.bless_empty`'s prologue (the four `u32`s, the length ℰ(n)), then the pair reader
  (2727) through `VecU32U64.vec_u32u64_heap`, then the epilogue storing the variant into O. The
  encoding lies inside an allocated chunk, the allocator's context is `HeapCtx`, and the model's
  `alloc` failing is an outcome (null at the `alloc` wrapper's return, 40611).
* `bless_elem`: the same, as an element of the decode loop (`ElemOkAF`) at a frame base F with
  `Lay F RD`.
-/

namespace Services.Bootstrap.Decode.Bless

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Bless` with 1 ≤ n ≤ 1024 always-accumulate entries, the payload in the heap** (GP v0.8.0 B.7,
    tag 11): from 20626, with tag 11 read without error and the reader `{ptr, len}` at rd (ω₆) holding
    the four `u32`s (16 octets), ℰ(n) (w octets) and n pairs (12n octets: ℰ₄ then ℰ₈ each), all inside
    an allocated chunk of the allocator's state `s` (context `HeapCtx`, under `refineContractK cap`),
    either the model's `alloc` of ⌈16n/32⌉ units gives `(q, s')` and `Instruction::decode` returns
    `Bless { manager, assigner, designator, registrar, always_acc }` in O (the discriminant word
    2^63 + 10, the `Vec` `{cap n, ptr q, len n}` at O + 8, the four `u32`s at O + 32 … O + 44, pair j's
    `u32` at q + 16j and its `u64` at q + 16j + 8), the reader advanced by 16 + w + 12n, the context
    kept for `s'`, every allocated chunk of `s` kept with its data; or the model's `alloc` fails and
    the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem bless_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 11) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 408 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484056 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 1024)
    (hlen : 16 + (Blob.encodeNat n).length + 12 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 48 ≤ S1) (hOr : O + 48 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 16 + (Blob.encodeNat n).length + 12 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN (ptr + 16) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (260 * n + 2000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775818 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 32) 4 = μ.readN ptr 4 ∧ μ'.readN (O + 36) 4 = μ.readN (ptr + 4) 4 ∧
      μ'.readN (O + 40) 4 = μ.readN (ptr + 8) 4 ∧ μ'.readN (O + 44) 4 = μ.readN (ptr + 12) 4 ∧
      (∀ j, j < n → μ'.readN (q + 16 * j) 4 = μ.readN (ptr + 16 + (Blob.encodeNat n).length + 12 * j) 4 ∧
        μ'.readN (q + 16 * j + 8) 8 = μ.readN (ptr + 16 + (Blob.encodeNat n).length + 12 * j + 4) 8) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 16 + (Blob.encodeNat n).length + 12 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 16 - (Blob.encodeNat n).length - 12 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((16 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (260 * n + 2000) ∧
      ω'[7] = UInt64.ofNat 0) := by
  have hA2 := F.hA
  have hst := H.st
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen henc hpay hw1 ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := VecU8.chunk_in H.wf hcpm hcpu
  have hrdA : 65536 ≤ rd ∧ rd + 16 < 4294967296 := ⟨by omega, by omega⟩
  have hws : ∀ a, A - 208 ≤ a → a < A → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hrp : ∀ a, ptr ≤ a → a < ptr + 16 + w + 12 * n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (VecU8.heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨hv0, ev0⟩ := u32_of (μ := μ) (a := ptr)
  obtain ⟨hv1, ev1⟩ := u32_of (μ := μ) (a := ptr + 4)
  obtain ⟨hv2, ev2⟩ := u32_of (μ := μ) (a := ptr + 8)
  obtain ⟨hv3, ev3⟩ := u32_of (μ := μ) (a := ptr + 12)
  -- the prologue, as in `bless_empty`: H = A − 80 the helper's frame, the buffer at H + 32
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 11
    (by decide) (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    b1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1)
      (e5'.trans F.h5) (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- manager
  obtain ⟨ω3, μ3, run3, g0, g1, -, -, -, g5, g6, -, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1140 24543 (A - 80) rd (A - 48) ptr len 4
      f0 f1 f7 f8 f9 (by decide) jte_569 bs_24543 ⟨by omega, by omega⟩ hrdA ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have pay3 : ∀ b, ptr ≤ b → b < ptr + 16 + w + 12 * n → μ3.read b = μ.read b := fun b h1 h2 =>
    (gfr b (by omega) (by omega) (by omega) (by omega)).trans (ffr b (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    bk (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 24543 24 1142 (A - 80)
      (Num.decodeLE (μ.readN ptr 4)) (Or.inl ⟨rfl, rfl, rfl⟩) (by omega) (g1.trans f1) g7 hv0
      (by rw [show A - 80 + 32 = A - 48 by omega, gbuf, ev0]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- assigner
  obtain ⟨ω5, μ5, run5, m0, m1, -, -, -, m5, m6, -, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 1142 24572 (A - 80) rd (A - 48) (ptr + 4)
      (len - 4) 4 k0 (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6))
      (by rw [k8, show A - 80 + 32 = A - 48 by omega]) k9
      (by decide) jte_570 bs_24572 ⟨by omega, by omega⟩ hrdA ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have pay5 : ∀ b, ptr ≤ b → b < ptr + 16 + w + 12 * n → μ5.read b = μ.read b := fun b h1 h2 =>
    (mfr b (by omega) (by omega) (by omega) (by omega)).trans ((kfr b (by omega) (by omega) (by omega)).trans
      (pay3 b h1 h2))
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, n8, n9, npark, nfr, nrd, nwr⟩ :=
    bk (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 24572 16 1144 (A - 80)
      (Num.decodeLE (μ.readN (ptr + 4) 4)) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (by omega)
      (m1.trans (k1.trans (g1.trans f1))) m7 hv1
      (by rw [show A - 80 + 32 = A - 48 by omega, mbuf, ev1]
          exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega) (by omega)).trans
            (pay3 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- designator
  obtain ⟨ω7, μ7, run7, q0, q1, -, -, -, q5, q6, -, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 1144 24601 (A - 80) rd (A - 48)
      (ptr + 4 + 4) (len - 4 - 4) 4 n0
      (n1.trans (m1.trans (k1.trans (g1.trans f1)))) (n7.trans (m6.trans (k6.trans (g6.trans f6))))
      (by rw [n8, show A - 80 + 32 = A - 48 by omega]) n9
      (by decide) jte_571 bs_24601 ⟨by omega, by omega⟩ hrdA ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR8)
  have pay7 : ∀ b, ptr ≤ b → b < ptr + 16 + w + 12 * n → μ7.read b = μ.read b := fun b h1 h2 =>
    (qfr b (by omega) (by omega) (by omega) (by omega)).trans ((nfr b (by omega) (by omega) (by omega)).trans
      (pay5 b h1 h2))
  obtain ⟨ω8, μ8, run8, r0, r1, r5, r6, r7, r8, r9, rpark, rfr, rrd, rwr⟩ :=
    bk (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 24601 8 1146 (A - 80)
      (Num.decodeLE (μ.readN (ptr + 8) 4)) (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by omega)
      (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))) q7 hv2
      (by rw [show A - 80 + 32 = A - 48 by omega, qbuf, ev2, show ptr + 4 + 4 = ptr + 8 by omega]
          exact Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans
            (pay5 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- registrar
  obtain ⟨ω9, μ9, run9, s0, s1, -, -, -, s5, s6, -, s7, sR0, sR8, sbuf, sfr, srd, swr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 1146 24630 (A - 80) rd (A - 48)
      (ptr + 4 + 4 + 4) (len - 4 - 4 - 4) 4 r0
      (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))))
      (r7.trans (q6.trans (n6.trans (m6.trans (k6.trans (g6.trans f6))))))
      (by rw [r8, show A - 80 + 32 = A - 48 by omega]) r9
      (by decide) jte_572 bs_24630 ⟨by omega, by omega⟩ hrdA ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rrd, qrd, nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega) (by omega))]; exact qR0)
      (by rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega) (by omega))]; exact qR8)
  have pay9 : ∀ b, ptr ≤ b → b < ptr + 16 + w + 12 * n → μ9.read b = μ.read b := fun b h1 h2 =>
    (sfr b (by omega) (by omega) (by omega) (by omega)).trans ((rfr b (by omega) (by omega) (by omega)).trans
      (pay7 b h1 h2))
  obtain ⟨ω10, μ10, run10, u0, u1, u5, u6, u7, upark, ufr, urd, uwr⟩ :=
    b5 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 (A - 80) (Num.decodeLE (μ.readN (ptr + 12) 4))
      (by omega) (s1.trans (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))))) s7 hv3
      (by rw [show A - 80 + 32 = A - 48 by omega, sbuf, ev3, show ptr + 4 + 4 + 4 = ptr + 12 by omega]
          exact Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega) (by omega)).trans
            (pay7 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [srd, rrd, qrd, nrd, mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have h1_10 : ω10[1] = UInt64.ofNat (A - 80) :=
    u1.trans (s1.trans (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1)))))))
  have h6_10 : ω10[6] = UInt64.ofNat rd :=
    u6.trans (s6.trans (r6.trans (q6.trans (n6.trans (m6.trans (k6.trans (g6.trans f6)))))))
  have h5_10 : ω10[5] = UInt64.ofNat O :=
    u5.trans (s5.trans (r5.trans (q5.trans (n5.trans (m5.trans (k5.trans (g5.trans f5)))))))
  -- the length ℰ(n)
  obtain ⟨ω11, μ11, run11, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω10 μ10 1148 24647 (A - 80) rd
      (ptr + 4 + 4 + 4 + 4) (len - 4 - 4 - 4 - 4) u0 h1_10 (u7.trans (u6.symm.trans h6_10)) (by decide) jte_573
      bs_24647 ⟨by omega, by omega⟩ hrdA ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => ufr _ (by omega) (by omega))]; exact sR0)
      (by rw [Memory.readN_congr (fun j hj => ufr _ (by omega) (by omega))]; exact sR8) n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by
        rw [hW] at h2
        rw [urd, srd, rrd, qrd, nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by
        rw [hW, show ptr + 4 + 4 + 4 + 4 = ptr + 16 by omega,
          Memory.readN_congr (fun j hj => (ufr _ (by omega) (by omega)).trans (pay9 _ (by omega) (by omega)))]
        exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω12, run12, c0, c1, c5, c6, c7, c8, c9⟩ := b6 (p := p) (P := P) (R := refineContractK cap env) x ω11 μ11
    (A - 80) n (by omega) (by omega) (d1.trans h1_10) d7 d8
  -- the memory so far: only the frames A − 208 … A and the reader changed
  have b11 : ∀ a, a < 4294967296 → (a < A - 208 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ11.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans
      ((ufr a h0 (by omega)).trans ((sfr a h0 (by omega) h2 (by omega)).trans ((rfr a h0 (by omega) (by omega)).trans
      ((qfr a h0 (by omega) h2 (by omega)).trans ((nfr a h0 (by omega) (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega) (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))))))))
  have wr11 : ∀ a, μ11.writable a = μ.writable a := fun a => by
    rw [dwr, uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]
  have H11 : HeapCtx env pb S0 S1 μ11 s :=
    VecU8.ctx_congr_data H hcpm (fun a h1 _ => b11 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr11
  have run011 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans (run10.trans (run11.trans run12))))))))))
  -- the pairs
  rcases VecU32U64.vec_u32u64_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω12 μ11 s (A - 80)
      (A - 80 + 32) rd (ptr + 4 + 4 + 4 + 4 + w) (len - 4 - 4 - 4 - 4 - w) n 1150 24670 O rd pb S0 S1 H11
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ c0
      (by rw [c1, d1, h1_10]) (by rw [c5, d5, h5_10]) (by rw [c6, d6, h6_10]) c7 (by rw [c8, d6, h6_10]) c9
      (by decide) jte_574 bs_24670 hO64 hrd64 hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω13, μ13, ha, run13, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H13, keep, cm13, hfresh, kd13, -,
      vfr, -, vgl, -⟩ | ⟨hna, ω13, μ13, run13, f7'⟩
  rotate_left
  · exact Or.inr ⟨hna, ω13, μ13, (run011.trans run13).mono (by omega), f7'⟩
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + 16 * n < 2147483648 := by
    have := VecU8.chunk_in H13.wf cm13 rfl; simp only at this; rw [hbase'] at this; omega
  -- the frame's words in μ13
  have kH : ∀ a, A - 80 ≤ a → a < A + 56 → (a < A - 48 ∨ A - 24 ≤ a) → μ13.read a = μ10.read a :=
    fun a h1 h2 h3 => (vfr a (by omega) (by omega) (by omega) (by omega)).trans (dfr a (by omega) (by omega) (by omega))
  have park0 : (μ13.readN (A - 80 + 24) 8).take 4 = μ.readN ptr 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      ((sfr _ (by omega) (by omega) (by omega) (by omega)).trans ((rfr _ (by omega) (by omega) (by omega)).trans
      ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans ((nfr _ (by omega) (by omega) (by omega)).trans
      (mfr _ (by omega) (by omega) (by omega) (by omega)))))))), kpark, ev0]
  have park1 : (μ13.readN (A - 80 + 16) 8).take 4 = μ.readN (ptr + 4) 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      ((sfr _ (by omega) (by omega) (by omega) (by omega)).trans ((rfr _ (by omega) (by omega) (by omega)).trans
      (qfr _ (by omega) (by omega) (by omega) (by omega)))))), npark, ev1]
  have park2 : (μ13.readN (A - 80 + 8) 8).take 4 = μ.readN (ptr + 8) 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      (sfr _ (by omega) (by omega) (by omega) (by omega)))), rpark, ev2]
  have park3 : (μ13.readN (A - 80) 8).take 4 = μ.readN (ptr + 12) 4 := by
    rw [Memory.readN_congr (fun j hj => kH _ (by omega) (by omega) (by omega)), upark, ev3]
  have hsv : ∀ a, A - 24 ≤ a → a < A → μ13.read a = μ2.read a := fun a h1 h2 =>
    (kH a (by omega) (by omega) (by omega)).trans ((ufr a (by omega) (by omega)).trans
      ((sfr a (by omega) (by omega) (by omega) (by omega)).trans ((rfr a (by omega) (by omega) (by omega)).trans
      ((qfr a (by omega) (by omega) (by omega) (by omega)).trans ((nfr a (by omega) (by omega) (by omega)).trans
      ((mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))))))))
  have hst13 := H13.st
  -- the variant
  obtain ⟨ω14, μ14, run14, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO36, zO40, zO44, zfr, zrd, zwr⟩ :=
    b7 (p := p) (P := P) (R := refineContractK cap env) x ω13 μ13 (A - 80) O n q n (rdN μ13 (A - 80 + 24) 8)
      (rdN μ13 (A - 80 + 16) 8) (rdN μ13 (A - 80 + 8) 8) (rdN μ13 (A - 80) 8) rd (by omega) (by omega)
      (by omega) v1 v5' (by omega) (by omega) (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (rdN_lt64 _ _) hrd64 hO64 vc (by rw [show A - 80 + 40 = A - 80 + 32 + 8 by omega]; exact vp)
      (by rw [show A - 80 + 48 = A - 80 + 32 + 16 by omega]; exact vl)
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [show A - 80 + 72 = A - 8 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f72)
      (by rw [show A - 80 + 64 = A - 16 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f64)
      (by rw [show A - 80 + 56 = A - 24 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f56)
      (fun a h1 h2 => hst13 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst13 a (by omega) (by omega)))
  have b14 : ∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 48 ≤ a) →
      μ14.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (zfr a h0 h3).trans ((vfr a h0 (by omega) h2 (by omega)).trans (b11 a h0 (Or.inr h1) h2))
  obtain ⟨ω15, run15, y0, y1, y5, y6⟩ := b8 (p := p) (P := P) (R := refineContractK cap env) x ω14 μ14 A ret t v5 v6
    ⟨by omega, by omega⟩ (by rw [z1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => by rw [zrd]; exact Memory.readable_of_writable (hst13 a (by omega) (by omega)))
  -- the heap after the variant: only the stack changed
  have hlow : ∀ a, a < 2147483648 → μ14.read a = μ13.read a := fun a h0 => zfr a (by omega) (Or.inl (by omega))
  have run := run011.trans (run13.trans (run14.trans run15))
  refine Or.inl ⟨q, s', ω15, μ14, ha, run.mono (by omega), y0, y1, y5, y6, zO, zO8, zO16, zO24, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, VecU8.ctx_congr_data H13 cm13 (fun a h1 _ => hlow a h1) zwr, keep, cm13, hfresh,
    fun c hc hu a hia => by
      have := (VecU8.chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd13 c hc hu a ⟨hia.1, hia.2⟩]
      exact b11 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, b14, ?_, ?_, ?_⟩
  · rw [zO32, ← take_encodeLE, encodeLE_rdN]; exact park0
  · rw [zO36, ← take_encodeLE, encodeLE_rdN]; exact park1
  · rw [zO40, ← take_encodeLE, encodeLE_rdN]; exact park2
  · rw [zO44, ← take_encodeLE, encodeLE_rdN]; exact park3
  · intro j hj
    obtain ⟨e4, e8⟩ := vdata j hj
    refine ⟨?_, ?_⟩
    · rw [Memory.readN_congr (fun i hi => hlow _ (by omega)), e4,
        show ptr + 4 + 4 + 4 + 4 + w + 12 * j = ptr + 16 + w + 12 * j by omega]
      exact Memory.readN_congr (fun i hi => b11 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
    · rw [Memory.readN_congr (fun i hi => hlow _ (by omega)), e8,
        show ptr + 4 + 4 + 4 + 4 + w + 12 * j + 4 = ptr + 16 + w + 12 * j + 4 by omega]
      exact Memory.readN_congr (fun i hi => b11 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
  · have e : ∀ j, j < 8 → μ14.read (rd + j) = μ13.read (rd + j) := fun j hj => zfr _ (by omega) (by omega)
    rw [show ptr + 16 + w + 12 * n = ptr + 4 + 4 + 4 + 4 + w + 12 * n by omega, Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ14.read (rd + 8 + j) = μ13.read (rd + 8 + j) := fun j hj =>
      zfr _ (by omega) (by omega)
    rw [show len - 16 - w - 12 * n = len - 4 - 4 - 4 - 4 - w - 12 * n by omega, Memory.readN_congr e, vR8]
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlow a (by omega), vgl a ha']
    exact b11 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

/-! ## As an element of the decode loop -/

open Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems

/-- **`Bless`'s slot** (GP v0.8.0 B.7, tag 11): the discriminant word 2^63 + 10, the four `u32`s'
    octets m, a, d, r at 32, 36, 40, 44, and the `Vec` `{cap n, ptr q, len n}` at 8 for some q whose
    element j (16 octets at q + 16j, in the heap μ) holds pair j of `items` (12 octets: the `u32`'s 4
    and then the `u64`'s 8): the `u32` at q + 16j and the `u64` at q + 16j + 8. -/
def BlessRep (m a d r : List UInt8) (n : Nat) (items : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775818 ∧ (bs.drop 32).take 4 = m ∧ (bs.drop 36).take 4 = a ∧
  (bs.drop 40).take 4 = d ∧ (bs.drop 44).take 4 = r ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧
    ∀ j, j < n → μ.readN (q + 16 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ.readN (q + 16 * j + 8) 8 = (items.drop (12 * j + 4)).take 8

/-- **`Bless`, as an element of the decode loop** (GP v0.8.0 B.7, tag 11): the encoding
    11 :: m ++ a ++ d ++ r ++ ℰ(n) ++ items, with m, a, d, r the 4 octets of `manager`, `assigner`,
    `designator`, `registrar` and items the 12n octets of the 1 ≤ n ≤ 1024 `always_acc` pairs, decodes
    to `BlessRep`, the pairs a fresh chunk of the heap; or the `alloc` fails. -/
theorem bless_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (m a d r : List UInt8) (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4)
    (hr4 : r.length = 4) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 1024) (items : List UInt8) (hi : items.length = 12 * n) :
    ElemOkAF env cap pb gl p P F RD (260 * n + 2000) (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items))
      (BlessRep m a d r n items) := by
  intro x ω μ ptr len v5 v6 st h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items)).length - 1 = 16 + w + 12 * n := by
    simp [hW, hi, hm4, ha4, hd4, hr4]; try omega
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have l8 : (m ++ a).length = 8 := by simp [hm4, ha4]
  have l12 : (m ++ a ++ d).length = 12 := by simp [hm4, ha4, hd4]
  have l16 : (m ++ a ++ d ++ r).length = 16 := by simp [hm4, ha4, hd4, hr4]
  have lw : (m ++ a ++ d ++ r ++ Blob.encodeNat n).length = 16 + w := by simp [hm4, ha4, hd4, hr4, hW]; try omega
  have payM : μ.readN ptr (16 + w + 12 * n) = m ++ (a ++ (d ++ (r ++ (Blob.encodeNat n ++ items)))) := by
    rw [pay]; simp
  have pay8 : μ.readN ptr (16 + w + 12 * n) = (m ++ a) ++ (d ++ (r ++ (Blob.encodeNat n ++ items))) := by
    rw [pay]; simp
  have pay12 : μ.readN ptr (16 + w + 12 * n) = (m ++ a ++ d) ++ (r ++ (Blob.encodeNat n ++ items)) := by
    rw [pay]; simp
  have pay16 : μ.readN ptr (16 + w + 12 * n) = (m ++ a ++ d ++ r) ++ (Blob.encodeNat n ++ items) := by
    rw [pay]; simp
  have payI : μ.readN ptr (16 + w + 12 * n) = (m ++ a ++ d ++ r ++ Blob.encodeNat n) ++ items := pay
  have hm' : μ.readN ptr 4 = m := by
    rw [← readN_take _ _ (16 + w + 12 * n) 4 (by omega), payM, List.take_left' hm4]
  have ha' : μ.readN (ptr + 4) 4 = a := by
    rw [readN_sub μ ptr _ 4 4 _ payM (by omega), List.drop_left' hm4, List.take_left' ha4]
  have hd' : μ.readN (ptr + 8) 4 = d := by
    rw [readN_sub μ ptr _ 8 4 _ pay8 (by omega), List.drop_left' l8, List.take_left' hd4]
  have hr' : μ.readN (ptr + 12) 4 = r := by
    rw [readN_sub μ ptr _ 12 4 _ pay12 (by omega), List.drop_left' l12, List.take_left' hr4]
  have henc : μ.readN (ptr + 16) w = Blob.encodeNat n := by
    rw [readN_sub μ ptr _ 16 w _ pay16 (by omega), List.drop_left' l16, List.take_left' hW]
  have hitems : μ.readN (ptr + 16 + w) (12 * n) = items := by
    have := readN_sub μ ptr _ (16 + w) (12 * n) _ payI (by omega)
    rw [List.drop_left' lw, List.take_of_length_le (by omega)] at this
    rw [show ptr + 16 + w = ptr + (16 + w) by omega]
    exact this
  have hit : ∀ j, j < n → μ.readN (ptr + 16 + w + 12 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ.readN (ptr + 16 + w + 12 * j + 4) 8 = (items.drop (12 * j + 4)).take 8 := fun j hj =>
    ⟨readN_sub μ (ptr + 16 + w) (12 * n) (12 * j) 4 items hitems (by omega),
      by
        rw [Nat.add_assoc (ptr + 16 + w)]
        exact readN_sub μ (ptr + 16 + w) (12 * n) (12 * j + 4) 8 items hitems (by omega)⟩
  rcases bless_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ st F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', hal, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gO32, gO36, gO40, gO44, gdat, gR0, gR8, H',
      keep, hnew, hfresh, kd, -, gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1 <;> omega,
      by rw [gR8]; congr 1 <;> omega, ⟨9223372036854775818, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (16 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, ?_, ?_, ?_, ?_, q, ?_, ?_, ?_,
        fun j hj => ⟨?_, ?_⟩⟩
      · rw [← readN_sub μ' (F + 120) 232 32 4 _ rfl (by decide), gO32]; exact hm'
      · rw [← readN_sub μ' (F + 120) 232 36 4 _ rfl (by decide), gO36]; exact ha'
      · rw [← readN_sub μ' (F + 120) 232 40 4 _ rfl (by decide), gO40]; exact hd'
      · rw [← readN_sub μ' (F + 120) 232 44 4 _ rfl (by decide), gO44]; exact hr'
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun i hi => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), (gdat j hj).1]
        exact (hit j hj).1
      · rw [Memory.readN_congr (fun i hi => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), (gdat j hj).2]
        exact (hit j hj).2
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end Services.Bootstrap.Decode.Bless
