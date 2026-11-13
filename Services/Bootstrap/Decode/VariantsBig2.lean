import Services.Bootstrap.Decode.BlessHeap
import Services.Bootstrap.Decode.VecU32U64Big
import Services.Bootstrap.Decode.RandomStorageOk
import Services.Bootstrap.Decode.VecHash32Big
import Services.Bootstrap.Decode.DesignateHeap
import Services.Bootstrap.Decode.VecKey336Big
import Services.Bootstrap.Decode.AssignGas
import Services.Bootstrap.Decode.VecHashBig
import Services.Bootstrap.Decode.LookedUpHeap
import Services.Bootstrap.Decode.ProvideInlineHeap
import Services.Bootstrap.Decode.CreateServiceHeap
import Services.Bootstrap.Decode.VecU8HeapBig

/-!
# More variants with the large readers, the payload in the heap

Variant-level compositions of `Instruction::decode` (20626) with the element readers without their
small-n limits (GP v0.8.0 B.7, the bootstrap service's instruction list), in the style of
`VariantsBig`: the small composition's steps, then the big reader in place of the small one.

* `bless_heap_big`: `Bless` (tag 11) with n > 1024 always-accumulate entries, as `Bless.bless_heap`
  with `VecU32U64.vec_u32u64_heap_big`;
* `random_storage_ok_heap_big`: `RandomStorageAccumulate(Ok(v))` (tag 22) with n > 512 hashes, as
  `RandomStorage.random_storage_ok_heap` with `VecHash32.vec_hash32_heap_big`;
* `designate_heap_big`: `Designate { keys }` (tag 13) with 48 < n ≤ (3·𝖢) mod 2^16 keys, as
  `Designate.designate_heap` with `VecKey336.vec_key336_heap_big`;
* `assign_gas_heap_big`: `AssignForGasCost` (tag 24) with n > 512 hashes, the variant-level
  composition behind `AssignGas.assign_gas_elemF` (`ag1` … `ag5`) with `VecHash.vec_hash_heap_big`;
* `looked_up_heap_big`, `provide_inline_heap_big`, `create_service_heap_big` (with
  `opt_vec_heap_big`): `LookedUp { data: Some(bytes) }` (tag 18), `Provide { Inline(bytes) }` (tag 17)
  and `CreateService` with `Some(bytes)` (tag 0) for |bytes| > 16384, as `LookedUp.looked_up_heap`,
  `Provide.provide_inline_heap`, `CreateService.opt_vec_heap` / `create_service_heap` with
  `VecU8.vec_u8_heap_big`.

`Assign` (tag 12) needs no big version: its hash count is the global 𝖰 at 196680, which the start-up
copies from the protocol parameters (`BParamsConsts`: 𝖰 = 80 under `Params.full`), within the small
reader's n ≤ 512.

Each statement is its small composition's with: the reader's count bound replaced by the big
reader's, the stack bounds translated from the big reader's (sp ↦ the composition's call frame), the
step bound the big reader's plus the small composition's margin over its small reader, and the
failure outcome `Exhausts … 20626 …` (via `LoopA.Exhausts.pre`).

Either the decoder returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

The globals below the allocator (`Glob`) are kept, as in the small compositions. *Not stated*
(unlike the small compositions): the model `alloc` equation (the big readers do not state it).
-/

namespace Services.Bootstrap.Decode.VariantsBig2

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Alloc
  JAM Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.Bless in
/-- **`Bless` with more than 1024 always-accumulate entries, the payload in the heap** (GP v0.8.0
    B.7, tag 11): as `Bless.bless_heap`, for 1024 < n with 16n < 2³⁰ − 64, with A at least S0 + 560
    (the pair reader at A − 80 needing S0 + 480, `VecU32U64.vec_u32u64_heap_big`). Either
    `Instruction::decode` returns `Bless { manager, assigner, designator, registrar, always_acc }` in O
    (as in `bless_heap`, the pairs in a fresh allocated chunk of ⌈16n/32⌉ + 1 units), the reader
    advanced by 16 + w + 12n, the context kept for the final state `s'` and every allocated chunk of
    `s` kept with its data; or the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem bless_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 11) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 560 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484208 ≤ A ∧ A % 8 = 0)
    (hn : 1024 < n ∧ 16 * n < 1073741760)
    (hlen : 16 + (Blob.encodeNat n).length + 12 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 48 ≤ S1) (hOr : O + 48 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 16 + (Blob.encodeNat n).length + 12 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN (ptr + 16) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (268200 + VecPairs.pairSteps 1024 (n - 1024)) ∧
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
    Exhausts env cap pb p P 20626 ω μ x (268200 + VecPairs.pairSteps 1024 (n - 1024)) := by
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
  rcases VecU32U64.vec_u32u64_heap_big (p := p) (P := P) env cap hcap1 hcap x ω12 μ11 s (A - 80)
      (A - 80 + 32) rd (ptr + 4 + 4 + 4 + 4 + w) (len - 4 - 4 - 4 - 4 - w) n 1150 24670 O rd pb S0 S1 H11
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ c0
      (by rw [c1, d1, h1_10]) (by rw [c5, d5, h5_10]) (by rw [c6, d6, h6_10]) c7 (by rw [c8, d6, h6_10]) c9
      (by decide) jte_574 bs_24670 hO64 hrd64 hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω13, μ13, run13, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H13, keep, cm13, hfresh, kd13, -,
      vfr, -, vgl, -⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run011 ex).mono (by omega))
  have hqT : q + 16 * n < 2147483648 := by
    have hc13 := VecU8.chunk_in H13.wf cm13 rfl
    have := H13.hbT
    simp only at hc13
    omega
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
  refine Or.inl ⟨q, s', ω15, μ14, run.mono (by omega), y0, y1, y5, y6, zO, zO8, zO16, zO24, ?_, ?_, ?_, ?_,
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

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.RandomStorage in
/-- **`RandomStorageAccumulate(Ok(v))` with more than 512 hashes, the payload in the heap** (GP v0.8.0
    B.7, tag 22): as `RandomStorage.random_storage_ok_heap`, for 512 < n with 32n < 2³⁰ − 64, with A at
    least S0 + 568 (the hash reader at A − 56 needing S0 + 512, `VecHash32.vec_hash32_heap_big`).
    Either `Instruction::decode` returns `RandomStorageAccumulate(Ok(v))` in O (the discriminant word
    2^63 + 21, the `Vec` `{cap n, ptr q, len n}` at O + 8, the 32n octets of the hashes at q, the data
    of a fresh allocated chunk of n + 1 units), the reader advanced by 1 + w + 32n, the context kept
    for the final state `s'` and every allocated chunk of `s` kept with its data; or the run reaches a
    failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem random_storage_ok_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 22) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 568 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484216 ≤ A ∧ A % 8 = 0)
    (hn : 512 < n ∧ 32 * n < 1073741760)
    (hlen : 1 + (Blob.encodeNat n).length + 32 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + 32 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hok : μ.read ptr = 0) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (268300 + VecHash32.hashSteps 512 (n - 512)) ∧
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
    Exhausts env cap pb p P 20626 ω μ x (268300 + VecHash32.hashSteps 512 (n - 512)) := by
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
  rcases VecHash32.vec_hash32_heap_big (p := p) (P := P) env cap hcap1 hcap x ω7 μ6 s (A - 56) (A - 56 + 8)
      rd (ptr + 1 + w) (len - 1 - w) n 1680 35874 18446744073709551614 rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5]) hv6 o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_839 bs_35874 (by decide) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, -, vfr, -,
      vgl, -⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run07 ex).mono (by omega))
  have hst8 := H8.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 56 ≤ a → a < A + 56 → (a < A - 48 ∨ A - 24 ≤ a) → μ8.read a = μ3.read a :=
    fun a h1 h2 h3 => (vfr a (by omega) h1 (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hqT : q + 32 * n < 2147483648 := by
    have hc8 := chunk_in H8.wf cm8 rfl
    have := H8.hbT
    simp only at hc8
    omega
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
  refine Or.inl ⟨q, s', ω10, μ10, run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
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

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.VecKey336 Services.Bootstrap.Decode.Designate in
/-- **`Designate { keys }` with more than 48 keys, the payload in the heap** (GP v0.8.0 B.7, tag 13): as
    `Designate.designate_heap` (the same stack bounds, the key reader's being those of
    `VecKey336.vec_key336_heap_big`), for 48 < n ≤ (3·𝖢) mod 2^16 (the code's bound) with
    336n < 2³⁰ − 64. Either `Instruction::decode` returns `Designate { keys }` in O (the discriminant
    word 2^63 + 12, the `Vec` `{cap n, ptr q, len n}` at O + 8, the keys at q in their in-memory layout
    `keysRot`, the data of a fresh allocated chunk of ⌈336n/32⌉ + 1 units), the reader advanced by
    w + 336n, the context kept for the final state `s'` and every allocated chunk of `s` kept with its
    data; or the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem designate_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len n C pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 13) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hC : μ.readN 196616 2 = Num.encodeLE 2 C) (hnC : n ≤ 3 * C % 65536)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 1648 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147485296 ≤ A ∧ A % 8 = 0)
    (hn : 48 < n ∧ 336 * n < 1073741760)
    (hlen : (Blob.encodeNat n).length + 336 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat n).length + 336 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (396000 + VecKey336.keySteps 48 (n - 48)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775820 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (336 * n) = keysRot n (μ.readN (ptr + (Blob.encodeNat n).length) (336 * n)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat n).length + 336 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat n).length - 336 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (336 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (336 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (396000 + VecKey336.keySteps 48 (n - 48)) := by
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
  have hra : ∀ a, ptr ≤ a → a < ptr + w + 336 * n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  have hws : ∀ a, A - 1648 ≤ a → a < A + 56 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hc : ∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (glob_writable' H ⟨by omega, by omega⟩)
  -- dispatch and the helper's frame
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 13
    (by decide) (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    d1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1)
      (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hws a (by omega) (by omega))
  -- the length ℰ(n)
  obtain ⟨ω3, μ3, run3, ⟨d0, d1', -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1648 35293 (A - 48) rd ptr len b0 b1 b7
      (by decide) jte_823 bs_35293 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [bwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [brd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  -- the bound check and the call of the key reader
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := d2n (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    (A - 48) n C (by omega) (by rw [d1', b1]) d7 d8 (by omega)
    (by rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hC) hnC
    (fun a h1 h2 => by rw [drd, brd]; exact hc a h1 h2)
  -- the heap is as it was so far
  have b3 : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [dwr, bwr]
  have H3 : HeapCtx env pb S0 S1 μ3 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr3
  have hv6 : ω4[6] = UInt64.ofNat rd := by rw [c6, d6, b6]
  have run04 := run1.trans (run2.trans (run3.trans run4))
  -- the keys
  rcases vec_key336_heap_big (p := p) (P := P) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48)
      rd (ptr + w) (len - w) n 1650 35349 A rd pb S0 S1 H3
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ c0
      (by rw [c1, d1', b1]) (by rw [c5, d5, b5]) hv6 c7 (by rw [c8, d6, b6]) c9
      (by decide) jte_824 bs_35349 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω5, μ5, run5, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H5, keep, cm5, hfresh, kd5, -, vfr, -,
      vgl, -⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run04 ex).mono (by omega))
  have hst5 := H5.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a :=
    fun a h1 h2 => (vfr a (by omega) (by omega) (by omega) (by omega)).trans
      (dfr a (by omega) (by omega) (by omega))
  have hqT : q + 336 * n < 2147483648 := by
    have hc5 := chunk_in H5.wf cm5 rfl
    have := H5.hbT
    simp only at hc5
    omega
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fA, fA8, fA16, ffr, frd, fwr⟩ :=
    d3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (A - 48) A n q n O rd ⟨by omega, by omega⟩
      (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => hst5 a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (ffr a h0 (by omega)).trans ((vfr a h0 (by omega) h2 (by omega)).trans (b3 a h0 (by omega) h2))
  obtain ⟨ω7, μ7, run7, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    d4 (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 A O n q n ret t v5 v6 ⟨by omega, by omega⟩ (by omega)
      (by omega) (by rw [f1]; congr 1; omega) f5 (by omega) (by omega) (by omega) F.hv5 F.hv6 fA fA8 fA16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt
      (fun a h1 h2 => by rw [frd]; exact Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [fwr]; exact hst5 a (by omega) (by omega))
  -- the heap after the copies: only the stack changed
  have hlow : ∀ a, a < 2147483648 → μ7.read a = μ5.read a := fun a h0 =>
    (nfr a (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  have run := run04.trans (run5.trans (run6.trans run7))
  have wr7 : ∀ a, μ7.writable a = μ5.writable a := fun a => by rw [nwr, fwr]
  refine Or.inl ⟨q, s', ω7, μ7, run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
    ctx_congr_data H5 cm5 (fun a h1 _ => hlow a h1) wr7, keep, cm5, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd5 c hc hu a ⟨hia.1, hia.2⟩]
      exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata,
      Memory.readN_congr (fun j hj => b3 _ (by omega) (by omega) (by omega))]
  · have e : ∀ j, j < 8 → μ7.read (rd + j) = μ5.read (rd + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (ffr _ (by omega) (by omega))
    rw [Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ7.read (rd + 8 + j) = μ5.read (rd + 8 + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (ffr _ (by omega) (by omega))
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
    exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.AssignGas in
/-- **`AssignForGasCost { core, queue, assigner }` with more than 512 hashes, the payload in the
    heap** (GP v0.8.0 B.7, tag 24): the variant-level composition behind `AssignGas.assign_gas_elemF`
    (handler 21075, frame S = A − 80: the `u16` core, ℰ(n), the hash reader 1764, the `u32` assigner,
    `ag1` … `ag5`) with the hash reader `VecHash.vec_hash_heap_big`, for 512 < n with 32n < 2³⁰ − 64,
    with A at least S0 + 592 (the reader at A − 80 needing S0 + 512). From 20626 with tag 24 read
    without error, the reader `{ptr, len}` at rd (ω₆) holding the core (2 octets), ℰ(n) (w octets), the
    n hashes (32n octets) and the assigner (4 octets), all inside an allocated chunk of the allocator's
    state `s` (context `HeapCtx`, under `refineContractK cap`): either `Instruction::decode` returns
    `AssignForGasCost` in O (the discriminant word 2^63 + 23, the `Vec` `{cap n, ptr q, len n}` at
    O + 8, the assigner's 4 octets at O + 32 and the core's 2 at O + 36, q holding the 32n octets of
    the hashes, the data of a fresh allocated chunk of n + 1 units), the reader advanced by
    2 + w + 32n + 4, the context kept for the final state `s'` and every allocated chunk of `s` kept
    with its data; or the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem assign_gas_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = UInt8.ofNat 24) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 592 ≤ A ∧ A + 56 ≤ S1) (hA8 : 2147484240 ≤ A ∧ A % 8 = 0)
    (hn : 512 < n ∧ 32 * n < 1073741760)
    (hlen : 2 + (Blob.encodeNat n).length + 32 * n + 4 ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 38 ≤ S1) (hOr : O + 38 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 2 + (Blob.encodeNat n).length + 32 * n + 4 ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN (ptr + 2) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (267800 + VecHash.hashSteps 512 (n - 512)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775831 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 32) 4 = μ.readN (ptr + 2 + (Blob.encodeNat n).length + 32 * n) 4 ∧
      μ'.readN (O + 36) 2 = μ.readN ptr 2 ∧
      μ'.readN q (32 * n) = μ.readN (ptr + 2 + (Blob.encodeNat n).length) (32 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 2 + (Blob.encodeNat n).length + 32 * n + 4) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 2 - (Blob.encodeNat n).length - 32 * n - 4) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (32 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (32 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 38 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (267800 + VecHash.hashSteps 512 (n - 512)) := by
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
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hra : ∀ a, ptr ≤ a → a < ptr + 2 + w + 32 * n + 4 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  have hws : ∀ a, A - 592 ≤ a → a < A + 56 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hcv : Num.decodeLE (μ.readN ptr 2) < 65536 := by
    have := decodeLE_lt (μ.readN ptr 2); simpa [Memory.length_readN] using this
  have ec : Num.encodeLE 2 (Num.decodeLE (μ.readN ptr 2)) = μ.readN ptr 2 := by
    have := encodeLE_decodeLE (μ.readN ptr 2); simpa [Memory.length_readN] using this
  obtain ⟨hgv, eg⟩ := Services.Bootstrap.Decode.Bless.u32_of (μ := μ) (a := ptr + 2 + w + 32 * n)
  -- the dispatch and the handler's frame S = A − 80
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 24
    (by decide) (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  rw [show handler 24 = 21075 from rfl] at run1
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    ag1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1)
      (e5'.trans F.h5) (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) (by omega))
  -- the core, into S + 32
  obtain ⟨ω3, μ3, run3, g0, g1, -, -, -, g5, g6, -, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1174 25390 (A - 80) rd (A - 48) ptr len 2
      f0 f1 f7 f8 f9 (by decide) jte_586 bs_25390 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hlen.2
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- the core parked, and the call of decodeU32
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k24, kfr, krd, kwr⟩ :=
    ag2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (A - 80) O rd
      (Num.decodeLE (μ.readN ptr 2)) ⟨by omega, by omega⟩ (g1.trans f1) (g5.trans f5) (g6.trans f6) g7
      hrd64 hcv
      (by
        rw [show A - 80 + 32 = A - 48 by omega, gbuf, Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]
        exact ec.symm)
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  have pay4 : ∀ b, ptr ≤ b → b < ptr + 2 + w + 32 * n + 4 → μ4.read b = μ.read b := fun b h1 h2 =>
    (kfr b (by omega) (by omega)).trans ((gfr b (by omega) (by omega) (by omega) (by omega)).trans
      (ffr b (by omega) (by omega)))
  -- the length ℰ(n)
  obtain ⟨ω5, μ5, run5, ⟨e0, e1, -, -, -, e5, e6, -, e7, e8, eR0, eR8, efr, erd, ewr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 1176 25408 (A - 80) rd (ptr + 2)
      (len - 2) k0 k1 k7 (by decide) jte_587 bs_25408 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8)
      n (by omega) (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd, frd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hW] at eR0 eR8
  -- the heap is as it was so far
  have b5 : ∀ a, a < 4294967296 → (a < A - 208 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (efr a h0 (by omega) h2).trans ((kfr a h0 (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))
  have wr5 : ∀ a, μ5.writable a = μ.writable a := fun a => by rw [ewr, kwr, gwr, fwr]
  have H5 : HeapCtx env pb S0 S1 μ5 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b5 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr5
  -- the call of the hash reader
  obtain ⟨ω6, run6, a0, a1, a5, a6, a7, a8, a9⟩ :=
    ag3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (A - 80) O rd n (by omega)
      (by rw [e1, k1]) (by rw [e5, k5]) (by rw [e6, k6]) e7 e8 (by omega) hrd64
  have run06 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  -- the queue: n hashes, into a fresh Vec at S + 32
  rcases VecHash.vec_hash_heap_big (p := p) (P := P) env cap hcap1 hcap x ω6 μ5 s (A - 80) (A - 80 + 32) rd
      (ptr + 2 + w) (len - 2 - w) n 1178 25431 O rd pb S0 S1 H5 ⟨cp, hcpm, hcpu, by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by decide) jte_588 bs_25431 hO64 hrd64 hn
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) eR0 eR8 with
    ⟨q, s', ω7, μ7, run7, v0, v1, v5', v6', vO, vO8, vO16, vdata, vR0, vR8, H7, keep, cm7, hfresh, kd7, -, vfr,
      vlo, vgl, vwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run06 ex).mono (by omega))
  have hqT : q + 32 * n < 2147483648 := by
    have hc7 := chunk_in H7.wf cm7 rfl
    have := H7.hbT
    simp only at hc7
    omega
  have hst7 := H7.st
  -- the Vec copied, and the assigner's call
  obtain ⟨ω8, μ8, run8, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    ag4 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (A - 80) O rd n q n
      ⟨by omega, by omega⟩ v1 v5' v6' hrd64 (by omega) (by omega) (by omega) vO
      (by rw [show A - 80 + 40 = A - 80 + 32 + 8 by omega]; exact vO8)
      (by rw [show A - 80 + 48 = A - 80 + 32 + 16 by omega]; exact vO16)
      (fun a h1 h2 => hst7 a (by omega) (by omega))
  have pg8 : μ8.readN (ptr + 2 + w + 32 * n) 4 = μ.readN (ptr + 2 + w + 32 * n) 4 :=
    Memory.readN_congr (fun j hj => (mfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩).trans (b5 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))))
  obtain ⟨ω9, μ9, run9, n0, n1, -, -, -, n5, -, -, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 1180 25470 (A - 80) rd
      (A - 48) (ptr + 2 + w + 32 * n) (len - 2 - w - 32 * n) 4 m0 m1 m7 (by rw [m8]; congr 1; omega) m9
      (by decide) jte_589 bs_25470
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [mrd]; exact Memory.readable_of_writable (heap_writable H7 (keep cp hcpm hcpu) hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR0)
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR8)
  -- the frame above S + 56, from the handler's start to before the store
  have up9 : ∀ a, A - 24 ≤ a → a < 4294967296 → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ2.read a :=
    fun a h0 h1 h3 =>
    (nfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))).trans
      ((mfr a h1 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((vfr a h1 (by omega) h3 (Or.inr (by omega))).trans
      ((efr a h1 (Or.inr (by omega)) h3).trans ((kfr a h1 (Or.inr (by omega))).trans
        (gfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega)))))))
  have sH : ∀ a v, A - 80 ≤ a → a + 8 ≤ A - 56 → μ8.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))]
    exact h
  have sK4 : ∀ a v, A - 56 ≤ a → a + 8 ≤ A - 48 → μ4.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((mfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans ((vfr _ (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega))).trans (efr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))))))]
    exact h
  have sA : ∀ a v, A - 24 ≤ a → a + 8 ≤ A → μ2.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up9 _ (by omega) (by omega) (by omega))]; exact h
  have sv : ∀ a v, A ≤ a → a + 8 ≤ A + 56 → μ.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up9 _ (by omega) (by omega) (by omega)).trans
      (ffr _ (by omega) (Or.inr (by omega))))]; exact h
  have hst9 : ∀ a, S0 ≤ a → a < S1 → μ9.writable a = true := fun a h1 h2 => by
    rw [nwr, mwr]; exact hst7 a h1 h2
  -- the variant, into the slot O, and the returns
  obtain ⟨ω10, μ10, run10, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    ag5 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 (A - 80) O ret t v5 v6 rd
      n q n (Num.decodeLE (μ.readN (ptr + 2 + w + 32 * n) 4)) (Num.decodeLE (μ.readN ptr 2)) (by omega) (by omega)
      (Or.inr (by omega)) (n1.trans m1) (n5.trans m5) n7 F.hv5 F.hv6 hrd64 hO64 (by omega) (by omega) (by omega)
      hgv hcv
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24)
      (by rw [show A - 80 + 32 = A - 48 by omega, nbuf, pg8, eg])
      (by rw [show A - 80 + 72 = A - 8 by omega]; exact sA _ _ (by omega) (by omega) f72)
      (by rw [show A - 80 + 64 = A - 16 by omega]; exact sA _ _ (by omega) (by omega) f64)
      (by rw [show A - 80 + 56 = A - 24 by omega]; exact sA _ _ (by omega) (by omega) f56)
      (by rw [show A - 80 + 128 = A + 48 by omega]; exact sv _ _ (by omega) (by omega) F.s0)
      (by rw [show A - 80 + 120 = A + 40 by omega]; exact sv _ _ (by omega) (by omega) F.s5)
      (by rw [show A - 80 + 112 = A + 32 by omega]; exact sv _ _ (by omega) (by omega) F.s6)
      F.hret F.hjt F.hbt
      (fun a h1 h2 => hst9 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst9 a (by omega) (by omega)))
  have low10 : ∀ a, a < 2147483648 → μ10.read a = μ7.read a := fun a ha =>
    (ofr a (by omega) (Or.inl (by omega))).trans ((nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))))
  have H10 : HeapCtx env pb S0 S1 μ10 s' :=
    ctx_congr_data H7 cm7 (fun a h1 _ => low10 a h1) (fun a => by rw [owr, nwr, mwr])
  have run := run06.trans (run7.trans (run8.trans (run9.trans run10)))
  refine Or.inl ⟨q, s', ω10, μ10, run.mono (by omega), o0, (by rw [o1]; congr 1; omega), o5, o6, oO, oO8, oO16,
    oO24, by rw [oO32, eg], by rw [oO36, ec], ?_, ?_, ?_, H10, keep, cm7, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      have hia' := hia
      unfold InData at hia'
      rw [low10 a (by omega), kd7 c hc hu a hia]
      exact b5 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => low10 _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b5 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (by omega)), nR0]
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (by omega)), nR8]
  · intro a h0 h1 h2 h3
    rw [ofr a h0 h3, up9 a (by omega) h0 h2]
    exact ffr a h0 (Or.inr h1)
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [low10 a (by omega), vgl a ha']
    exact b5 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.LookedUp in
/-- **`LookedUp { data: Some(bytes) }` with more than 16384 octets, the payload in the heap** (GP v0.8.0
    B.7, tag 18): as `LookedUp.looked_up_heap`, for 16384 < n = |bytes| < 2³⁰ − 64, with A at least
    S0 + 512 (`read_vec` at A − 56 needing S0 + 456, `VecU8.vec_u8_heap_big`). Either
    `Instruction::decode` returns `LookedUp { data: Some(bytes) }` in O (the discriminant word
    2^63 + 17, the `Vec` `{cap n, ptr q, len n}` at O + 8, the n octets at q, the data of a fresh
    allocated chunk of ⌈n/32⌉ + 1 units), the reader advanced by 1 + w + n, the context kept for the
    final state `s'` and every allocated chunk of `s` kept with its data; or the run reaches a failed
    allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem looked_up_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 18) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 512 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484160 ≤ A ∧ A % 8 = 0)
    (hn : 16384 < n ∧ n < 1073741760)
    (hlen : 1 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (34800 + VecU8.loopSteps 16384 (n - 16384)) ∧
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
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (34800 + VecU8.loopSteps 16384 (n - 16384)) := by
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
  rcases vec_u8_heap_big (p := p) (P := P) env cap hcap1 hcap x ω7 μ6 s (A - 56) (A - 56) rd
      (ptr + 1 + w) (len - 1 - w) n 1686 36016 A rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5, k5, g5]) hv6 o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_842 bs_36016 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, pg8, vfr, -, vgl, -⟩ |
    ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run07 ex).mono (by omega))
  have hst8 := H8.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 32 ≤ a → a < A + 56 → a ≠ A - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hqT : q + n < 2147483648 := by
    have hc8 := chunk_in H8.wf cm8 rfl
    have := H8.hbT
    simp only at hc8
    omega
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
  refine Or.inl ⟨q, s', ω10, μ10, run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
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

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.Provide in
/-- **`Provide { service, preimage: Inline(bytes) }` with more than 16384 octets, the payload in the
    heap** (GP v0.8.0 B.7, tag 17): as `Provide.provide_inline_heap`, for 16384 < n = |bytes| < 2³⁰ − 64,
    with A at least S0 + 608 (`read_vec` at A − 152 needing S0 + 456, `VecU8.vec_u8_heap_big`). Either
    `Instruction::decode` returns the variant in O (the discriminant word 2^63 + 16, `Inline` (1) at
    O + 8, the `Vec` `{cap n, ptr q, len n}` at O + 16, the service's 4 octets at O + 48, the n octets
    at q, the data of a fresh allocated chunk of ⌈n/32⌉ + 1 units), the reader advanced by 5 + w + n,
    the context kept for the final state `s'` and every allocated chunk of `s` kept with its data; or
    the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem provide_inline_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 608 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147484256 ≤ A ∧ A % 8 = 0) (hn : 16384 < n ∧ n < 1073741760)
    (hlen : 5 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 52 ≤ S1) (hOr : O + 52 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 5 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hinl : μ.read (ptr + 4) = 1) (henc : μ.readN (ptr + 5) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (35100 + VecU8.loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 32) 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 48) 4 = μ.readN ptr 4 ∧
      μ'.readN q n = μ.readN (ptr + 5 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 5 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 5 - (Blob.encodeNat n).length - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (35100 + VecU8.loopSteps 16384 (n - 16384)) := by
  have hA2 := F.hA
  have hS1' := H.hS1
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hra : ∀ a, ptr ≤ a → a < ptr + 5 + (Blob.encodeNat n).length + n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, atag, apark, a982, aO, ard, aR0, aR8, afr, ard', awr⟩ :=
    pi_pre (p := p) (P := P) (R := refineContractK cap env) x ω μ A O ret t v5 v6 rd ptr len n F ⟨by omega, hA8.2⟩
      h6 h7 tag tab hrt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, hlen.2⟩ hinl henc hR0 hR8
      (Or.inr hrd.1) (Or.inl (by omega)) (by omega) hO64 (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hra a h1 (by omega))
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen henc hcp2 hra hw1 aR0 aR8 ⊢
  have b1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h0 => afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_congr_data H hcpm (fun a h1 _ => b1 a h1) awr
  rcases vec_u8_heap_big (p := p) (P := P) env cap hcap1 hcap x ω1 μ1 s (A - 152) (A - 152 + 80) rd
      (ptr + 5 + w) (len - 5 - w) n 1168 25153 O rd pb S0 S1 H1 ⟨cp, hcpm, hcpu, by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ a0 a1 a5 a6 a7 a8 a9 (by decide) jte_583 bs_25153 hO64 (by omega) hn
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) aR0 aR8 with
    ⟨q, s', ω2, μ2, run2, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H2, keep, cm2, hfresh, kd2, pg2, vfr, -, vgl, -⟩ |
    ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 ex).mono (by omega))
  have hst2 := H2.st
  have hqT : q + n < 2147483648 := by
    have hc2 := chunk_in H2.wf cm2 rfl
    have := H2.hbT
    simp only at hc2
    omega
  have hS2 : ∀ a, A - 152 ≤ a → a < 4294967296 → (a < A - 152 + 80 ∨ A - 152 + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ2.read a = μ1.read a := fun a h1 h2 h3 h4 => vfr a h2 h1 h4 (by omega)
  obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO48, zfr, zrd, zwr⟩ :=
    pi_post (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 A O ret t v5 v6 n q n (rdN μ1 (A - 152 + 8) 8) rd
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
  have run := run1.trans (run2.trans run3)
  have wr3 : ∀ a, μ3.writable a = μ2.writable a := zwr
  refine Or.inl ⟨q, s', ω3, μ3, run.mono (by omega), z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, ?_, ?_, ?_, ?_,
    ctx_congr_data H2 cm2 (fun a h1 _ => hlow a h1) wr3, keep, cm2, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd2 c hc hu a ⟨hia.1, hia.2⟩]
      exact b1 a (by omega),
    FreeStepsH.pagesOut H.bd run, ?_, ?_, ?_, ?_⟩
  · rw [zO48, ← take_encodeLE, encodeLE_rdN]; exact apark
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR0
  · rw [Memory.readN_congr (fun j hj => zfr _ (by omega) (by omega) (by omega))]; exact vR8
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) h3, vfr a h0 (by omega) h2 (by omega)]; exact afr a h0 (Or.inr h1) h2
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlow a (by omega), vgl a ha']
    exact b1 a (by omega)
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.LookedUp Services.Bootstrap.Decode.CreateService in
/-- **`Option<Vec<u8>>::decode` of `Some(bytes)` with more than 16384 octets, the payload in the heap**
    (GP v0.8.0 B.7, `CreateService`'s code): as `CreateService.opt_vec_heap` (from 35937, the slot at
    sp + 232, return address 1130), for 16384 < n = |bytes| < 2³⁰ − 64, with sp at least S0 + 512
    (`read_vec` at sp − 56 needing S0 + 456, `VecU8.vec_u8_heap_big`). Either the decoder returns to
    24265 with the `Vec` `{cap n, ptr q, len n}` in the slot, the n octets at q (the data of a fresh
    allocated chunk of ⌈n/32⌉ + 1 units), the context kept for the final state `s'` and every
    allocated chunk of `s` kept with its data; or the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem opt_vec_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (sp v5 v6 rd ptr len n pb S0 S1 : Nat)
    (h0 : ω[0] = UInt64.ofNat 1130) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (sp + 232)) (h8 : ω[8] = UInt64.ofNat rd)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 512 ≤ sp ∧ sp + 256 ≤ S1)
    (hA8 : 2147484160 ≤ sp ∧ sp % 8 = 0)
    (hn : 16384 < n ∧ n < 1073741760)
    (hlen : 1 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : sp + 256 ≤ rd ∧ rd + 16 ≤ S1)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 35937 ω μ x 24265 ω' μ' x
        (34750 + VecU8.loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat 1130 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (sp + 232) 8 = Num.encodeLE 8 n ∧ μ'.readN (sp + 240) 8 = Num.encodeLE 8 q ∧
      μ'.readN (sp + 248) 8 = Num.encodeLE 8 n ∧
      μ'.readN q n = μ.readN (ptr + 1 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1 - (Blob.encodeNat n).length - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < sp + 232 ∨ sp + 256 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 35937 ω μ x (34750 + VecU8.loopSteps 16384 (n - 16384)) := by
  have hst := H.st
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have hO64 : sp + 232 < 18446744073709551616 := by omega
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
  have hws : ∀ a, sp - 400 ≤ a → a < sp + 256 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp (sp + 232) rd 1130 v5 v6 ⟨by omega, by omega⟩
      hO64 (by omega) (by omega) hv5 hv6 h0 h1 h5 h6 h7 h8 (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 1682 35970 (sp - 56) rd (sp - 25) ptr len 1
      g0 g1 g7 g8 g9 (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (sp - 56 + 31) = 1 := by
    rw [show sp - 56 + 31 = sp - 25 by omega, read_of_readN1 kbuf, ← hsome]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := o_some (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4
    (sp - 56) ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have pay4 : ∀ a, ptr ≤ a → a < ptr + 1 + w + n → μ4.read a = μ.read a := fun a h1 h2 =>
    (kfr a (by omega) (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ4 1684 35994 (sp - 56) rd (ptr + 1) (len - 1)
      m0 (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_841 bs_35994 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := o_len (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    (sp - 56) n (by omega) (by omega) (by rw [d1, m1, k1', g1]) d7 d8
  have b6 : ∀ a, a < 4294967296 → (a < sp - 400 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [dwr, kwr, gwr]
  have H6 : HeapCtx env pb S0 S1 μ6 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr6
  have hv6' : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  have run07 := run3.trans (run4.trans (run5.trans (run6.trans run7)))
  rcases vec_u8_heap_big (p := p) (P := P) env cap hcap1 hcap x ω7 μ6 s (sp - 56) (sp - 56) rd
      (ptr + 1 + w) (len - 1 - w) n 1686 36016 (sp + 232) rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5, k5, g5]) hv6' o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_842 bs_36016 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, pg8, vfr, -,
      vgl, -⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run07 ex).mono (by omega))
  have hst8 := H8.st
  have hfA : ∀ a, sp - 32 ≤ a → a < sp → a ≠ sp - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hqT : q + n < 2147483648 := by
    have hc8 := chunk_in H8.wf cm8 rfl
    have := H8.hbT
    simp only at hc8
    omega
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    o_copy (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 (sp - 56) (sp + 232) n q n 1130 24265 v5 v6
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) hv5 hv6 vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show sp - 56 + 48 = sp - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show sp - 56 + 40 = sp - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show sp - 56 + 32 = sp - 24 by omega]; exact gs6)
      (by decide) jte_564 bs_24265
      (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
      (fun a h1 h2 => hst8 a (by omega) (by omega))
  have hlow : ∀ a, a < 2147483648 → μ9.read a = μ8.read a := fun a h0 => cfr a (by omega) (by omega)
  have run := run07.trans (run8.trans run9)
  have wr9 : ∀ a, μ9.writable a = μ8.writable a := fun a => by rw [cwr]
  refine Or.inl ⟨q, s', ω9, μ9, run.mono (by omega), c0, by rw [c1]; congr 1; omega, c5, c6, cO, cO8, cO16,
    ?_, ?_, ?_, ctx_congr_data H8 cm8 (fun a h1 _ => hlow a h1) wr9, keep, cm8, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at hia
      rw [hlow a (by omega), kd8 c hc hu a ⟨hia.1, hia.2⟩]
      exact b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)), ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega)), vR0]
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega)), vR8]
  · intro a h0 h1 h2 h3
    rw [cfr a h0 h3]; exact (vfr a h0 (by omega) h2 (by omega)).trans (b6 a h0 (by omega) h2)
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

open Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.LookedUp Services.Bootstrap.Decode.CreateService in
/-- **`CreateService { …, Option<Vec<u8>>: Some(bytes), … }` with more than 16384 octets, the payload
    in the heap** (GP v0.8.0 B.7, tag 0): as `CreateService.create_service_heap` (from `cs_head`,
    `opt_vec_heap_big` and `cs_tail`), for 16384 < n = |bytes| < 2³⁰ − 64, with S at least S0 + 512.
    Either `Instruction::decode` returns `CreateService` in its slot O (the `Vec` `{cap n, ptr q, len n}`
    at O, the n octets at q, the data of a fresh allocated chunk of ⌈n/32⌉ + 1 units, the rest as in
    `create_service_heap`), the context kept for the final state `s'` and every allocated chunk of `s`
    kept with its data; or the run reaches a failed allocator call (`Exhausts`).

    The globals below the allocator (`Glob`) are kept. *Not stated:* the model `alloc` equation (see
    the module doc). -/
theorem create_service_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (S O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (ou : List UInt8) (F : Frame P (S + 384) O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (S + 384) = 0) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 512 ≤ S) (hA8 : 2147484160 ≤ S ∧ S % 8 = 0)
    (hO : O % 8 = 0 ∧ S + 440 ≤ O) (hrd : O + 256 ≤ rd ∧ rd + 16 ≤ S1)
    (hn : 16384 < n ∧ n < 1073741760) (hou : ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u)
    (hlen : 201 + (Blob.encodeNat n).length + n + ou.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 201 + (Blob.encodeNat n).length + n + ou.length ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read (ptr + 192) = 1)
    (henc : μ.readN (ptr + 193) (Blob.encodeNat n).length = Blob.encodeNat n)
    (pay : μ.readN (ptr + 201 + (Blob.encodeNat n).length + n) ou.length = ou) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (38400 + VecU8.loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧
      μ'.readN q n = μ.readN (ptr + 193 + (Blob.encodeNat n).length) n ∧
      μ'.readN (O + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat ∧
      (ou.headD 0 = 1 → μ'.readN (O + 28) 4 = ou.tail) ∧
      μ'.readN (O + 32) 32 = μ.readN ptr 32 ∧
      μ'.readN (O + 64) 8 = μ.readN (ptr + 32) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (ptr + 40) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (ptr + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (ptr + 56) 8 ∧
      μ'.readN (O + 96) 128 = μ.readN (ptr + 64) 128 ∧
      μ'.readN (O + 224) 8 = μ.readN (ptr + 193 + (Blob.encodeNat n).length + n) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 201 + (Blob.encodeNat n).length + n + ou.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (201 + (Blob.encodeNat n).length + n + ou.length)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → S + 384 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (38400 + VecU8.loopSteps 16384 (n - 16384)) := by
  have hA2 := F.hA
  have hst := H.st
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  have hol : 1 ≤ ou.length ∧ ou.length ≤ 5 := by rcases hou with rfl | ⟨u, hu, rfl⟩ <;> simp [*]
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by
    rw [← hW]; unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  simp only [hW] at hlen henc hpay pay ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hra : ∀ a, ptr ≤ a → a < ptr + 201 + w + n + ou.length → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  -- the fixed-size fields
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a376, a368, a360, ahash, a64, a56, a48, a40, aarr, aR0, aR8,
      afr, ard, awr⟩ :=
    cs_head (p := p) (P := P) (R := refineContractK cap env) x ω μ S O ret t v5 v6 rd ptr len F
      ⟨by omega, hA8.2⟩ h6 h7 tag tab hrt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, hlen.2⟩ hR0 hR8
      (by omega) (by omega) (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hra a h1 (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s :=
    ctx_congr_data H hcpm (fun a h1 _ => afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) awr
  have pay1 : ∀ a, ptr ≤ a → a < ptr + 201 + w + n + ou.length → μ1.read a = μ.read a := fun a h1 h2 =>
    afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  -- the Option<Vec<u8>>
  rcases opt_vec_heap_big (p := p) (P := P) env cap hcap1 hcap x ω1 μ1 s S O rd rd (ptr + 192) (len - 192) n
      pb S0 S1 a0 a1 a5 a6 a7 a8 (by omega) (by omega) H1 ⟨by omega, by omega⟩ hA8 hn
      ⟨by rw [hW]; omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨cp, hcpm, hcpu, by omega, by rw [hW]; omega⟩
      aR0 aR8 (by rw [pay1 _ (by omega) (by omega)]; exact hsome)
      (by rw [hW, Memory.readN_congr (fun j hj => pay1 _ (by omega) (by omega))]; exact henc) with
    ⟨q, s', ω2, μ2, run2, g0, g1, g5, g6, gW, gq, gn, gdat, gR0, gR8, H2, keep, cm, hfresh, kd2, gfr, glo, ggl,
      gwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run1 ex).mono (by omega))
  rw [hW] at gdat gR0 gR8
  have hst2 := H2.st
  have hqT : q + n < 2147483648 := by
    have hc2 := chunk_in H2.wf cm rfl
    have := H2.hbT
    simp only at hc2
    omega
  have cp2 := keep cp hcpm hcpu
  have pay2 : ∀ a, ptr ≤ a → a < ptr + 201 + w + n + ou.length → μ2.read a = μ.read a := fun a h1 h2 =>
    (kd2 cp hcpm hcpu a ⟨by omega, by omega⟩).trans (pay1 a h1 h2)
  have b21 : ∀ a, a < 4294967296 → S + 384 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => (gfr a h0 (by omega) h2 (by omega)).trans (afr a h0 (by omega) h2)
  -- u₅, the Option<u32> and the stores
  obtain ⟨ω3, μ3, run3, n0, n1, n5, n6, nO, nO8, nO16, nO24, nO28, nO32, nO64, nO72, nO80, nO88, nO96, nO224,
      nR0, nR8, nfr, nrd, nwr⟩ :=
    cs_tail (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 S O ret t v5 v6 rd (ptr + 193 + w + n)
      (len - 193 - w - n) n q n ou ⟨by omega, hA8.2, by omega⟩ ⟨hO.1, by omega⟩ (by omega) g1 g5 g6 (by omega)
      (by omega) (by omega) (by omega) gW gq gn
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega))]; exact a376)
      (by rw [Memory.readN_congr (fun j hj => b21 _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => b21 _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => b21 _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hv5 F.hv6 F.hret F.hjt F.hbt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hou ⟨by omega, by omega⟩
      (gR0.trans (congrArg _ (by omega))) (gR8.trans (congrArg _ (by omega)))
      (by rw [Memory.readN_congr (fun j hj => pay2 _ (by omega) (by omega)), show ptr + 193 + w + n + 8 =
          ptr + 201 + w + n by omega]; exact pay)
      (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => hst2 a (by omega) (by omega)) (fun a h1 h2 => hst2 a (by omega) (by omega))
      (fun a h1 h2 => hst2 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (heap_writable H2 cp2 hcpu ⟨by omega, by omega⟩))
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
  have hlow : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a h0 =>
    nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have wr3 : ∀ a, μ3.writable a = μ2.writable a := nwr
  refine Or.inl ⟨q, s', ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), n0, n1, n5, n6, nO, nO8,
    nO16, ?_, nO24, nO28, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ctx_congr_data H2 cm (fun a h1 _ => hlow a h1) wr3, keep, cm, hfresh, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), gdat]
    exact Memory.readN_congr (fun j hj => pay1 _ (by omega) (by omega))
  · rw [nO32]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans ahash
  · rw [nO64]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans a64
  · rw [nO72]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans a56
  · rw [nO80]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans a48
  · rw [nO88]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans a40
  · rw [nO96]; exact Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega) (by omega) (by omega)) |>.trans aarr
  · rw [nO224]; exact Memory.readN_congr (fun j hj => pay2 _ (by omega) (by omega))
  · rw [nR0]; exact congrArg _ (by omega)
  · rw [nR8]; exact congrArg _ (by omega)
  · intro c hc hu a hia
    have := (chunk_in H.wf hc hu).2.2
    unfold InData at hia
    rw [hlow a (by omega), kd2 c hc hu a hia]
    exact afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a h0 h1 h2 h3
    rw [nfr a h0 (by omega) h2 h3]; exact b21 a h0 h1 h2
  · intro a ha'
    rw [hlow a (by omega), nrd, (glo a ha').1, (glo a ha').2, ard]
    exact ⟨afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)), rfl⟩
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [hlow a (by omega), ggl a ha']
    exact afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha'
    rw [wr3, gwr a ha', awr]

end Services.Bootstrap.Decode.VariantsBig2
