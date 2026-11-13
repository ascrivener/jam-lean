import Services.Bootstrap.Decode.CreateServiceRun
import Services.Bootstrap.Decode.LookedUpHeap

/-!
# `Instruction::decode` of `CreateService` with `Option<Vec<u8>>` = `Some(bytes)`, the payload in the heap

`opt_vec_heap`: `Option<Vec<u8>>::decode` (35937, `Services.Bootstrap.Decode.LookedUp`) called with its
slot at sp + 232 (as `CreateService`'s decoder calls it, return address 1130) on `Some(bytes)`,
1 ≤ |bytes| ≤ 16384, through `VecU8.vec_u8_heap`: the encoding lies inside an allocated chunk, the
allocator's context is `HeapCtx`, and the model's `alloc` failing is an outcome (null at the `alloc`
wrapper's return, 40611). `create_service_heap`: `CreateService` (tag 0; GP v0.8.0 B.7) with that
option, from `cs_head`, `opt_vec_heap` and `cs_tail`.
-/

namespace Services.Bootstrap.Decode.CreateService

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.LookedUp

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Option<Vec<u8>>::decode` of `Some(bytes)`, 1 ≤ n = |bytes| ≤ 16384, the payload in the heap**:
    from 35937 with sp = ω₁, the slot sp + 232 (ω₇), the reader rd (ω₈) holding 1 (`Some`), ℰ(n) (w
    octets) and n more octets inside an allocated chunk of `s` (context `HeapCtx`, under
    `refineContractK cap`), and return address 1130: either the model's `alloc` of ⌈n/32⌉ units gives
    `(q, s')` and the decoder returns to 24265 with the `Vec` `{cap n, ptr q, len n}` in the slot, the
    n octets at q, the context kept for `s'` and every allocated chunk of `s` kept with its data; or the
    model's `alloc` fails and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem opt_vec_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp v5 v6 rd ptr len n pb S0 S1 : Nat)
    (h0 : ω[0] = UInt64.ofNat 1130) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (sp + 232)) (h8 : ω[8] = UInt64.ofNat rd)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 400 ≤ sp ∧ sp + 256 ≤ S1)
    (hA8 : 2147484048 ≤ sp ∧ sp % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 16384)
    (hlen : 1 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : sp + 256 ≤ rd ∧ rd + 16 ≤ S1)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 1 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 35937 ω μ x 24265 ω' μ' x (2 * n + 1950) ∧
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
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 35937 ω μ x 40611 ω' μ' x (2 * n + 1950) ∧
      ω'[7] = UInt64.ofNat 0) := by
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
  rcases vec_u8_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω7 μ6 s (sp - 56) (sp - 56) rd
      (ptr + 1 + w) (len - 1 - w) n 1686 36016 (sp + 232) rd pb S0 S1 H6
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ o0
      (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5, k5, g5]) hv6' o7 (by rw [o8, d6, m6, k6, g6]) o9
      (by decide) jte_842 bs_36016 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω8, μ8, ha, run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H8, keep, cm8, hfresh, kd8, pg8, vfr, -,
      vgl, -⟩ | ⟨hna, ω8, μ8, run8, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω8, μ8, (run07.trans run8).mono (by omega), f7⟩
  have hst8 := H8.st
  have hfA : ∀ a, sp - 32 ≤ a → a < sp → a ≠ sp - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + n < 2147483648 := by
    have := chunk_in H8.wf cm8 rfl; simp only at this; rw [hbase'] at this; omega
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
  refine Or.inl ⟨q, s', ω9, μ9, ha, run.mono (by omega), c0, by rw [c1]; congr 1; omega, c5, c6, cO, cO8, cO16,
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

/-- **`CreateService { …, Option<Vec<u8>>: Some(bytes), … }`, 1 ≤ n = |bytes| ≤ 16384, the payload in
    the heap**: from 20626, with tag 0 read without error and the reader `{ptr, len}` at rd (ω₆) holding
    the 192 octets of h, u₁ … u₄ and the array, then 1 (`Some`), ℰ(n) (w octets), n octets, the 8 of u₅
    and the `Option<u32>` ou, all inside an allocated chunk of `s` (context `HeapCtx`, under
    `refineContractK cap`): either the model's `alloc` of ⌈n/32⌉ units gives `(q, s')` and
    `Instruction::decode` returns `CreateService` in its slot O (the `Vec` `{cap n, ptr q, len n}` at O,
    the n octets at q, the rest as in `create_service_none`), the context kept for `s'`, every allocated
    chunk of `s` kept with its data; or the model's `alloc` fails and the run reaches the `alloc`
    wrapper's return (40611) with null. -/
theorem create_service_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (S O ret t v5 v6 rd ptr len n pb S0 S1 : Nat)
    (ou : List UInt8) (F : Frame P (S + 384) O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (S + 384) = 0) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 400 ≤ S) (hA8 : 2147484048 ≤ S ∧ S % 8 = 0)
    (hO : O % 8 = 0 ∧ S + 440 ≤ O) (hrd : O + 256 ≤ rd ∧ rd + 16 ≤ S1)
    (hn : 1 ≤ n ∧ n ≤ 16384) (hou : ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u)
    (hlen : 201 + (Blob.encodeNat n).length + n + ou.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + 201 + (Blob.encodeNat n).length + n + ou.length ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read (ptr + 192) = 1)
    (henc : μ.readN (ptr + 193) (Blob.encodeNat n).length = Blob.encodeNat n)
    (pay : μ.readN (ptr + 201 + (Blob.encodeNat n).length + n) ou.length = ou) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (2 * n + 5600) ∧
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
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (2 * n + 5600) ∧
      ω'[7] = UInt64.ofNat 0) := by
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
  rcases opt_vec_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s S O rd rd (ptr + 192) (len - 192) n
      pb S0 S1 a0 a1 a5 a6 a7 a8 (by omega) (by omega) H1 ⟨by omega, by omega⟩ hA8 hn
      ⟨by rw [hW]; omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨cp, hcpm, hcpu, by omega, by rw [hW]; omega⟩
      aR0 aR8 (by rw [pay1 _ (by omega) (by omega)]; exact hsome)
      (by rw [hW, Memory.readN_congr (fun j hj => pay1 _ (by omega) (by omega))]; exact henc) with
    ⟨q, s', ω2, μ2, ha, run2, g0, g1, g5, g6, gW, gq, gn, gdat, gR0, gR8, H2, keep, cm, hfresh, kd2, gfr, glo, ggl,
      gwr⟩ | ⟨hna, ω2, μ2, run2, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω2, μ2, (run1.trans run2).mono (by omega), f7⟩
  rw [hW] at gdat gR0 gR8
  have hst2 := H2.st
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + n < 2147483648 := by
    have := chunk_in H2.wf cm rfl; simp only at this; rw [hbase'] at this; omega
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
  refine Or.inl ⟨q, s', ω3, μ3, ha, (run1.trans (run2.trans run3)).mono (by omega), n0, n1, n5, n6, nO, nO8,
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

end Services.Bootstrap.Decode.CreateService
