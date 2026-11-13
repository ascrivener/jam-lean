import Services.Bootstrap.Decode.Designate
import Services.Bootstrap.Decode.VecKey336
import Services.Bootstrap.Decode.Elems

/-!
# `Instruction::decode` of `Designate { keys }`, the keys in the heap

`Designate { keys: BoundedVec<[u8; 336], 3·𝖢> }` (tag 13; GP v0.8.0 B.7, the bootstrap service's
instruction list) is decoded by a helper with a 48-octet frame at H = A − 48 (`Designate.d1`): it decodes
the length n (`decodeU32`), checks n against 3·𝖢 (𝖢 the 16-bit word at 196616), calls the key reader
(1300, `VecKey336.vec_key336_heap`) for n keys into a `Vec` at H, copies it to A (`Designate.d3`), and
`Instruction::decode` copies the three words at A to O + 8 after the discriminant word 2^63 + 12
(`Designate.d4`).

The bound check (35293 … 35315, `d2n`) loads 𝖢 sign-extended, computes 3·𝖢 and zero-extends it from
16 bits, so the code accepts n ≤ (3·𝖢) mod 2^16; for the start-up's 𝖢 = 341 that is 3·𝖢 = 1023.

* `designate_heap`: with 1 ≤ n ≤ 48 keys (one reservation batch of the key reader), through
  `vec_key336_heap`. The encoding lies inside an allocated chunk, the allocator's context is `HeapCtx`,
  and the model's `alloc` failing is an outcome (null at the `alloc` wrapper's return, 40611). The keys
  land in the block in their in-memory layout (`VecKey336.keysRot`: each key's last 128 octets, then
  its first 208).
* `designate_elem`: the same, as an element of the decode loop (`ElemOkAF`) at a frame base F with
  `Lay F RD`, 𝖢 read from the globals `gl`.
-/

namespace Services.Bootstrap.Decode.Designate

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 35293 … 35342: the length n ≥ 1 was decoded (ω₇ = 0, ω₈ = n < 2^31): the decoder loads the core
    count 𝖢 (the 16-bit word at 196616, sign-extended), computes 3·𝖢 truncated to 16 bits and, as
    n ≤ (3·𝖢) mod 2^16, calls the key reader (1300) for n keys into a `Vec` at H (ω₇ = H = ω₁, ω₈ =
    the reader ω₆, ω₉ = n), return address 1650. -/
theorem d2n {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H n C : Nat)
    (hH : H < 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat n) (hn : n < 2147483648)
    (hC : μ.readN 196616 2 = Num.encodeLE 2 C) (hnC : n ≤ 3 * C % 65536)
    (hc : ∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 35293 ω μ x 1300 ω' μ x 14 ∧
      ω'[0] = UInt64.ofNat 1650 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat H ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat n := by
  have rc : rdN μ 196616 2 = C % 65536 := by
    unfold rdN; rw [hC, Num.decodeLE_encodeLE]
  have hge : (rdN μ 196616 2 % 65536 + rdN μ 196616 2 % 65536 / 32768 * 18446744073709486080 +
      (rdN μ 196616 2 % 65536 + rdN μ 196616 2 % 65536 / 32768 * 18446744073709486080) * 2 %
        18446744073709551616) % 18446744073709551616 % 65536 ≥ n := by
    rw [rc]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h8, hn, hc, hH, hge, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx in
/-- The globals (196608 … 196792) lie on the heap's first page, which is writable. -/
theorem glob_writable' {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {a : Nat} (ha : 196608 ≤ a ∧ a < 196792) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecKey336 in
/-- **`Designate { keys }` with 1 ≤ n ≤ 48 keys, the payload in the heap** (GP v0.8.0 B.7, tag 13):
    from 20626, with tag 13 read without error, the core count 𝖢 at 196616 (ℰ₂(𝖢)) with
    n ≤ (3·𝖢) mod 2^16 (the code's bound, 3·𝖢 truncated to 16 bits) and the reader `{ptr, len}` at rd
    (ω₆) holding ℰ(n) (w octets) and the n keys (336n octets), all inside an allocated chunk of the
    allocator's state `s` (context `HeapCtx`, under `refineContractK cap`), either the model's `alloc`
    of ⌈336n/32⌉ units gives `(q, s')` and `Instruction::decode` returns `Designate { keys }` in O (the
    discriminant word 2^63 + 12, the `Vec` `{cap n, ptr q, len n}` at O + 8, the keys at q in their
    in-memory layout `keysRot`), the reader advanced by w + 336n, the context kept for `s'`, every
    allocated chunk of `s` kept with its data; or the model's `alloc` fails and the run reaches the
    `alloc` wrapper's return (40611) with null. -/
theorem designate_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (A O ret t v5 v6 rd ptr len n C pb S0 S1 : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 13) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hC : μ.readN 196616 2 = Num.encodeLE 2 C) (hnC : n ≤ 3 * C % 65536)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 1648 ≤ A ∧ A + 56 ≤ S1)
    (hA8 : 2147485296 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ n ∧ n ≤ 48)
    (hlen : (Blob.encodeNat n).length + 336 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat n).length + 336 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((336 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x (8200 * n + 2000) ∧
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
    (alloc (growTo pb) hb 1 ((336 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x (8200 * n + 2000) ∧
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
  rcases vec_key336_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48)
      rd (ptr + w) (len - w) n 1650 35349 A rd pb S0 S1 H3
      ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ c0
      (by rw [c1, d1', b1]) (by rw [c5, d5, b5]) hv6 c7 (by rw [c8, d6, b6]) c9
      (by decide) jte_824 bs_35349 (by omega) (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
    ⟨q, s', ω5, μ5, ha, run5, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H5, keep, cm5, hfresh, kd5, -, vfr, -,
      vgl, -⟩ | ⟨hna, ω5, μ5, run5, f7⟩
  rotate_left
  · exact Or.inr ⟨hna, ω5, μ5, (run04.trans run5).mono (by omega), f7⟩
  have hst5 := H5.st
  -- the copy to A and the variant
  have hfA : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a :=
    fun a h1 h2 => (vfr a (by omega) (by omega) (by omega) (by omega)).trans
      (dfr a (by omega) (by omega) (by omega))
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hqT : q + 336 * n < 2147483648 := by
    have := chunk_in H5.wf cm5 rfl; simp only at this; rw [hbase'] at this; omega
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
  refine Or.inl ⟨q, s', ω7, μ7, ha, run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
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

/-! ## As an element of the decode loop -/

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.VecKey336

/-- **`Designate`'s slot** (GP v0.8.0 B.7, tag 13): the discriminant word 2^63 + 12 and the `Vec`
    `{cap n, ptr q, len n}` at 8 for some q whose 336n octets (in the heap μ) are the n keys ks in their
    in-memory layout (`keysRot`: each key's last 128 octets, then its first 208). -/
def DesignateRep (n : Nat) (ks : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775820 ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (336 * n) = keysRot n ks

/-- The globals' octets at 196616 … 196618 read as ℰ₂(𝖢) in every memory that holds `gl` there. -/
theorem glob_core {gl : Nat → UInt8} {C : Nat}
    (gv : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 C) {μ : Memory}
    (hg : ∀ a, Glob a → μ.read a = gl a) : μ.readN 196616 2 = Num.encodeLE 2 C := by
  rw [← gv]
  unfold Memory.readN
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  exact hg _ ⟨by omega, by omega⟩

/-- **`Designate { keys }`, as an element of the decode loop** (GP v0.8.0 B.7, tag 13): with the
    globals `gl` holding ℰ₂(𝖢) at 196616 and 1 ≤ n ≤ 48 keys, n ≤ (3·𝖢) mod 2^16 (the code's bound),
    the encoding 13 :: ℰ(n) ++ ks, with ks the 336n octets of the keys, decodes to `DesignateRep`, the
    keys a fresh chunk of the heap; or the `alloc` fails. -/
theorem designate_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (C : Nat) (gv : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 C)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 48) (hnC : n ≤ 3 * C % 65536) (ks : List UInt8) (hk : ks.length = 336 * n) :
    ElemOkAF env cap pb gl p P F RD (8200 * n + 2000) (13 :: (Blob.encodeNat n ++ ks))
      (DesignateRep n ks) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hg
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (13 :: (Blob.encodeNat n ++ ks)).length - 1 = w + 336 * n := by simp [hW, hk]
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have henc : μ.readN ptr w = Blob.encodeNat n := by
    have := readN_sub μ ptr (w + 336 * n) 0 w _ pay (by omega)
    rw [Nat.add_zero, List.drop_zero, List.take_left' hW] at this
    exact this
  have hitems : μ.readN (ptr + w) (336 * n) = ks := by
    have := readN_sub μ ptr (w + 336 * n) w (336 * n) _ pay (by omega)
    rw [List.drop_left' hW, List.take_of_length_le (by omega)] at this
    exact this
  rcases designate_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n C pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt (glob_core gv hg) hnC H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1; omega,
      by rw [gR8]; congr 1; omega, ⟨9223372036854775820, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (336 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
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
          ⟨by simp only; omega, by simp only; omega⟩), gdat, hitems]
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end Services.Bootstrap.Decode.Designate
