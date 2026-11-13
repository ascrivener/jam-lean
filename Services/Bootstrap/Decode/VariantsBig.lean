import Services.Bootstrap.Decode.VecPairsBig
import Services.Bootstrap.Decode.VecVecU8Big

/-!
# `Import`, `DeleteItems`, `Export` and `Imported` with the large readers, the payload in the heap

The variant-level compositions of `Instruction::decode` (20626) with the element readers without
their small-n limits (GP v0.8.0 B.7, the bootstrap service's instruction list):

* `import_heap_big`: `Import { items: Vec<(u64, u64)> }` (tag 9) with n > 1024 items, as
  `VecPairs.import_heap` with the pair reader `VecPairs.vec_pairs_heap_big`;
* `vecvec_heap_big`: `DeleteItems`, `Export`, `Imported` (tags 5, 10, 19, items `Vec<Vec<u8>>`)
  with any n ≥ 1 items of any length, with the element reader `VecVecU8.vec_vec_u8_heap_big`.

The decoder dispatches on the tag, opens its helper frame at A − 48 (`VecEmpty.e1`), decodes the
length (`decodeU32`), calls the reader (`VecEmpty.e2`), copies the `Vec` into the slot O with the
discriminant word (`VecEmpty.e3`) and returns (`VecEmpty.e4`).

Either the decoder returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

The globals below the allocator (`Glob`) are kept, as in the small compositions. *Not stated*
(unlike the small composition): the model `alloc` equation of `import_heap` (`vec_pairs_heap_big`
does not state it).
-/

namespace Services.Bootstrap.Decode.VariantsBig

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Alloc
  JAM Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecEmpty

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Import { items }` with more than 1024 items, the payload in the heap** (GP v0.8.0 B.7): as
    `VecPairs.import_heap`, for 1024 < n with 16n < 2³⁰ − 64, with A at least S0 + 528 (the reader at
    A − 48 needing S0 + 480, `VecPairs.vec_pairs_heap_big`). From 20626 with tag 9 read without error,
    the reader `{ptr, len}` at rd (ω₆) holding ℰ(n) (w octets) and the n items (16 octets each), all
    inside an allocated chunk of the allocator's state `s` (context `HeapCtx`, under
    `refineContractK cap`): either `Instruction::decode` returns `Import` in O (the discriminant word
    2^63 + 8 and the `Vec` `{cap n, ptr q, len n}` at O + 8, q holding the 16n item octets, the data
    of a fresh allocated chunk of ⌈16n/32⌉ + 1 units), the reader advanced by w + 16n, the context
    kept for the final state `s'` and every allocated chunk of `s` kept with its data; or the run
    reaches a failed allocator call (`Exhausts`). The globals below the allocator (`Glob`) are kept.

    *Not stated:* the model `alloc` equation (see the module doc). -/
theorem import_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len n pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (htg : μ.read A = UInt8.ofNat 9) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 528 ≤ A ∧ A + 56 ≤ S1) (hA8 : 2147484176 ≤ A ∧ A % 8 = 0)
    (hn : 1024 < n ∧ 16 * n < 1073741760)
    (hlen : (Blob.encodeNat n).length + 16 * n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat n).length + 16 * n ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    (∃ q s' ω' μ',
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (268200 + VecPairs.pairSteps 1024 (n - 1024)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775816 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (16 * n) = μ.readN (ptr + (Blob.encodeNat n).length) (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat n).length + 16 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat n).length - 16 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x (268200 + VecPairs.pairSteps 1024 (n - 1024)) := by
  have hA2 := F.hA
  have hS1 := H.hS1
  have hst := H.st
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen hpay henc hw1 ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hs : Shape 21028 956 1106 1108 3100 := by unfold Shape; simp
  obtain ⟨bs1, bs2, bs3⟩ := shape_bs (p := p) (P := P) hs
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A 9
    (by decide) (by omega) F.h1 h7 htg tab (F.hr A (by omega) (by omega)) hrt
  rw [show handler 9 = 21028 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    e1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ 21028 956 1106 1108 3100 A O rd hs ⟨by omega, by omega⟩
      (e1'.trans F.h1) (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
  have hra : ∀ a, ptr ≤ a → a < ptr + w + 16 * n → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω3, μ3, run3, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1106 _ (A - 48) rd ptr len b0 b1 b7
      (by decide) rfl bs2 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [brd]; exact hra a h1 (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := e2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    21028 956 1106 1108 3100 (A - 48) n hs (by omega) (by omega) (by rw [d1, b1]) d7 d8
  have b3 : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [dwr, bwr]
  have H3 : HeapCtx env pb S0 S1 μ3 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr3
  have run04 := run1.trans (run2.trans (run3.trans run4))
  rcases VecPairs.vec_pairs_heap_big (p := p) (P := P) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48) rd
      (ptr + w) (len - w) n 1108 _ O rd pb S0 S1 H3 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) (by rw [c6, d6, b6]) c7
      (by rw [c8, d6, b6]) c9 (by decide) rfl bs3 hO64 (by omega) hn (by omega) (by omega) ⟨by omega, by omega⟩
      ⟨Nat.le_refl _, by omega⟩ (by omega) dR0 dR8 with
    ⟨q, s', ω5, μ5, run5, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H5, keep, cm5, hfresh, kd5, pg5, vfr, -, vgl, -⟩ |
    ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run04 ex).mono (by omega))
  have hqT : q + 16 * n < 2147483648 := by
    have hc5 := chunk_in H5.wf cm5 rfl
    have := H5.hbT
    simp only at hc5
    omega
  have hfrH : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))).trans
      (dfr a (by omega) (by omega) (Or.inl (by omega)))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fO, fO8, fO16, fO24, ffr, frd, fwr⟩ :=
    e3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 21028 956 1106 1108 3100 9223372036854775816
      (A - 48) O n q n O rd hs (by simp) ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega)
      (by omega) (by omega) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
      μ6.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (ffr a h0 h3).trans ((vfr a h0 (by omega) h2 (Or.inr (by omega))).trans (b3 a h0 (Or.inr h1) h2))
  have hlow : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a h => ffr a (by omega) (Or.inl (by omega))
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H5 cm5 (fun a h1 _ => hlow a h1) fwr
  obtain ⟨ω7, run7, g0, g1, g5, g6⟩ := e4 (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    21028 956 1106 1108 3100 A ret t v5 v6 hs ⟨by omega, by omega⟩ (by rw [f1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => Memory.readable_of_writable (H6.st a (by omega) (by omega)))
  have run := run04.trans (run5.trans (run6.trans run7))
  refine Or.inl ⟨q, s', ω7, μ6, run.mono (by omega), g0, g1, g5, g6, fO, fO8, fO16, fO24, ?_, ?_, ?_,
    H6, keep, cm5, hfresh,
    fun c hc hu a hia => by
      have := (chunk_in H.wf hc hu).2.2
      have hia' := hia
      unfold InData at hia'
      rw [hlow a (by omega), kd5 c hc hu a hia]
      exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
    FreeStepsH.pagesOut H.bd run, hfar, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
  · have e : ∀ j, j < 8 → μ6.read (rd + j) = μ5.read (rd + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ6.read (rd + 8 + j) = μ5.read (rd + 8 + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR8]
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

/-- **`DeleteItems` (5), `Export` (10) or `Imported` (19) with any n ≥ 1 items of any length, the
    payload in the heap** (GP v0.8.0 B.7): from 20626 with the tag read without error (its handler h
    and return addresses r1, r2, r3 and discriminant word W as in `VecVecElem.vecvec_elem`), the
    reader `{ptr, len}` at rd (ω₆) holding ℰ(n) (w octets) and the items' encodings (each
    ℰ(|e|) ++ e, L octets in all), all inside an allocated chunk of the allocator's state `s` (context
    `HeapCtx`, under `refineContractK cap`), with 24n < 2³⁰ − 64, every item shorter than 2³⁰ − 64
    octets and A at least S0 + 632 (the reader at A − 48 needing S0 + 584,
    `VecVecU8.vec_vec_u8_heap_big`): either `Instruction::decode` returns the variant in O (the
    discriminant word W and the `Vec` `{cap n, ptr q, len n}` at O + 8, item j at q + 24j the
    `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` with qs j holding es[j], in the fresh allocated chunks `cs`),
    the reader advanced by w + L, the context kept for the final state `s'` and every allocated chunk
    of `s` kept with its data; or the run reaches a failed allocator call (`Exhausts`). The globals
    below the allocator (`Glob`) are kept. -/
theorem vecvec_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (A O ret t v5 v6 rd ptr len pb S0 S1 : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (tag h r1 r2 r3 W : Nat)
    (htag : (tag = 5 ∧ h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ W = 9223372036854775812) ∨
      (tag = 10 ∧ h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ W = 9223372036854775826))
    (es : List (List UInt8))
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (htg : μ.read A = UInt8.ofNat tag) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (H : HeapCtx env pb S0 S1 μ s) (hS : S0 + 632 ≤ A ∧ A + 56 ≤ S1) (hA8 : 2147484280 ≤ A ∧ A % 8 = 0)
    (hn : 1 ≤ es.length ∧ 24 * es.length < 1073741760) (hes : ∀ e ∈ es, e.length < 1073741760)
    (hlen : (Blob.encodeNat es.length).length + (VecVecU8.encs es).flatten.length ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat es.length).length + (VecVecU8.encs es).flatten.length ≤ c.addr + 32 * c.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (henc : μ.readN ptr (Blob.encodeNat es.length).length = Blob.encodeNat es.length)
    (hpd : μ.readN (ptr + (Blob.encodeNat es.length).length) (VecVecU8.encs es).flatten.length =
      (VecVecU8.encs es).flatten) :
    (∃ s' ω' μ' q, ∃ cs : List Chunk, ∃ qs : Nat → Nat,
      FreeStepsH p (refineContractK cap env) 20626 ω μ x t ω' μ' x
        (9 * (VecVecU8.encs es).flatten.length + 70300 * es.length + 41200) ∧ q < 2147483648 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 W ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8
        (ptr + (Blob.encodeNat es.length).length + (VecVecU8.encs es).flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8
        (len - (Blob.encodeNat es.length).length - (VecVecU8.encs es).flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
        ∀ j (hj : j < es.length),
          μ''.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
          μ''.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (qs j) es[j].length = es[j]) ∧
      (∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x
      (9 * (VecVecU8.encs es).flatten.length + 70300 * es.length + 41200) := by
  have hA2 := F.hA
  have hS1 := H.hS1
  have hst := H.st
  have hO64 : O < 18446744073709551616 := by omega
  have hs : Shape h r1 r2 r3 8 := by
    unfold Shape
    rcases htag with ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, rfl, -⟩ <;> simp
  have hh : handler tag = h := by
    rcases htag with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  have ht25 : tag < 25 := by omega
  have hr3 : 0 < r3 ∧ r3 ≤ 2806 ∧ r3 % 2 = 0 := by omega
  have hr2 : 0 < r2 ∧ r2 ≤ 2806 ∧ r2 % 2 = 0 := by omega
  obtain ⟨bs1, bs2, bs3⟩ := shape_bs (p := p) (P := P) hs
  have hw1 : 1 ≤ (Blob.encodeNat es.length).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat es.length).length = w := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, (VecVecU8.encs es).flatten.length = L := ⟨_, rfl⟩
  simp only [hW, hLd] at hlen hpay henc hw1 hpd ⊢
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  -- the dispatch, the helper's frame and the length
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ A tag
    ht25 (by omega) F.h1 h7 htg tab (F.hr A (by omega) (by omega)) hrt
  rw [hh] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    e1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ h r1 r2 r3 8 A O rd hs ⟨by omega, by omega⟩
      (e1'.trans F.h1) (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
  have hra : ∀ a, ptr ≤ a → a < ptr + w + L → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  obtain ⟨ω3, μ3, run3, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 r2 _ (A - 48) rd ptr len b0 b1 b7
      hr2 rfl bs2 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hst a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) es.length (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [brd]; exact hra a h1 (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := e2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    h r1 r2 r3 8 (A - 48) es.length hs (by omega) (by omega) (by rw [d1, b1]) d7 d8
  have b3 : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [dwr, bwr]
  have H3 : HeapCtx env pb S0 S1 μ3 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr3
  have run04 := run1.trans (run2.trans (run3.trans run4))
  -- the items
  rcases VecVecU8.vec_vec_u8_heap_big (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48)
      rd (ptr + w) (len - w) r3 _ O rd pb S0 S1 es H3 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) (by rw [c6, d6, b6]) c7
      (by rw [c8, d6, b6]) c9 hr3 rfl bs3 hO64 (by omega) hn hes
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩ (Or.inl (by omega)) dR0 dR8
      (by rw [hLd, Memory.readN_congr (fun j hj => b3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]; exact hpd) with
    ⟨s', ω5, μ5, q, cs, qs, run5, hq, v0, v1, v5', v6', vc, vp, vl, vR0, vR8, H5, keep, kd5, hcs, hrep, vfr, vlo, vgl, vwr⟩ |
    ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run04 ex).mono (by omega))
  simp only [hLd] at vR0 vR8 run5
  -- the copy into the slot and the return
  have hfrH : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))).trans
      (dfr a (by omega) (by omega) (Or.inl (by omega)))
  have hW' : (h = 21522 ∧ W = 9223372036854775812) ∨ (h = 21871 ∧ W = 9223372036854775817) ∨
      (h = 22072 ∧ W = 9223372036854775826) ∨ (h = 21028 ∧ W = 9223372036854775816) := by
    rcases htag with ⟨-, a, -, -, -, b⟩ | ⟨-, a, -, -, -, b⟩ | ⟨-, a, -, -, -, b⟩ <;> simp [a, b]
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fO, fO8, fO16, fO24, ffr, frd, fwr⟩ :=
    e3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 h r1 r2 r3 8 W (A - 48) O es.length q es.length O rd
      hs hW' ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) hO64
      (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
      μ6.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (ffr a h0 h3).trans ((vfr a h0 (by omega) h2 (Or.inr (by omega))).trans (b3 a h0 (Or.inr h1) h2))
  have hlow : ∀ a, a < 2147483648 → μ6.read a = μ5.read a := fun a h => ffr a (by omega) (Or.inl (by omega))
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H5 (keep cp hcpm hcpu) (fun a h1 _ => hlow a h1) fwr
  obtain ⟨ω7, run7, g0, g1, g5, g6⟩ := e4 (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6
    h r1 r2 r3 8 A ret t v5 v6 hs ⟨by omega, by omega⟩ (by rw [f1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => Memory.readable_of_writable (H6.st a (by omega) (by omega)))
  have run := run04.trans (run5.trans (run6.trans run7))
  refine Or.inl ⟨s', ω7, μ6, q, cs, qs, run.mono (by omega), hq, g0, g1, g5, g6, fO, fO8, fO16, fO24, ?_, ?_,
    H6, keep, ?_, hcs, fun μ'' hag => ?_, hfar, ?_, ?_, ?_⟩
  · have e : ∀ j, j < 8 → μ6.read (rd + j) = μ5.read (rd + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR0, Nat.add_assoc]
  · have e : ∀ j, j < 8 → μ6.read (rd + 8 + j) = μ5.read (rd + 8 + j) := fun j hj => ffr _ (by omega) (by omega)
    rw [Memory.readN_congr e, vR8, Nat.sub_sub]
  · intro c hc hu a hia
    have := (chunk_in H.wf hc hu).2.2
    have hia' := hia
    unfold InData at hia'
    rw [hlow a (by omega), kd5 c hc hu a hia]
    exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · have hag' : ∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ5.read a := fun c hc a hia => by
      obtain ⟨hcm, hcu, -⟩ := hcs c hc
      have := (chunk_in H5.wf hcm hcu).2.2
      have hb5 := H5.hbT
      have hia' := hia
      unfold InData at hia'
      rw [hag c hc a hia, hlow a (by omega)]
    exact hrep μ'' hag'
  · intro a ha
    refine ⟨?_, ?_⟩
    · rw [hlow a (by omega), (vlo a ha).1]
      exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · rw [frd, (vlo a ha).2, drd, brd]
  · intro a ha
    have hg := ha
    unfold Glob at hg
    rw [hlow a (by omega), vgl a ha]
    exact b3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro a ha
    rw [fwr, vwr a ha, dwr, bwr]

end Services.Bootstrap.Decode.VariantsBig
