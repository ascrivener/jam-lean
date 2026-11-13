import Services.Bootstrap.Decode.VecVecU8
import Services.Bootstrap.Decode.VecPairsBig

/-!
# `Vec<Vec<u8>>` without the limits, the payload in the heap

`vec_vec_u8_heap_big` is `VecVecU8.vec_vec_u8_heap` (the element reader at 8: the items of
`DeleteItems`, `Export` and `Imported`) without its two limits: any number n ≥ 1 of elements (with
24n < 2³⁰ − 64), each of any length below 2³⁰ − 64.

* Items: each element's octets are read by `read_vec` (3473) into a fresh block, by
  `VecU8.vec_u8_heap` for at most 16384 octets and by `VecU8.vec_u8_heap_big` (its chunk loop growing
  the block with `realloc`) for more (`elemB`).
* Elements: the reader's outer loop reserves c = min(left, B) elements per batch, `left` the elements
  still to read and B a bound that is 682 for the first batch and the length read so far for every
  later one (86: ω₁₀ ← ω₇, the length), so the buffer doubles: L ↦ L + min(left, L). Each reservation
  calls `finish_grow` (32989, alignment 8, element size 24) for the capacity L + c: for the first
  batch with no old buffer (`alloc`), for every later one with the old buffer q of L elements
  (`realloc`, `ReallocCall.realloc_call`). Then the inner loop (197) reads the batch's c elements.

The outer loop's invariant (`bloopB`), at the batch end 77: L elements read, their 24-octet `Vec<u8>`
headers in the buffer q, the data of an allocated chunk of ⌈24L/32⌉ + 1 units; the items' blocks, a
list `cs` of allocated chunks, none q's nor protected; a set `K` of protected chunks (allocated, not
q's, one of them holding the payload); `HeapCtx`. `realloc` of the buffer moves only the headers: it
keeps every other allocated chunk with its data (`OthersData`: the protected chunks and the items'
blocks), and its new block is never one of them (`VecU8.realloc_fresh`); its copy clause keeps the L
headers. The items' reads keep every allocated chunk's data off the header being pushed.

Either the reader returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

The globals below the allocator (`Glob`) are kept, as in `vec_vec_u8_heap`: `alloc_call`,
`realloc_call` and `vec_u8_heap_big` all keep them.

GP v0.8.0: the octets are read from the service's memory by the PVM (Appendix A); the
`Vec<Vec<u8>>` is the bootstrap service's own decoding of an argument blob.
-/

namespace Services.Bootstrap.Decode.VecVecU8

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **One element read, any length** (197 … 229): as `elem`, for an element e of any length below
    2³⁰ − 64 (`vec_u8_heap` up to 16384 octets, `vec_u8_heap_big` above), with the deeper stack
    `vec_u8_heap_big` needs. -/
theorem elemB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (S r rd ptr len pb S0 S1 : Nat) (e : List UInt8)
    (H : HeapCtx env pb S0 S1 μ s)
    (hS : S0 + 456 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147484104 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : r < 18446744073709551616)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hm : e.length < 1073741760)
    (hlen : (Blob.encodeNat e.length).length + e.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ cp ∈ chunks s, cp.used = true ∧ cp.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat e.length).length + e.length ≤ cp.addr + 32 * cp.size)
    (henc : μ.readN ptr ((Blob.encodeNat e.length).length + e.length) = Blob.encodeNat e.length ++ e) :
    (∃ s' ω' μ' qe, ∃ cs : List Chunk, FreeStepsH p (refineContractK cap env) 197 ω μ x 229 ω' μ' x (9 * e.length + 70000) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat r ∧ qe < 4294967296 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (S + 64) 8 = Num.encodeLE 8 qe ∧
      μ'.readN (S + 72) 8 = Num.encodeLE 8 e.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat e.length).length + e.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat e.length).length - e.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) → μ''.readN qe e.length = e) ∧
      (∀ a, a < 4294967296 → S ≤ a → (a < S + 56 ∨ S + 80 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 197 ω μ x (9 * e.length + 70000) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨m, hM⟩ : ∃ m, e.length = m := ⟨_, rfl⟩
  simp only [hM] at hlen hcp2 henc hm ⊢
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat m).length = w := ⟨_, rfl⟩
  simp only [hW] at hlen hcp2 henc ⊢
  have hw1 : 1 ≤ w := by
    rw [← hW]; unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  have hencw : μ.readN ptr w = Blob.encodeNat m := by
    have := readN_sub μ ptr (w + m) 0 w _ henc (by omega)
    simp only [Nat.add_zero] at this
    rw [this, List.drop_zero, List.take_left' hW]
  have hdat : μ.readN (ptr + w) m = e := by
    rw [readN_sub μ ptr (w + m) w m _ henc (by omega), List.drop_left' hW]
    exact List.take_of_length_le (by omega)
  have hra : ∀ a, ptr ≤ a → a < ptr + w + m → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable H hcpm hcpu ⟨by omega, by omega⟩)
  -- the length
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := r1 (p := p) (P := P) (R := refineContractK cap env) x ω μ S rd
    ⟨by omega, by omega⟩ h1 (by omega) s24 (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
  obtain ⟨ω2, μ2, run2, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ 4 207 S rd ptr len a0 a1 a7
      (by decide) jte_1 bs_207 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega)) hR0 hR8 m
      (by omega) (by rw [hW]; omega) (fun a h1 h2 => by rw [hW] at h2; exact hra a h1 (by omega))
      (by rw [hW]; exact hencw)
  rw [hW] at dR0 dR8
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8, c9⟩ := r2 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2
    S rd m ⟨by omega, by omega⟩ (by rw [d1, a1]) (by rw [d5, a5]) d7 d8 (by omega) (by omega)
  have b2 : ∀ a, a < 4294967296 → (a < S - 128 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => dfr a h0 h1 h2
  have wr2 : ∀ a, μ2.writable a = μ.writable a := dwr
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) wr2
  have run03 := run1.trans (run2.trans run3)
  have hc6 : ω3[6] = UInt64.ofNat r := by rw [c6, d6, a6, h6]
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · -- an empty element: no allocation
    subst hm0
    have he : e = [] := List.eq_nil_of_length_eq_zero hM
    obtain ⟨ω4, μ4, run4, f0, f1, f5, f6, fO, fO8, fO16, ffr, frd, fwr⟩ :=
      vec_u8_empty (p := p) (P := P) (R := refineContractK cap env) x ω3 μ2 S (S + 56) rd (len - w) 6 229 rd r
        ⟨by omega, by omega⟩ c0 c1 c5 hc6 c7 c8 c9 (by omega) hr (by decide) jte_2 bs_229 (by omega)
        (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (rd8'' (by omega) dR8)
        (fun a h1 h2 => by rw [drd]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => by rw [dwr]; exact hst a (by omega) (by omega))
        (fun a h1 h2 => by rw [dwr]; exact hst a (by omega) (by omega))
    have b4 : ∀ a, a < 4294967296 → (a < S - 128 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < S + 56 ∨ S + 80 ≤ a) →
        μ4.read a = μ.read a := fun a h0 h1 h2 h3 => (ffr a h0 (by omega) h3).trans (b2 a h0 h1 h2)
    have H4 : HeapCtx env pb S0 S1 μ4 s :=
      ctx_congr_data H hcpm (fun a h1 _ => b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))
        (fun a => by rw [fwr, dwr])
    refine Or.inl ⟨s, ω4, μ4, 1, [], (run03.trans run4).mono (by omega), f1, f6, by decide, fO, fO8, fO16,
      ?_, ?_, H4, fun c hc _ => hc, ?_, fun c hc => by simp at hc, fun μ'' _ => by rw [he]; rfl, ?_,
      fun a ha => by
        unfold Glob at ha
        exact b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))⟩
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega) (Or.inr (by omega))), dR0, Nat.add_zero]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega) (Or.inr (by omega))), dR8, Nat.sub_zero]
    · intro c hc hu a ha
      have := (chunk_in H.wf hc hu).2.2
      unfold InData at ha
      exact b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    · intro a h0 h1 h2 h3
      exact b4 a h0 (Or.inr h1) h3 h2
  rcases Nat.lt_or_ge 16384 m with hbig | hsmall
  · -- a long element: `read_vec`'s chunk loop
    rcases vec_u8_heap_big (p := p) (P := P) env cap hcap1 hcap x ω3 μ2 s S (S + 56) rd (ptr + w) (len - w)
        m 6 229 rd r pb S0 S1 H2 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        c0 c1 c5 hc6 c7 c8 c9 (by decide) jte_2 bs_229 (by omega) hr ⟨hbig, hm⟩ (by omega) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
      ⟨qe, s', ω4, μ4, run4, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H4, keep, cm, hfresh, kd, -, vfr,
        -, vgl, -⟩ | ex
    · have hqm := chunk_in H4.wf cm rfl
      simp only at hqm
      have hb4 := H4.hbT
      have hb4' := H4.hb0
      refine Or.inl ⟨s', ω4, μ4, qe, [⟨qe - 32, (m + 31) / 32 + 1, true⟩], (run03.trans run4).mono (by
          unfold loopSteps; omega),
        v1, v6', by omega, vc, vp, vl, ?_, ?_, H4, keep, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vR0]
      · rw [vR8]
      · intro c hc hu a hia
        have := (chunk_in H.wf hc hu).2.2
        have hia' := hia
        unfold InData at hia'
        rw [kd c hc hu a hia]
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨cm, rfl, hfresh⟩
      · intro μ'' hag
        rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), vdata]
        exact Memory.readN_congr (fun j hj => b2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))) |>.trans hdat
      · intro a h0 h1 h2 h3
        rw [vfr a h0 h1 h3 h2]
        exact b2 a h0 (Or.inr h1) h3
      · intro a ha
        have hg := ha
        unfold Glob at hg
        rw [vgl a ha]
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · exact Or.inr ((Exhausts.pre run03 ex).mono (by unfold loopSteps; omega))
  · -- a short element: one block
    rcases vec_u8_heap (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω3 μ2 s S (S + 56) rd (ptr + w) (len - w)
        m 6 229 rd r pb S0 S1 H2 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        c0 c1 c5 hc6 c7 c8 c9 (by decide) jte_2 bs_229 (by omega) hr ⟨hm0, hsmall⟩ (by omega) (by omega)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) dR0 dR8 with
      ⟨qe, s', ω4, μ4, ha, run4, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, H4, keep, cm, hfresh, kd, -, vfr,
        -, vgl, -⟩ | ⟨hna, ω4, μ4, run4, f7⟩
    · have hqm := chunk_in H4.wf cm rfl
      simp only at hqm
      have hb4 := H4.hbT
      have hb4' := H4.hb0
      refine Or.inl ⟨s', ω4, μ4, qe, [⟨qe - 32, (m + 31) / 32 + 1, true⟩], (run03.trans run4).mono (by omega),
        v1, v6', by omega, vc, vp, vl, ?_, ?_, H4, keep, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vR0]
      · rw [vR8]
      · intro c hc hu a hia
        have := (chunk_in H.wf hc hu).2.2
        have hia' := hia
        unfold InData at hia'
        rw [kd c hc hu a hia]
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      · intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨cm, rfl, hfresh⟩
      · intro μ'' hag
        rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), vdata]
        exact Memory.readN_congr (fun j hj => b2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))) |>.trans hdat
      · intro a h0 h1 h2 h3
        rw [vfr a h0 h1 h3 h2]
        exact b2 a h0 (Or.inr h1) h3
      · intro a ha
        have hg := ha
        unfold Glob at hg
        rw [vgl a ha]
        exact b2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · exact Or.inr ((Exhausts.pre run03 (Exhausts.of_alloc run4 f7 hna)).mono (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA in
/-- **One pass of the read loop, any element length** (197 … 197, or 77): as `pass`, with `elemB` for
    the element, any capacity c with 24c < 2³⁰ − 64. -/
theorem passB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (S q c k r rd ptr len pb S0 S1 : Nat) (cb : Chunk) (e : List UInt8)
    (H : HeapCtx env pb S0 S1 μ s)
    (hS : S0 + 456 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147484104 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 1 ≤ r ∧ r < 4294967296)
    (hk : k < c ∧ 24 * c < 1073741760)
    (hcb : cb ∈ chunks s) (hcbu : cb.used = true) (hq1 : cb.addr + 32 ≤ q)
    (hq2 : q + 24 * c ≤ cb.addr + 32 * cb.size)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 c) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 k)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hm : e.length < 1073741760)
    (hlen : (Blob.encodeNat e.length).length + e.length ≤ len ∧ len < 4294967296)
    (hpay : ∃ cp ∈ chunks s, cp.used = true ∧ cp.addr + 32 ≤ ptr ∧
      ptr + (Blob.encodeNat e.length).length + e.length ≤ cp.addr + 32 * cp.size)
    (henc : μ.readN ptr ((Blob.encodeNat e.length).length + e.length) = Blob.encodeNat e.length ++ e) :
    (∃ s' ω' μ' j qe, ∃ cs : List Chunk,
      FreeStepsH p (refineContractK cap env) 197 ω μ x j ω' μ' x (9 * e.length + 70100) ∧
      (2 ≤ r → j = 197) ∧ (r = 1 → j = 77 ∧ ω'[7] = UInt64.ofNat (k + 1)) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧
      μ'.readN (q + 24 * k) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (q + 24 * k + 8) 8 = Num.encodeLE 8 qe ∧
      μ'.readN (q + 24 * k + 16) 8 = Num.encodeLE 8 e.length ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (k + 1) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (Blob.encodeNat e.length).length + e.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (Blob.encodeNat e.length).length - e.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) → μ''.readN qe e.length = e) ∧
      (∀ a, a < 4294967296 → S ≤ a → (a < S + 48 ∨ S + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 197 ω μ x (9 * e.length + 70100) := by
  have hS1 := H.hS1
  obtain ⟨hcbb, hcbT, hcbT'⟩ := chunk_in H.wf hcb hcbu
  have hbT := H.hbT
  rcases elemB (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S r rd ptr len pb S0 S1 e H hS hSa h1 h6
      (by omega) s24 hrd hR0 hR8 hm hlen hpay henc with
    ⟨s', ω4, μ4, qe, cs, run4, e1, e6, hqe, s56, s64, s72, R0, R8, H4, keep, kd, hcs, hrep, fr4, gl4⟩ | ex
  · have hcb' := keep cb hcb hcbu
    have hst4 := H4.st
    have u32 : μ4.readN (S + 32) 8 = Num.encodeLE 8 c := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s32
    have u40 : μ4.readN (S + 40) 8 = Num.encodeLE 8 q := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s40
    have u48 : μ4.readN (S + 48) 8 = Num.encodeLE 8 k := by
      rw [Memory.readN_congr (fun j hj => fr4 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s48
    obtain ⟨j, ω5, μ5, run5, hj1, hj2, f1, f6, fe0, fe1, fe2, f48, ffr, frd, fwr⟩ :=
      r3 (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 S q c k r e.length qe e.length
        ⟨by omega, by omega⟩ e1 e6 hr ⟨hk.1, by omega⟩ (by omega) (by omega) hqe (by omega) u32 u48 u40 s56 s64 s72
        (by omega) (fun a h1 h2 => hst4 a (by omega) (by omega))
        (fun a h1 h2 => heap_writable H4 hcb' hcbu ⟨by omega, by omega⟩)
    have low5 : ∀ a, a < 2147483648 → (a < q + 24 * k ∨ q + 24 * k + 24 ≤ a) → μ5.read a = μ4.read a :=
      fun a h0 h1 => ffr a (by omega) h1 (Or.inl (by omega)) (Or.inl (by omega))
    refine Or.inl ⟨s', ω5, μ5, j, qe, cs, (run4.trans run5).mono (by omega), hj1, hj2, f1, f6, fe0, fe1, fe2, f48,
      ?_, ?_, ctx_congr_data H4 hcb' (fun a h1 h2 => low5 a h1 (by omega)) fwr, keep, ?_, hcs, ?_, ?_,
      fun a ha => by
        have := H.hb0
        unfold Glob at ha
        exact (low5 a (by omega) (Or.inl (by omega))).trans (gl4 a (by unfold Glob; omega))⟩
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)))]
      exact R0
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)))]
      exact R8
    · intro d hd hu a hia hout
      have := (chunk_in H.wf hd hu).2.2
      have hia' := hia
      unfold InData at hia'
      rw [low5 a (by omega) hout]
      exact kd d hd hu a hia
    · intro μ'' hag
      apply hrep
      intro d hdc a hia
      obtain ⟨hdm, hdu, hdf⟩ := hcs d hdc
      have hdis := data_disj H4.wf hdm hcb' (fun e' => hdf cb hcb hcbu e'.symm) hia
      have := (chunk_in H4.wf hdm hdu).2.2
      have hbase := H4.hbT
      have hia' := hia
      unfold InData at hia'
      rw [hag d hdc a hia, low5 a (by omega) (by omega)]
    · intro a h0 h1 h2 h3
      rw [ffr a h0 (Or.inr (by omega)) (by omega) (by omega)]
      exact fr4 a h0 h1 (by omega) h3
  · exact Or.inr (ex.mono (by omega))

open Services.Bootstrap.Decode.Loop in
/-- The offsets grow with the index. -/
theorem off_mono (es : List (List UInt8)) {k k' : Nat} (h : k ≤ k') : off es k ≤ off es k' := by
  unfold off
  have e : (es.take k').take k = es.take k := by rw [List.take_take, Nat.min_eq_left h]
  conv => rhs; rw [← List.take_append_drop k (es.take k')]
  rw [e, List.flatten_append, List.length_append]
  omega

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **The read loop, any element length, any capacity** (197 … 77): as `loop`, for the elements
    k … N − 1 of `es` (N ≤ |es|, 24N < 2³⁰ − 64, the capacity N at S + 32), each of any length below
    2³⁰ − 64 (`passB`). -/
theorem loopB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) {hb : Nat}
    (S q rd ptr0 len0 pb S0 S1 N : Nat) (cb cp : Chunk) (es : List (List UInt8))
    (hS : S0 + 456 ≤ S ∧ S + 128 ≤ S1) (hSa : 2147484104 ≤ S ∧ S % 8 = 0)
    (hN : N ≤ es.length ∧ 24 * N < 1073741760) (hes : ∀ e ∈ es, e.length < 1073741760)
    (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1) (hcbcp : cb ≠ cp)
    (hq1 : cb.addr + 32 ≤ q) (hq2 : q + 24 * N ≤ cb.addr + 32 * cb.size)
    (hp1 : cp.addr + 32 ≤ ptr0) (hp2 : ptr0 + (encs es).flatten.length ≤ cp.addr + 32 * cp.size)
    (hlen : (encs es).flatten.length ≤ len0 ∧ len0 < 4294967296) :
    ∀ i k (s : State) (ω : Regs) (μ : Memory), k + i = N → 1 ≤ i →
      HeapCtx env pb S0 S1 μ s → cb ∈ chunks s → cb.used = true → cp ∈ chunks s → cp.used = true →
      ω[1] = UInt64.ofNat S → ω[6] = UInt64.ofNat i →
      μ.readN (S + 32) 8 = Num.encodeLE 8 N → μ.readN (S + 40) 8 = Num.encodeLE 8 q →
      μ.readN (S + 48) 8 = Num.encodeLE 8 k → μ.readN (S + 24) 8 = Num.encodeLE 8 rd →
      μ.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) k) →
      μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) k) →
      μ.readN ptr0 (encs es).flatten.length = (encs es).flatten →
      (∃ s' ω' μ', ∃ cs : List Chunk, ∃ qs : Nat → Nat,
        FreeStepsH p (refineContractK cap env) 197 ω μ x 77 ω' μ' x
          (9 * (off (encs es) N - off (encs es) k) + 70100 * i) ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat N ∧
        (∀ j (hj : j < N), k ≤ j →
          μ'.readN (q + 24 * j) 8 = Num.encodeLE 8 (es[j]'(Nat.lt_of_lt_of_le hj hN.1)).length ∧
          μ'.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
          μ'.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 (es[j]'(Nat.lt_of_lt_of_le hj hN.1)).length) ∧
        μ'.readN (S + 48) 8 = Num.encodeLE 8 N ∧
        μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) N) ∧
        μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) N) ∧
        HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
        (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < q + 24 * k ∨ q + 24 * N ≤ a) →
          μ'.read a = μ.read a) ∧
        (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          ∀ j (hj : j < N), k ≤ j →
            μ''.readN (qs j) (es[j]'(Nat.lt_of_lt_of_le hj hN.1)).length = es[j]'(Nat.lt_of_lt_of_le hj hN.1)) ∧
        (∀ a, a < 4294967296 → S ≤ a → (a < S + 48 ∨ S + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
          μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a)) ∨
      Exhausts env cap pb p P 197 ω μ x (9 * (off (encs es) N - off (encs es) k) + 70100 * i) := by
  intro i
  induction i with
  | zero => intro k s ω μ _ h; exact absurd h (by decide)
  | succ i ih =>
  intro k s ω μ hki _ H hcb hcbu hcp hcpu h1 h6 s32 s40 s48 s24 R0 R8 pay
  have hk : k < es.length := by omega
  have hkE : k < (encs es).length := by rw [encs_length]; exact hk
  have hEk := encs_get es k hkE
  have hoff := off_lt (encs es) k hkE
  rw [hEk] at hoff
  simp only [List.length_append] at hoff
  have hm := hes es[k] (List.getElem_mem hk)
  have henc : μ.readN (ptr0 + off (encs es) k)
      ((Blob.encodeNat es[k].length).length + es[k].length) = Blob.encodeNat es[k].length ++ es[k] := by
    rw [readN_sub μ ptr0 _ _ _ _ pay (by omega)]
    have := flatten_at (encs es) k hkE
    rw [hEk] at this
    simpa using this
  have hS1 := H.hS1
  have hoff1 : off (encs es) (k + 1) = off (encs es) k + ((Blob.encodeNat es[k].length).length + es[k].length) := by
    rw [off_succ (encs es) k hkE, hEk, List.length_append]
  have hmoN := off_mono (encs es) (show k + 1 ≤ N by omega)
  rcases passB (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S q N k (i + 1) rd
      (ptr0 + off (encs es) k) (len0 - off (encs es) k) pb S0 S1 cb es[k] H hS hSa h1 h6 ⟨by omega, by omega⟩
      ⟨by omega, hN.2⟩ hcb hcbu hq1 hq2 s32 s40 s48 s24 hrd R0 R8 hm ⟨by omega, by omega⟩
      ⟨cp, hcp, hcpu, by omega, by omega⟩ henc with
    ⟨s1, ω1, μ1, j, qe, cs1, run1, hj1, hj2, f1, f6, fe0, fe1, fe2, f48, fR0, fR8, H1, keep1, kd1, hcs1, hrep1,
      ffr1, gl1⟩ | ex
  rotate_left
  · exact Or.inr (ex.mono (by omega))
  have hcb1 := keep1 cb hcb hcbu
  have hcp1 := keep1 cp hcp hcpu
  obtain ⟨hcbb, hcbT, -⟩ := chunk_in H.wf hcb hcbu
  have hb0 := H.hb0
  -- the payload is kept: it lies in cp, the push in cb
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + (encs es).flatten.length → μ1.read a = μ.read a := fun a h1 h2 =>
    kd1 cp hcp hcpu a ⟨by omega, by omega⟩ (by
      have := data_disj H.wf hcp hcb (Ne.symm hcbcp) (a := a) ⟨by omega, by omega⟩
      omega)
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · -- the last element: on to 77
    subst hi0
    obtain ⟨rfl, f7⟩ := hj2 rfl
    have hkn : k + 1 = N := by omega
    have hoffN : off (encs es) N = off (encs es) k + ((Blob.encodeNat es[k].length).length + es[k].length) := by
      rw [← hkn, hoff1]
    refine Or.inl ⟨s1, ω1, μ1, cs1, fun _ => qe, run1.mono (by omega), f1, by rw [f7, hkn], ?_, by rw [f48, hkn],
      ?_, ?_, H1, keep1, ?_, hcs1, ?_, ffr1, gl1⟩
    · intro j' hj' hkj
      obtain rfl : j' = k := by omega
      exact ⟨fe0, fe1, fe2⟩
    · rw [fR0, hoffN]; congr 1; omega
    · rw [fR8, hoffN]; congr 1; omega
    · intro c hc hu a hia hout
      exact kd1 c hc hu a hia (by omega)
    · intro μ'' hag j' hj' hkj
      obtain rfl : j' = k := by omega
      exact hrep1 μ'' hag
  · -- more to read: the next pass
    have hj197 := hj1 (by omega)
    subst hj197
    have u32 : μ1.readN (S + 32) 8 = Num.encodeLE 8 N := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s32
    have u40 : μ1.readN (S + 40) 8 = Num.encodeLE 8 q := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s40
    have u24 : μ1.readN (S + 24) 8 = Num.encodeLE 8 rd := by
      rw [Memory.readN_congr (fun j hj => ffr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]
      exact s24
    rcases ih (k + 1) s1 ω1 μ1 (by omega) hi0 H1 hcb1 hcbu hcp1 hcpu f1 (by rw [f6]; congr 1) u32 u40 f48 u24
        (by rw [fR0, hoff1]; congr 1; omega) (by rw [fR8, hoff1]; congr 1; omega)
        (by rw [Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))]; exact pay) with
      ⟨s2, ω2, μ2, cs2, qs2, run2, g1, g7, gel, g48, gR0, gR8, H2, keep2, kd2, hcs2, hrep2, gfr, ggl⟩ | ex
    · have hcb2 := keep2 cb hcb1 hcbu
      refine Or.inl ⟨s2, ω2, μ2, cs1 ++ cs2, fun j' => if j' = k then qe else qs2 j',
        (run1.trans run2).mono (by omega), g1, g7, ?_, g48, gR0, gR8, H2,
        fun c hc hu => keep2 c (keep1 c hc hu) hu, ?_, ?_, ?_, ?_, fun a ha => (ggl a ha).trans (gl1 a ha)⟩
      · intro j' hj' hkj
        by_cases hjk : j' = k
        · subst hjk
          simp only [ite_true]
          have kk : ∀ t, t < 24 → μ2.read (q + 24 * j' + t) = μ1.read (q + 24 * j' + t) := fun t ht =>
            kd2 cb hcb1 hcbu _ ⟨by omega, by omega⟩ (Or.inl (by omega))
          have k8 : μ2.readN (q + 24 * j' + 8) 8 = μ1.readN (q + 24 * j' + 8) 8 :=
            Memory.readN_congr (fun t ht => by
              have := kk (8 + t) (by omega); rwa [show q + 24 * j' + (8 + t) = q + 24 * j' + 8 + t by omega] at this)
          have k16 : μ2.readN (q + 24 * j' + 16) 8 = μ1.readN (q + 24 * j' + 16) 8 :=
            Memory.readN_congr (fun t ht => by
              have := kk (16 + t) (by omega); rwa [show q + 24 * j' + (16 + t) = q + 24 * j' + 16 + t by omega] at this)
          refine ⟨?_, ?_, ?_⟩
          · rw [Memory.readN_congr (fun t ht => kk t (by omega))]; exact fe0
          · rw [k8]; exact fe1
          · rw [k16]; exact fe2
        · simp only [hjk, ite_false]
          exact gel j' hj' (by omega)
      · intro c hc hu a hia hout
        have hc1 := keep1 c hc hu
        by_cases hin : q + 24 * k ≤ a ∧ a < q + 24 * k + 24
        · rcases Classical.em (c = cb) with hcbc | hne
          · subst hcbc
            omega
          · have := data_disj H.wf hc hcb hne hia
            omega
        · rw [kd2 c hc1 hu a hia (by omega)]
          exact kd1 c hc hu a hia (by omega)
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨hcm, hcu, hcf⟩ := hcs1 c hc
          exact ⟨keep2 c hcm hcu, hcu, hcf⟩
        · obtain ⟨hcm, hcu, hcf⟩ := hcs2 c hc
          exact ⟨hcm, hcu, fun d hd hu => hcf d (keep1 d hd hu) hu⟩
      · intro μ'' hag j' hj' hkj
        by_cases hjk : j' = k
        · subst hjk
          simp only [ite_true]
          apply hrep1
          intro c hc a hia
          obtain ⟨hcm, hcu, -⟩ := hcs1 c hc
          rw [hag c (List.mem_append_left _ hc) a hia]
          have := (chunk_in H1.wf hcm hcu).2.2
          have hne : c ≠ cb := fun e => by
            obtain ⟨-, -, hf⟩ := hcs1 c hc
            exact hf cb hcb hcbu e.symm
          have hdis := data_disj H1.wf hcm hcb1 hne hia
          have hia' := hia
          unfold InData at hia'
          exact kd2 c hcm hcu a hia (by omega)
        · simp only [hjk, ite_false]
          exact hrep2 μ'' (fun c hc a hia => hag c (List.mem_append_right _ hc) a hia) j' hj' (by omega)
      · intro a h0 h1 h2 h3
        rw [gfr a h0 h1 h2 h3]
        exact ffr1 a h0 h1 h2 h3
    · exact Or.inr ((Exhausts.pre run1 ex).mono (by omega))

/-- 120 … 147, as `q4` for any batch: `finish_grow` returned `Ok` with the buffer q (S + 80 holds 0,
    S + 88 holds q), the capacity N at S and the bound M ≠ 0 at S + 8, left (ω₅) and the batch c
    (ω₆): the reader records the `Vec` `{cap N, ptr q}` at S + 32, left at S + 8 and c at S, and enters
    its read loop (197). -/
theorem q4g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q n c N M : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat c)
    (hq : q < 18446744073709551616) (hc : c < 18446744073709551616) (hn : n < 18446744073709551616)
    (hN : N < 18446744073709551616) (hM : 0 < M ∧ M < 18446744073709551616)
    (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 0) (s88 : μ.readN (S + 88) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 N) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 M)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 120 ω μ x 197 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat c ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 N ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧ μ'.readN S 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 16 ≤ a) → (a < S + 32 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r80 := rd8' (by decide) s80
  have r88 := rd8' hq s88
  have r0 := rd8' hN s0
  have r8 := rd8' hM.2 s8
  have hM0 : ¬ M = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r80, r88, r0, r8, hM0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide
    all_goals assumption

/-- 77 … 114, the batch end with more to read: the batch of c elements is read (ω₇ = L, the length;
    S + 8 holds c + left, S holds c, left ≥ 1), and the buffer is full (S + 32, the capacity, holds L):
    the reader goes back to its reserve loop (52) with the bound L, and calls `finish_grow` for the
    capacity L + c', c' = min(left, L) (ω₆ = c', ω₈ = L the old capacity, ω₉ = q from S + 40, ω₁₀ =
    L + c', alignment 8, element size 24, result slot S + 80, return address 2), L + c' at S and L at
    S + 8. -/
theorem bkv {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q L c left : Nat) (hS : 65536 ≤ S ∧ S + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L) (hL : 1 ≤ L ∧ L < 4294967296)
    (hl : 1 ≤ left ∧ c + left < 4294967296) (hq : q < 18446744073709551616)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s0 : μ.readN S 8 = Num.encodeLE 8 c)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 L) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (hw : ∀ a, S ≤ a → a < S + 128 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 77 ω μ x 32989 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 2 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat left ∧
      ω'[6] = UInt64.ofNat (min left L) ∧ ω'[7] = UInt64.ofNat (S + 80) ∧ ω'[8] = UInt64.ofNat L ∧
      ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + min left L) ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 24 ∧
      μ'.readN S 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r8 := rd8'' (by omega) s8
  have r0 := rd8'' (by omega) s0
  have r32 := rd8'' (by omega) s32
  have r40 := rd8'' hq s40
  have hpos : 0 < (if left ≤ L then left else L) % 18446744073709551616 := by split <;> omega
  have hle : c ≤ c + left := Nat.le_add_right c left
  have hne : ¬ c + left - c = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, hL, hl, r8, r0, r32, r40, hle, hne, Nat.sub_self, hpos, Nat.add_sub_cancel_left,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; split <;> omega)
    all_goals try (congr 1; omega)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll Services.Bootstrap.Decode.Loop in
/-- **One later batch, the payload in the heap** (77 … 77): at the batch end with L ≥ 1 elements read
    (ω₇ = L; the buffer q of capacity L at S + 40, S + 32, S + 48; S + 8, S holding c + left, c) and
    left ≥ 1 to go, q the data of an allocated chunk of ⌈24L/32⌉ + 1 units, the payload (the
    elements' encodings) inside an allocated chunk that is not q's: either the model's `realloc` of q
    to ⌈24(L + c')/32⌉ units (c' = min(left, L)) gives a block r and state `s'`, and the reader reads
    the batch's c' elements (`loopB`) into r, reaching the batch end again with ω₇ = L + c', the `Vec`
    `{cap L + c', ptr r, len L + c'}`, r holding q's first 24L octets (the old headers) and the new
    elements' headers, r the data of an allocated chunk of ⌈24(L + c')/32⌉ + 1 units, the new
    elements' blocks fresh allocated chunks (`cs`), every allocated chunk of `s` other than q's still
    allocated, not r's, with its data; or the run reaches a failed allocator call (`Exhausts`). -/
theorem batchB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (S rd q L c left ptr0 len0 pb S0 S1 : Nat) (es : List (List UInt8))
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (24 * L + 31) / 32 + 1)
    (hpay : ∃ d ∈ chunks s, d.used = true ∧ d.addr + 32 ≠ q ∧ d.addr + 32 ≤ ptr0 ∧
      ptr0 + (encs es).flatten.length ≤ d.addr + 32 * d.size)
    (hS : S0 + 456 ≤ S ∧ S + 128 ≤ S1) (hsp : 2147484104 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hLl : L + left = es.length) (hn : 24 * es.length < 1073741760)
    (hes : ∀ e ∈ es, e.length < 1073741760)
    (hlen : (encs es).flatten.length ≤ len0 ∧ len0 < 4294967296)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s0 : μ.readN S 8 = Num.encodeLE 8 c)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 L)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 L)
    (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) L))
    (hpd : μ.readN ptr0 (encs es).flatten.length = (encs es).flatten) :
    (∃ ω' μ' s' r, ∃ cs : List Chunk, ∃ qs : Nat → Nat,
      FreeStepsH p (refineContractK cap env) 77 ω μ x 77 ω' μ' x
        (64 * ((24 * L + 31) / 32) + 1400 + 9 * (off (encs es) (L + min left L) - off (encs es) L) +
          70100 * min left L) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (L + min left L) ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 left ∧ μ'.readN S 8 = Num.encodeLE 8 (min left L) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 r ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 (L + min left L) ∧
      (∀ a, a < 4294967296 → (S + 16 ≤ a ∧ a < S + 32 ∨ S + 104 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) (L + min left L)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) (L + min left L)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = r ∧ d.used = true ∧ d.size = (24 * (L + min left L) + 31) / 32 + 1) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ q →
        d ∈ chunks s' ∧ d.addr + 32 ≠ r ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ d ∈ cs, d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
        ∀ e ∈ chunks s, e.used = true → e.addr + 32 ≠ q → e ≠ d) ∧
      μ'.readN r (24 * L) = μ.readN q (24 * L) ∧
      (∀ j (hj : j < L + min left L), L ≤ j →
        μ'.readN (r + 24 * j) 8 = Num.encodeLE 8 (es[j]'(by omega)).length ∧
        μ'.readN (r + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
        μ'.readN (r + 24 * j + 16) 8 = Num.encodeLE 8 (es[j]'(by omega)).length) ∧
      (∀ μ'' : Memory, (∀ d ∈ cs, ∀ a, InData d a → μ''.read a = μ'.read a) →
        ∀ j (hj : j < L + min left L), L ≤ j → μ''.readN (qs j) (es[j]'(by omega)).length = es[j]'(by omega)) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 77 ω μ x
      (64 * ((24 * L + 31) / 32) + 1400 + 9 * (off (encs es) (L + min left L) - off (encs es) L) +
        70100 * min left L) := by
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨cp, hcpm, hcpu, hcpq, hcp1, hcp2⟩ := hpay
  have hu : usable s q = (24 * L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨hp0, -, hpT⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  -- the batch end, and finish_grow to realloc
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m0, m8, fr1, rd1, wr1⟩ :=
    bkv (p := p) (P := P) (R := refineContractK cap env) x ω μ S q L c left ⟨by omega, by omega⟩ h1 h7
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ (by omega) s8 s0 s32 s40 (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨c', hcdef⟩ : ∃ c', min left L = c' := ⟨_, rfl⟩
  rw [hcdef] at a6 a10 m0
  have hc1 : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    VecPairs.g3e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (S - 40) (S + 80) L q (L + c') 8 24 2
      left c' ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by decide)
      (by omega) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 16 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcqm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (S - 40) q 8 (24 * (L + c')) pb
      S0 S1 H2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6, gl3, -, -⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr ((Exhausts.of_realloc (run1.trans (run2.trans (run3.trans run4))) e7 hR).mono (by omega))
  have hR1 : realloc (growTo pb) hb s q 1 ((24 * (L + c') + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hcp' := keep3 cp hcpm hcpu hcpq
  have hcpr : cp.addr + 32 ≠ r := hfr cp hcpm hcpu hcpq
  have hcpne : cp ≠ cr := fun e => hcpr (by rw [e]; exact hcra)
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (S - 40) (S + 80) (24 * (L + c')) r 2 120
      left c' ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_0 bs_120
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 80 ∨ S + 104 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω6, μ6, run6, d1, d6, d32, d40, d8, d0, fr6, rd6, wr6⟩ :=
    q4g (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 S r left c' (L + c') L ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      cres (by rw [show S + 88 = S + 80 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m0)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m8)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  -- the frame S in μ6: off the slots written since μ
  have hS60 : ∀ a, S ≤ a → a < 4294967296 →
      (S + 16 ≤ a ∧ a < S + 32 ∨ S + 48 ≤ a ∧ a < S + 80 ∨ S + 104 ≤ a) → μ6.read a = μ.read a :=
    fun a h1 h2 h3 => (fr6 a h2 (by omega) (by omega)).trans ((hS51 a h1 h2 (by omega)).trans
      (fr1 a h2 (by omega)))
  have hhigh : ∀ a, a < 4294967296 → S + 104 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    hS60 a (by omega) h0 (by omega)
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha => by
    have hca := ha
    unfold InData at hca
    rw [h63 a (by omega), kp3 a ⟨cp, hcpm, hcpu, hcpq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H3 hcrm (fun a h1 _ => h63 a h1) wr36
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  -- the batch's reads
  rcases loopB (p := p) (P := P) (hb := hb) env cap hcap1 hcap x S r rd ptr0 len0 pb S0 S1 (L + c') cr cp es
      hS hsp ⟨by omega, by omega⟩ hes hrd (Ne.symm hcpne) (by omega) (by rw [hcrs]; omega) hcp1 hcp2 hlen
      c' L s' ω6 μ6 (by omega) hc1.1 H6 hcrm hcru hcp' hcpu d1 d6 d32 d40
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s48)
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s24)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by rw [Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)]; exact hpd) with
    ⟨s2, ω7, μ7, cs1, qs1, run7, g1, g7, gel, g48, gR0, gR8, H7, keep7, kd7, hcs7, hrep7, gfr, ggl⟩ | ex
  all_goals subst hcdef
  rotate_left
  · exact Or.inr ((Exhausts.pre run16 ex).mono (by omega))
  have h76 : ∀ a, S ≤ a → a < S + 48 → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ6.read a := fun a h1 h2 h3 =>
    gfr a (by omega) h1 (Or.inl h2) h3
  have hcr2 := keep7 cr hcrm hcru
  refine Or.inl ⟨ω7, μ7, s2, r, cs1, qs1, (run16.trans run7).mono (by omega), g1, g7, ?_, ?_, ?_, ?_, g48, ?_,
    gR0, gR8, H7, ⟨cr, hcr2, hcra, hcru, hcrs⟩, ?_, ?_, ?_, fun j hj hLj => gel j hj hLj,
    fun μ'' hag j hj hLj => hrep7 μ'' hag j hj hLj, ?_⟩
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d8
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d0
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d32
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega))]; exact d40
  · intro a h0 h1 h2
    exact (gfr a h0 (by omega) (by omega) h2).trans (hS60 a (by omega) h0 (by omega))
  · intro d hd hu hdq
    have hdm' := keep3 d hd hu hdq
    have hdr : d.addr + 32 ≠ r := hfr d hd hu hdq
    have hdne : d ≠ cr := fun e => hdr (by rw [e]; exact hcra)
    refine ⟨keep7 d hdm' hu, hdr, fun a ha => ?_⟩
    have hdis := data_disj H3.wf hdm' hcrm hdne ha
    rw [hcrs] at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [kd7 d hdm' hu a ha (by omega), h63 a (by omega), kp3 a ⟨d, hd, hu, hdq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro d hd
    obtain ⟨hdm, hdu, hdf⟩ := hcs7 d hd
    refine ⟨hdm, hdu, fun e => ?_, fun e he heu heq => hdf e (keep3 e he heu heq) heu⟩
    have ht := H7.wf.2.2.2.1; unfold TilesOk at ht
    exact hdf cr hcrm hcru (Tiles.addr_inj ht cr hcr2 d hdm (by omega))
  · rw [Memory.readN_congr (fun j hj => (kd7 cr hcrm hcru _ ⟨by omega, by rw [hcrs]; omega⟩ (Or.inl (by omega))).trans
        (h63 _ (by omega))), readN_prefix (by omega) dat3]
    exact Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega)))
  · intro a ha
    have hg := ha
    unfold Glob at hg
    rw [ggl a ha, h63 a (by omega), gl3 a ha]
    exact hlow a (by omega) (Or.inl (by omega))

/-- A window of a copied stretch. -/
theorem readN_win {μ μ' : Memory} {a b n i m : Nat} (h : μ'.readN a n = μ.readN b n) (hi : i + m ≤ n) :
    μ'.readN (a + i) m = μ.readN (b + i) m := by
  rw [Services.Bootstrap.Decode.Loop.readN_sub μ' a n i m _ h hi,
    Services.Bootstrap.Decode.Loop.readN_sub μ b n i m _ rfl hi]

open Services.Bootstrap.Decode.Loop in
/-- A step bound for the batches from L elements read with `left` to go: the elements' reads
    (`elemB`: at most 9 per octet of the encodings, 70200 per element) and the `realloc`s (with the
    doubling, at most 50 per element read before the last batch, and 2000 per batch). -/
def vvSteps (es : List (List UInt8)) (L left : Nat) : Nat :=
  9 * (off (encs es) (L + left) - off (encs es) L) + 70200 * left + 2000 * (left / L) + 2000 +
    (if left = 0 then 0 else 50 * L + 2000)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **The reader's batches, the payload in the heap** (from the batch end 77 to the reader's return
    t): at the batch end with L ≥ 1 elements read, their headers in the buffer q (the data of an
    allocated chunk of ⌈24L/32⌉ + 1 units) with the items' blocks qs j in the chunks `cs` (allocated,
    not q's, not protected), the protected chunks `K` (allocated, not q's, one of them holding the
    payload), the reader's frame (O at S + 16, ret, v5, v6 at S + 120, S + 112, S + 104) and left ≥ 0
    to go: as `batchB` per batch, until the reader returns to t with the `Vec` `{cap n, ptr q', len n}`
    at O (n = |es| = L + left), element j at q' + 24j as `{|es[j]|, qs' j, |es[j]|}` with qs' j holding
    es[j] in the chunks `cs'`, q' the data of an allocated chunk of exactly ⌈24n/32⌉ + 1 units, the
    context kept for the final state, every protected chunk still allocated, not q''s, with its data,
    and memory from S + 128 up kept off the reader and O; or the run reaches a failed allocator call
    (`Exhausts`). -/
theorem bloopB {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop)
    (S O rd q L c left ptr0 len0 ret t v5 v6 pb S0 S1 : Nat) (es : List (List UInt8)) (cs : List Chunk)
    (qs : Nat → Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (24 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + (encs es).flatten.length ≤ d.addr + 32 * d.size)
    (hcs : ∀ d ∈ cs, d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q ∧ ∀ e, K e → e ≠ d)
    (hS : S0 + 456 ≤ S ∧ S + 128 ≤ S1) (hsp : 2147484104 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (hL : 1 ≤ L) (hc : c ≤ L) (hLl : L + left = es.length) (hn : 24 * es.length < 1073741760)
    (hes : ∀ e ∈ es, e.length < 1073741760)
    (hlen : (encs es).flatten.length ≤ len0 ∧ len0 < 4294967296)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 O)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s0 : μ.readN S 8 = Num.encodeLE 8 c)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 L)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 q) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 L)
    (s120 : μ.readN (S + 120) 8 = Num.encodeLE 8 ret) (s112 : μ.readN (S + 112) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : S + 128 ≤ rd ∧ rd + 16 ≤ S1) (hO : S + 128 ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + off (encs es) L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - off (encs es) L))
    (hpd : μ.readN ptr0 (encs es).flatten.length = (encs es).flatten)
    (hhd : ∀ j (hj : j < L), μ.readN (q + 24 * j) 8 = Num.encodeLE 8 (es[j]'(by omega)).length ∧
      μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 (es[j]'(by omega)).length)
    (hrep : ∀ μ'' : Memory, (∀ d ∈ cs, ∀ a, InData d a → μ''.read a = μ.read a) →
      ∀ j (hj : j < L), μ''.readN (qs j) (es[j]'(by omega)).length = es[j]'(by omega)) :
    (∃ ω' μ' s' q', ∃ cs' : List Chunk, ∃ qs' : Nat → Nat,
      FreeStepsH p (refineContractK cap env) 77 ω μ x t ω' μ' x (vvSteps es L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 128) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 es.length ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + (encs es).flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - (encs es).flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = q' ∧ d.used = true ∧ d.size = (24 * es.length + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ d ∈ cs', d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ e, K e → e ≠ d) ∧
      (∀ j (hj : j < es.length), μ'.readN (q' + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧
        μ'.readN (q' + 24 * j + 8) 8 = Num.encodeLE 8 (qs' j) ∧
        μ'.readN (q' + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length) ∧
      (∀ μ'' : Memory, (∀ d ∈ cs', ∀ a, InData d a → μ''.read a = μ'.read a) →
        ∀ j (hj : j < es.length), μ''.readN (qs' j) es[j].length = es[j]) ∧
      (∀ a, a < 4294967296 → S + 128 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 77 ω μ x (vvSteps es L left) := by
  induction left using Nat.strongRecOn generalizing ω μ s q L c cs qs with
  | _ left ih =>
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpm, hcpu, hcpq⟩ := hK cp hcpK
  rcases Nat.eq_zero_or_pos left with hl0 | hl1
  · -- every element read: the exit
    subst hl0
    have hLn : L = es.length := by omega
    obtain ⟨ω2, run2, g1⟩ :=
      x1 (p := p) (P := P) (R := refineContractK cap env) x ω μ S c ⟨by omega, by omega⟩ h1 (by omega)
        (by rw [Nat.add_zero] at s8; exact s8) s0
        (fun a h1 h2 => Memory.readable_of_writable (H.st a (by omega) (by omega)))
    obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, fr3, rd3, wr3⟩ :=
      x2 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ S O L q L ret t v5 v6 ⟨by omega, by omega⟩
        (by omega) (Or.inr (by omega)) g1 (by omega) (by omega) (by omega) hv5 hv6 s32 s40 s48 s16 s120 s112 s104
        hret hjt hbt (fun a h1 h2 => H.st a (by omega) (by omega)) (fun a h1 h2 => H.st a (by omega) (by omega))
    have hlow3 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a h =>
      fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    have hoffn : off (encs es) L = (encs es).flatten.length := by
      unfold off; rw [hLn, ← encs_length es, List.take_length]
    refine Or.inl ⟨ω3, μ3, s, q, cs, qs, (run2.trans run3).mono (by unfold vvSteps; split <;> omega), z0, z1, z5, z6,
      by rw [← hLn]; exact zO, zO8, by rw [← hLn]; exact zO16, ?_, ?_,
      ctx_congr_data H hcqm (fun a h1 _ => hlow3 a h1) wr3, ⟨cq, hcqm, hcqa, hcqu, by rw [hcqs, hLn]⟩,
      fun d hd => ⟨(hK d hd).1, (hK d hd).2.1, (hK d hd).2.2, fun a ha => ?_⟩, hcs, fun j hj => ?_,
      fun μ'' hag j hj => hrep μ'' (fun d hd a ha => (hag d hd a ha).trans ?_) j (by omega),
      fun a h0 h1 h2 h3 => fr3 a h0 (Or.inr (by omega)) h3, fun a ha => hlow3 a (by unfold Glob at ha; omega)⟩
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega)), hR0, hoffn]
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega)), hR8, hoffn]
    · have := (chunk_in H.wf (hK d hd).1 (hK d hd).2.1).2.2
      have hca := ha
      unfold InData at hca
      exact hlow3 a (by omega)
    · obtain ⟨w0, w8, w16⟩ := hhd j (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [Memory.readN_congr (fun t ht => hlow3 _ (by omega))]; exact w0
      · rw [Memory.readN_congr (fun t ht => hlow3 _ (by omega))]; exact w8
      · rw [Memory.readN_congr (fun t ht => hlow3 _ (by omega))]; exact w16
    · obtain ⟨d1, d2, -, -⟩ := hcs d hd
      have := (chunk_in H.wf d1 d2).2.2
      have hca := ha
      unfold InData at hca
      exact hlow3 a (by omega)
  -- a batch
  have hmo := off_mono (encs es) (show L + min left L ≤ L + left by omega)
  have hmo0 := off_mono (encs es) (show L ≤ L + min left L by omega)
  rcases batchB (p := p) (P := P) env cap hcap1 hcap x ω μ hb s S rd q L c left ptr0 len0 pb S0 S1 es H
      ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ ⟨cp, hcpm, hcpu, hcpq, hcp1, hcp2⟩ hS hsp h1 h7 hL hc hl1 hLl hn hes hlen
      s8 s0 s24 s32 s40 s48 hrd hR0 hR8 hpd with
    ⟨ω1, μ1, s', r, cs1, qs1, run1, a1, a7, m8, m0, m32, m40, m48, fr1, rR0, rR8, H1, hc1, hK1, hcs1, hdat1,
      hhd1, hrep1, gl1⟩ | hex
  rotate_left
  · exact Or.inr (hex.mono (by unfold vvSteps; split <;> omega))
  have hK' : ∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
      ∀ a, InData d a → μ1.read a = μ.read a := fun d hd => by
    obtain ⟨e1, e2, e3⟩ := hK d hd
    obtain ⟨k1, k2, k3⟩ := hK1 d e1 e2 e3
    exact ⟨k1, e2, k2, k3⟩
  have hcs' : ∀ d ∈ cs ++ cs1, d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧ ∀ e, K e → e ≠ d := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨d1, d2, d3, d4⟩ := hcs d hd
      obtain ⟨k1, k2, -⟩ := hK1 d d1 d2 d3
      exact ⟨k1, d2, k2, d4⟩
    · obtain ⟨n1, n2, n3, n4⟩ := hcs1 d hd
      exact ⟨n1, n2, n3, fun e he => n4 e (hK e he).1 (hK e he).2.1 (hK e he).2.2⟩
  have hpd1 : μ1.readN ptr0 (encs es).flatten.length = (encs es).flatten := by
    rw [Memory.readN_congr (fun j hj => (hK1 cp hcpm hcpu hcpq).2.2 _ ⟨by omega, by omega⟩)]; exact hpd
  have hhd' : ∀ j (hj : j < L + min left L),
      μ1.readN (r + 24 * j) 8 = Num.encodeLE 8 (es[j]'(by omega)).length ∧
      μ1.readN (r + 24 * j + 8) 8 = Num.encodeLE 8 (if j < L then qs j else qs1 j) ∧
      μ1.readN (r + 24 * j + 16) 8 = Num.encodeLE 8 (es[j]'(by omega)).length := by
    intro j hj
    rcases Nat.lt_or_ge j L with hjL | hjL
    · simp only [hjL, ↓reduceIte]
      obtain ⟨w0, w8, w16⟩ := hhd j hjL
      refine ⟨?_, ?_, ?_⟩
      · rw [readN_win hdat1 (by omega)]; exact w0
      · rw [show r + 24 * j + 8 = r + (24 * j + 8) by omega, readN_win hdat1 (by omega),
          show q + (24 * j + 8) = q + 24 * j + 8 by omega]; exact w8
      · rw [show r + 24 * j + 16 = r + (24 * j + 16) by omega, readN_win hdat1 (by omega),
          show q + (24 * j + 16) = q + 24 * j + 16 by omega]; exact w16
    · simp only [show ¬ j < L by omega, ↓reduceIte]
      exact hhd1 j hj hjL
  have hrep' : ∀ μ'' : Memory, (∀ d ∈ cs ++ cs1, ∀ a, InData d a → μ''.read a = μ1.read a) →
      ∀ j (hj : j < L + min left L),
        μ''.readN (if j < L then qs j else qs1 j) (es[j]'(by omega)).length = es[j]'(by omega) := by
    intro μ'' hag j hj
    rcases Nat.lt_or_ge j L with hjL | hjL
    · simp only [hjL, ↓reduceIte]
      exact hrep μ'' (fun d hd a ha => (hag d (List.mem_append_left _ hd) a ha).trans (by
        obtain ⟨d1, d2, d3, -⟩ := hcs d hd
        exact (hK1 d d1 d2 d3).2.2 a ha)) j hjL
    · simp only [show ¬ j < L by omega, ↓reduceIte]
      exact hrep1 μ'' (fun d hd a ha => hag d (List.mem_append_right _ hd) a ha) j hj hjL
  have hS1r : ∀ a, S ≤ a → a < S + 128 → (S + 16 ≤ a ∧ a < S + 32 ∨ S + 104 ≤ a) → μ1.read a = μ.read a :=
    fun a h1 h2 h3 => fr1 a (by omega) h3 (Or.inl (by omega))
  have e : L + min left L + (left - min left L) = L + left := by omega
  have hsteps : 64 * ((24 * L + 31) / 32) + 1400 + 9 * (off (encs es) (L + min left L) - off (encs es) L) +
      70100 * min left L + vvSteps es (L + min left L) (left - min left L) ≤ vvSteps es L left := by
    unfold vvSteps
    rw [e]
    rcases Classical.em (min left L < left) with hlt | hlt
    · have hcL : min left L = L := by omega
      rw [hcL] at hmo hmo0 ⊢
      have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
      have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
      split <;> split <;> omega
    · have hcl : min left L = left := by omega
      rw [hcl] at hmo hmo0 ⊢
      have hz : (left - left) / (L + left) = 0 := by simp
      split <;> split <;> omega
  rcases ih (left - min left L) (by omega) ω1 μ1 s' r (L + min left L) (min left L) (cs ++ cs1)
      (fun j => if j < L then qs j else qs1 j) H1 hc1 (fun d hd => ⟨(hK' d hd).1, (hK' d hd).2.1, (hK' d hd).2.2.1⟩)
      hcs' a1 a7 (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s16)
      (by rw [show min left L + (left - min left L) = left by omega]; exact m8) m0
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s24)
      m32 m40 m48
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s120)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s112)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s104)
      rR0 rR8 hpd1 hhd' hrep' with
    ⟨ω', μ', s'', q', cs', qs', run', z0, z1, z5, z6, zO, zO8, zO16, zR0, zR8, zH, zc, zK, zcs, zhd, zrep, zfr, zgl⟩ | hex
  · refine Or.inl ⟨ω', μ', s'', q', cs', qs', (run1.trans run').mono hsteps, z0, z1, z5, z6, zO, zO8, zO16, zR0,
      zR8, zH, zc, fun d hd => ?_, zcs, zhd, zrep,
      fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (by omega)) h2),
      fun a ha => (zgl a ha).trans (gl1 a ha)⟩
    obtain ⟨k1, k2, k3, k4⟩ := zK d hd
    exact ⟨k1, k2, k3, fun a ha => (k4 a ha).trans ((hK' d hd).2.2.2 a ha)⟩
  · exact Or.inr ((Exhausts.pre run1 hex).mono hsteps)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop in
/-- **Reading n ≥ 1 byte strings of any lengths into a fresh `Vec<Vec<u8>>`, the payload in the heap**
    (8): as `vec_vec_u8_heap`, for any n = |es| ≥ 1 with 24n < 2³⁰ − 64 and every element shorter than
    2³⁰ − 64 octets, with the stack pointer at least S0 + 584 (`vec_u8_heap_big`'s and the `realloc`
    wrapper's frames below the reader's). The first min(n, 682) elements go into the block of the
    model's `alloc`; then the reader's batches (`bloopB`) grow the buffer with `realloc` to L + min(left,
    L) elements per batch until all n are read; each element is read by `vec_u8_heap` (at most 16384
    octets) or `vec_u8_heap_big` (more). Either the reader returns to t with the `Vec` `{cap n, ptr q,
    len n}` at O, element j at q + 24j as the `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` with qs j holding
    es[j]; the buffer and the elements' blocks are fresh allocated chunks (`cs`), and the context,
    every allocated chunk of `s` with its data, the stack from sp up off the reader and O, memory below
    196608 and the access of everything from S0 up are kept; or the run reaches a failed allocator call
    (`Exhausts`): an `alloc` or a `realloc` (of the buffer or of an element's block) fails. The
    globals below the allocator (`Glob`) are kept too, as `vec_vec_u8_heap` states. -/
theorem vec_vec_u8_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) {hb : Nat} (s : State) (sp O rd ptr len ret t v5 v6 pb S0 S1 : Nat) (es : List (List UInt8))
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧
      ptr + (encs es).flatten.length ≤ c.addr + 32 * c.size)
    (hS : S0 + 584 ≤ sp ∧ sp ≤ S1) (hsp : 2147484232 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat es.length)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ es.length ∧ 24 * es.length < 1073741760) (hes : ∀ e ∈ es, e.length < 1073741760)
    (hlen : (encs es).flatten.length ≤ len ∧ len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hpd : μ.readN ptr (encs es).flatten.length = (encs es).flatten) :
    (∃ s' ω' μ' q, ∃ cs : List Chunk, ∃ qs : Nat → Nat,
      FreeStepsH p (refineContractK cap env) 8 ω μ x t ω' μ' x
        (9 * (encs es).flatten.length + 70300 * es.length + 40000) ∧ q < 2147483648 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 es.length ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + (encs es).flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - (encs es).flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
      (∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
        ∀ j (hj : j < es.length),
          μ''.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
          μ''.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧
          μ''.readN (qs j) es[j].length = es[j]) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 8 ω μ x (9 * (encs es).flatten.length + 70300 * es.length + 40000) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  rw [hN] at h9 hn
  -- the frame and the call of finish_grow for the first batch
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m104, m112, m128, m120, m80, fr1,
      rd1, wr1⟩ := q1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 (by omega) hv5 hv6 (by omega) (by omega) ⟨hn.1, by omega⟩
    (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨c, hcdef⟩ : ∃ c, min n 682 = c := ⟨_, rfl⟩
  rw [hcdef] at a6 a10 m128
  have hc1 : 1 ≤ c ∧ c ≤ 682 ∧ c ≤ n ∧ (c < n → c = 682) := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    VecPairs.g1e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 168) (sp - 128 + 80) c 8 24 2 n c
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨hc1.1, by omega⟩ (by decide) (by decide)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 168 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 168) (24 * c) 8 pb S0 S1 H2 b1
      b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (24 * c + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 168 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 168) (sp - 128 + 80) (24 * c) q 2 120 n c
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_0 bs_120
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  -- the frame S = sp − 128 in μ5
  have hS5 : ∀ a, sp - 128 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d1, d6, d32, d40, d8, d0, fr6, rd6, wr6⟩ :=
    q4 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 128) q n c ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega)
      (by rw [show sp - 128 + 80 = sp - 128 + 80 from rfl]; exact cres)
      (by rw [show sp - 128 + 88 = sp - 128 + 80 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m128)
      (by rw [show sp - 128 + 8 = sp - 120 by omega,
            Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m120)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS6 : ∀ a, sp - 128 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → (a < sp - 128 ∨ sp - 112 ≤ a) →
      (a < sp - 96 ∨ sp - 80 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (fr6 a h2 (by omega) (by omega)).trans (hS5 a h1 h2 h3)
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, ptr ≤ a → a < ptr + (encs es).flatten.length → μ6.read a = μ.read a := fun a h1 h2 =>
    (h63 a (by omega)).trans ((kd cp hcpm hcpu a ⟨by omega, by omega⟩).trans
      (hlow a (by omega) (Or.inl (by omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have H6 : HeapCtx env pb S0 S1 μ6 s' := ctx_congr_data H3 hnew (fun a h1 _ => h63 a h1) wr36
  -- the first batch's reads
  have hoff0 : off (encs es) 0 = 0 := by simp [off]
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  rcases loopB (p := p) (P := P) (hb := hb) env cap hcap1 hcap x (sp - 128) q rd ptr len pb S0 S1 c
      ⟨q - 32, (24 * c + 31) / 32 + 1, true⟩ cp es ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      hes ⟨by omega, by omega⟩ (Ne.symm hcpne) (by simp only; omega) (by simp only; omega) hcp1 hcp2 hlen
      c 0 s' ω6 μ6 (by omega) hc1.1 H6 hnew rfl hcp' hcpu d1 d6 d32 d40
      (by rw [show sp - 128 + 48 = sp - 80 by omega,
            Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m80)
      (by rw [show sp - 128 + 24 = sp - 104 by omega,
            Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m104)
      (by rw [hoff0, Nat.add_zero, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [hoff0, Nat.sub_zero, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by rw [Memory.readN_congr (fun j hj => hpay6 _ (by omega) (by omega))]; exact hpd) with
    ⟨s2, ω7, μ7, cs, qs, run7, g1, g7, gel, g48, gR0, gR8, H7, keep7, kd7, hcs7, hrep7, gfr, ggl⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre run16 ex).mono (by rw [hoff0]; have := off_le (encs es) c; omega))
  have h76 : ∀ a, sp - 128 ≤ a → a < sp → (a < sp - 80 ∨ sp - 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      μ7.read a = μ6.read a := fun a h1 h2 h3 h4 =>
    gfr a (by omega) h1 (by omega) h4
  have h7S : ∀ a, sp - 128 ≤ a → a < sp → (a < sp - 80 ∨ sp - 24 ≤ a) → (a < sp - 48 ∨ sp - 24 ≤ a) →
      (a < sp - 128 ∨ sp - 112 ≤ a) → (a < sp - 96 ∨ sp - 80 ≤ a) → μ7.read a = μ1.read a :=
    fun a h1 h2 h3 h4 h5 h6 => (h76 a h1 h2 h3 (Or.inl (by omega))).trans (hS6 a h1 (by omega) h4 h5 h6)
  have hcb7 := keep7 _ hnew rfl
  have hcp7 := keep7 cp hcp' hcpu
  have ht3 := H3.wf.2.2.2.1
  unfold TilesOk at ht3
  -- the protected chunks: the allocated chunks of `s`
  have hK : ∀ d, (d ∈ chunks s ∧ d.used = true) → d ∈ chunks s2 ∧ d.used = true ∧ d.addr + 32 ≠ q := by
    intro d ⟨hd, hu⟩
    refine ⟨keep7 d (keep d hd hu) hu, hu, fun e => hfresh d hd hu ?_⟩
    exact Tiles.addr_inj ht3 d (keep d hd hu) _ hnew (by simp only; omega)
  have hkd7 : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ7.read a = μ.read a := by
    intro d hd hu a hia
    have hc' := keep d hd hu
    have hne : d ≠ ⟨q - 32, (24 * c + 31) / 32 + 1, true⟩ := hfresh d hd hu
    have hdis := data_disj H3.wf hc' hnew hne hia
    simp only at hdis
    have := (chunk_in H.wf hd hu).2.2
    have hia' := hia
    unfold InData at hia'
    rw [kd7 d hc' hu a hia (by omega), h63 a (by omega), kd d hd hu a hia]
    exact hlow a (by omega) (Or.inl (by omega))
  have hcs : ∀ d ∈ cs, d ∈ chunks s2 ∧ d.used = true ∧ d.addr + 32 ≠ q ∧
      ∀ e, (e ∈ chunks s ∧ e.used = true) → e ≠ d := by
    intro d hd
    obtain ⟨hdm, hdu, hdf⟩ := hcs7 d hd
    refine ⟨hdm, hdu, fun e => ?_, fun e ⟨he, heu⟩ => hdf e (keep e he heu) heu⟩
    have ht := H7.wf.2.2.2.1; unfold TilesOk at ht
    exact hdf _ hnew rfl (Tiles.addr_inj ht _ hcb7 d hdm (by simp only; omega))
  -- the later batches (none when n ≤ 682)
  rcases bloopB (p := p) (P := P) env cap hcap1 hcap x ω7 μ7 hb s2 (fun d => d ∈ chunks s ∧ d.used = true)
      (sp - 128) O rd q c c (n - c) ptr len ret t v5 v6 pb S0 S1 es cs qs H7
      ⟨_, hcb7, by simp only; omega, rfl, rfl⟩ hK ⟨cp, ⟨hcpm, hcpu⟩, hcp1, hcp2⟩ hcs ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ g1 g7 hc1.1 (Nat.le_refl c) (by omega) (by omega) hes hlen
      (by rw [show sp - 128 + 16 = sp - 112 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega))]; exact m112)
      (by rw [show c + (n - c) = n by omega, Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega)
        (by omega) (by omega))]; exact d8)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d0)
      (by rw [show sp - 128 + 24 = sp - 104 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega))]; exact m104)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d32)
      (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d40)
      g48
      (by rw [show sp - 128 + 120 = sp - 8 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega))]; exact m8)
      (by rw [show sp - 128 + 112 = sp - 16 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega))]; exact m16)
      (by rw [show sp - 128 + 104 = sp - 24 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega))]; exact m24)
      hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr gR0 gR8
      (by rw [Memory.readN_congr (fun j hj => hkd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)]; exact hpd)
      (fun j hj => gel j hj (Nat.zero_le _)) (fun μ'' hag j hj => hrep7 μ'' hag j hj (Nat.zero_le _)) with
    ⟨ω', μ', s'', q', cs', qs', run', z0, z1, z5, z6, zO, zO8, zO16, zR0, zR8, zH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, zK, zcs, zhd, zrep, zfr, zgl⟩ | ex
  rotate_left
  · have hdv : 2000 * ((n - c) / c) ≤ 3 * n := by
      rcases Nat.lt_or_ge n 683 with h | h
      · rw [show n - c = 0 by omega, Nat.zero_div]; omega
      · rw [show c = 682 by omega]; omega
    have hmo := off_mono (encs es) (show c ≤ c + (n - c) by omega)
    have hle := off_le (encs es) (c + (n - c))
    exact Or.inr ((Exhausts.pre (run16.trans run7) ex).mono (by rw [hoff0]; unfold vvSteps; split <;> omega))
  have runAll := (run16.trans run7).trans run'
  obtain ⟨hfb, -, hfT⟩ := chunk_in zH.wf hcfm hcfu
  have hyb := zH.hb0
  have hybT := zH.hbT
  rw [hN] at zO zO16 hcfs
  have hcf : cf = ⟨q' - 32, (24 * n + 31) / 32 + 1, true⟩ := by
    obtain ⟨ca, cs0, cu⟩ := cf
    simp only at hcfa hcfu hcfs
    rw [hcfu, hcfs]; congr 1; omega
  subst hcf
  simp only at hfb hfT
  have hdv : 2000 * ((n - c) / c) ≤ 3 * n := by
    rcases Nat.lt_or_ge n 683 with h | h
    · rw [show n - c = 0 by omega, Nat.zero_div]; omega
    · rw [show c = 682 by omega]; omega
  have hmo := off_mono (encs es) (show c ≤ c + (n - c) by omega)
  have hle := off_le (encs es) (c + (n - c))
  refine Or.inl ⟨s'', ω', μ', q', ⟨q' - 32, (24 * n + 31) / 32 + 1, true⟩ :: cs', qs',
    runAll.mono (by rw [hoff0]; unfold vvSteps; split <;> omega), by omega, z0,
    by rw [z1]; congr 1; omega, z5, z6, by rw [hN]; exact zO, zO8, by rw [hN]; exact zO16, zR0, zR8, zH,
    fun d hd hu => (zK d ⟨hd, hu⟩).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd hu a hia
    exact ((zK d ⟨hd, hu⟩).2.2.2 a hia).trans (hkd7 d hd hu a hia)
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · refine ⟨hcfm, rfl, fun e he heu heq => (zK e ⟨he, heu⟩).2.2.1 ?_⟩
      rw [heq]; simp only; omega
    · obtain ⟨k1, k2, -, k4⟩ := zcs d hd
      exact ⟨k1, k2, fun e he heu => k4 e ⟨he, heu⟩⟩
  · intro μ'' hag j hj
    have hj' : j < n := by omega
    have hcbs : ∀ a, InData (⟨q' - 32, (24 * n + 31) / 32 + 1, true⟩ : Chunk) a → μ''.read a = μ'.read a :=
      fun a hia => hag _ List.mem_cons_self a hia
    obtain ⟨w0, w8, w16⟩ := zhd j hj
    refine ⟨?_, ?_, ?_, zrep μ'' (fun d hd a hia => hag d (List.mem_cons_of_mem _ hd) a hia) j hj⟩
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w0
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w8
    · rw [Memory.readN_congr (fun t ht => hcbs _ ⟨by simp only; omega, by simp only; omega⟩)]; exact w16
  · intro a h0 h1 h2 h3
    rw [zfr a h0 (by omega) h2 h3, gfr a h0 (by omega) (Or.inr (by omega)) h2]
    exact hhigh a h0 h1
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd runAll
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    rw [zgl a ha', ggl a ha', h63 a (by omega),
      hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht3.mem_lt c hc).1; omega)) a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    have := H.hSb
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd runAll
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.VecVecU8
