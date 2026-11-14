import Services.Bootstrap.Decode.ElemsBig

/-!
# Ownership of a decoded `Vec<Vec<u8>>`: which allocated chunks hold its buffers

`VecVecElem.VecVecRep` describes the slot of a decoded `DeleteItems` / `Export` / `Imported`
(`Vec<Vec<u8>>`, GP v0.8.0 B.7) by its contents only. A consumer that frees the buffers (`dealloc`)
needs to know which allocated chunks hold them: `VecVecRepC` adds, for the returned list `cs` of fresh
allocated chunks, the outer buffer's chunk (its data starting at the buffer, holding the 24n octets of
headers), each non-empty item's chunk (its data starting at the item's pointer, holding the item),
the dangling pointer 1 of each empty item, the distinctness of all these pointers and their bounds.

The reader-level proofs (`elemBO` … `vec_vec_u8_heap_bigO`, `vecvec_heap_bigO`) are copies of the
originals in `VecVecU8Big` / `VariantsBig` with one more conjunct each, carrying the chunk of every
item (`ItemsOwn`) and of the buffer; `vecvec_elem_bigC` is `ElemsBig.vecvec_elem_big` with
`VecVecRepC` (stated as `ElemOkAFC`, `ElemOkAF` with the representation predicate seeing `cs`).
-/

namespace Services.Bootstrap.Decode.VecVecU8

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

open Picoalloc Services.Bootstrap.Decode.LoopA in
/-- **The items' blocks** j ∈ [lo, hi) of `es`, at the pointers qs j: an empty item has the dangling
    pointer 1; a non-empty one is held by a chunk of `cs` whose data starts at qs j; the non-empty
    items' pointers are pairwise distinct. -/
def ItemsOwn (es : List (List UInt8)) (cs : List Chunk) (qs : Nat → Nat) (lo hi : Nat) : Prop :=
  (∀ j (hj : j < es.length), lo ≤ j → j < hi →
    (es[j].length = 0 → qs j = 1) ∧
    (es[j].length ≠ 0 → ∃ c ∈ cs, c.addr + 32 = qs j ∧ qs j + es[j].length ≤ c.addr + 32 * c.size)) ∧
  (∀ j j' (hj : j < es.length) (hj' : j' < es.length), lo ≤ j → j < hi → lo ≤ j' → j' < hi → j ≠ j' →
    es[j].length ≠ 0 → es[j'].length ≠ 0 → qs j ≠ qs j')

open Picoalloc in
theorem ItemsOwn.congr {es : List (List UInt8)} {cs cs' : List Chunk} {qs qs' : Nat → Nat} {lo hi : Nat}
    (h : ItemsOwn es cs qs lo hi) (hsub : ∀ c ∈ cs, c ∈ cs') (e : ∀ j, lo ≤ j → j < hi → qs' j = qs j) :
    ItemsOwn es cs' qs' lo hi := by
  refine ⟨fun j hj h1 h2 => ?_, fun j j' hj hj' h1 h2 h3 h4 hne hl hl' => ?_⟩
  · obtain ⟨a, b⟩ := h.1 j hj h1 h2
    rw [e j h1 h2]
    refine ⟨a, fun hl => ?_⟩
    obtain ⟨c, hc, hc1, hc2⟩ := b hl
    exact ⟨c, hsub c hc, hc1, hc2⟩
  · rw [e j h1 h2, e j' h3 h4]
    exact h.2 j j' hj hj' h1 h2 h3 h4 hne hl hl'

open Picoalloc in
theorem ItemsOwn.nil (es : List (List UInt8)) (cs : List Chunk) (qs : Nat → Nat) (lo : Nat) :
    ItemsOwn es cs qs lo lo :=
  ⟨fun _ _ h1 h2 => absurd h2 (by omega), fun _ _ _ _ h1 h2 => absurd h2 (by omega)⟩

open Picoalloc in
theorem ItemsOwn.single {es : List (List UInt8)} {cs : List Chunk} {qs : Nat → Nat} {k : Nat} (hk : k < es.length)
    (h0 : es[k].length = 0 → qs k = 1)
    (h1 : es[k].length ≠ 0 → ∃ c ∈ cs, c.addr + 32 = qs k ∧ qs k + es[k].length ≤ c.addr + 32 * c.size) :
    ItemsOwn es cs qs k (k + 1) := by
  refine ⟨fun j hj a b => ?_, fun j j' hj hj' a b c d hne _ _ => absurd (show j = j' by omega) hne⟩
  obtain rfl : j = k := by omega
  exact ⟨h0, h1⟩

open Picoalloc Services.Bootstrap.Decode.LoopA in
/-- Two stretches of items whose chunks are distinct allocated chunks of one well-formed state. -/
theorem ItemsOwn.append {es : List (List UInt8)} {cs1 cs2 : List Chunk} {qs : Nat → Nat} {lo mid hi : Nat}
    {s : State} (hwf : WF s) (h1 : ItemsOwn es cs1 qs lo mid) (h2 : ItemsOwn es cs2 qs mid hi)
    (m1 : ∀ c ∈ cs1, c ∈ chunks s) (m2 : ∀ c ∈ cs2, c ∈ chunks s) (hne : ∀ c ∈ cs1, ∀ d ∈ cs2, c ≠ d) :
    ItemsOwn es (cs1 ++ cs2) qs lo hi := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have cross : ∀ j j' (hj : j < es.length) (hj' : j' < es.length), lo ≤ j → j < mid → mid ≤ j' → j' < hi →
      es[j].length ≠ 0 → es[j'].length ≠ 0 → qs j ≠ qs j' := by
    intro j j' hj hj' a b c d hl hl' heq
    obtain ⟨c1, hc1, e1, -⟩ := (h1.1 j hj a b).2 hl
    obtain ⟨c2, hc2, e2, -⟩ := (h2.1 j' hj' c d).2 hl'
    exact hne c1 hc1 c2 hc2 (Tiles.addr_inj ht c1 (m1 c1 hc1) c2 (m2 c2 hc2) (by omega))
  refine ⟨fun j hj a b => ?_, fun j j' hj hj' a b c d hjj hl hl' => ?_⟩
  · rcases Nat.lt_or_ge j mid with hm | hm
    · obtain ⟨x, y⟩ := h1.1 j hj a hm
      refine ⟨x, fun hl => ?_⟩
      obtain ⟨c, hc, e⟩ := y hl
      exact ⟨c, List.mem_append_left _ hc, e⟩
    · obtain ⟨x, y⟩ := h2.1 j hj hm b
      refine ⟨x, fun hl => ?_⟩
      obtain ⟨c, hc, e⟩ := y hl
      exact ⟨c, List.mem_append_right _ hc, e⟩
  · rcases Nat.lt_or_ge j mid with hm | hm <;> rcases Nat.lt_or_ge j' mid with hm' | hm'
    · exact h1.2 j j' hj hj' a hm c hm' hjj hl hl'
    · exact cross j j' hj hj' a hm hm' d hl hl'
    · exact fun e => cross j' j hj' hj c hm' hm b hl' hl e.symm
    · exact h2.2 j j' hj hj' hm b hm' d hjj hl hl'

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **One element read, any length** (197 … 229): as `elem`, for an element e of any length below
    2³⁰ − 64 (`vec_u8_heap` up to 16384 octets, `vec_u8_heap_big` above), with the deeper stack
    `vec_u8_heap_big` needs. -/
theorem elemBO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (e.length = 0 → qe = 1) ∧
      (e.length ≠ 0 → ∃ c ∈ cs, c.addr + 32 = qe ∧ qe + e.length ≤ c.addr + 32 * c.size)) ∨
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
        exact b4 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      fun _ => rfl, fun h => absurd rfl h⟩
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
        v1, v6', by omega, vc, vp, vl, ?_, ?_, H4, keep, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by omega),
        fun _ => ⟨_, List.mem_singleton_self _, by simp only; omega, by simp only; omega⟩⟩
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
        v1, v6', by omega, vc, vp, vl, ?_, ?_, H4, keep, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by omega),
        fun _ => ⟨_, List.mem_singleton_self _, by simp only; omega, by simp only; omega⟩⟩
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
/-- **One pass of the read loop, any element length** (197 … 197, or 77): as `pass`, with `elemBO` for
    the element, any capacity c with 24c < 2³⁰ − 64. -/
theorem passBO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (e.length = 0 → qe = 1) ∧
      (e.length ≠ 0 → ∃ c ∈ cs, c.addr + 32 = qe ∧ qe + e.length ≤ c.addr + 32 * c.size)) ∨
    Exhausts env cap pb p P 197 ω μ x (9 * e.length + 70100) := by
  have hS1 := H.hS1
  obtain ⟨hcbb, hcbT, hcbT'⟩ := chunk_in H.wf hcb hcbu
  have hbT := H.hbT
  rcases elemBO (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S r rd ptr len pb S0 S1 e H hS hSa h1 h6
      (by omega) s24 hrd hR0 hR8 hm hlen hpay henc with
    ⟨s', ω4, μ4, qe, cs, run4, e1, e6, hqe, s56, s64, s72, R0, R8, H4, keep, kd, hcs, hrep, fr4, gl4, own0, own1⟩ | ex
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
        exact (low5 a (by omega) (Or.inl (by omega))).trans (gl4 a (by unfold Glob; omega)), own0, own1⟩
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
open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **The read loop, any element length, any capacity** (197 … 77): as `loop`, for the elements
    k … N − 1 of `es` (N ≤ |es|, 24N < 2³⁰ − 64, the capacity N at S + 32), each of any length below
    2³⁰ − 64 (`passBO`). -/
theorem loopBO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
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
        (∀ a, Glob a → μ'.read a = μ.read a) ∧ ItemsOwn es cs qs k N) ∨
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
  rcases passBO (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s S q N k (i + 1) rd
      (ptr0 + off (encs es) k) (len0 - off (encs es) k) pb S0 S1 cb es[k] H hS hSa h1 h6 ⟨by omega, by omega⟩
      ⟨by omega, hN.2⟩ hcb hcbu hq1 hq2 s32 s40 s48 s24 hrd R0 R8 hm ⟨by omega, by omega⟩
      ⟨cp, hcp, hcpu, by omega, by omega⟩ henc with
    ⟨s1, ω1, μ1, j, qe, cs1, run1, hj1, hj2, f1, f6, fe0, fe1, fe2, f48, fR0, fR8, H1, keep1, kd1, hcs1, hrep1,
      ffr1, gl1, own0, own1⟩ | ex
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
      ?_, ?_, H1, keep1, ?_, hcs1, ?_, ffr1, gl1, by rw [← hkn]; exact ItemsOwn.single hk own0 own1⟩
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
      ⟨s2, ω2, μ2, cs2, qs2, run2, g1, g7, gel, g48, gR0, gR8, H2, keep2, kd2, hcs2, hrep2, gfr, ggl, gown⟩ | ex
    · have hcb2 := keep2 cb hcb1 hcbu
      refine Or.inl ⟨s2, ω2, μ2, cs1 ++ cs2, fun j' => if j' = k then qe else qs2 j',
        (run1.trans run2).mono (by omega), g1, g7, ?_, g48, gR0, gR8, H2,
        fun c hc hu => keep2 c (keep1 c hc hu) hu, ?_, ?_, ?_, ?_, fun a ha => (ggl a ha).trans (gl1 a ha), ?_⟩
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
      · have hcs1' : ∀ c ∈ cs1, c ∈ chunks s2 := fun c hc => keep2 c (hcs1 c hc).1 (hcs1 c hc).2.1
        refine ItemsOwn.append (mid := k + 1) H2.wf ?_ ?_ hcs1' (fun c hc => (hcs2 c hc).1)
          (fun c hc d hd e => (hcs2 d hd).2.2 c (hcs1 c hc).1 (hcs1 c hc).2.1 e)
        · exact ItemsOwn.single hk (fun h => by simp only [ite_true]; exact own0 h)
            (fun h => by simp only [ite_true]; exact own1 h)
        · exact gown.congr (fun c hc => hc) (fun j h1 h2 => by simp only [show j ≠ k by omega, ite_false])
    · exact Or.inr ((Exhausts.pre run1 ex).mono (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll Services.Bootstrap.Decode.Loop in
/-- **One later batch, the payload in the heap** (77 … 77): at the batch end with L ≥ 1 elements read
    (ω₇ = L; the buffer q of capacity L at S + 40, S + 32, S + 48; S + 8, S holding c + left, c) and
    left ≥ 1 to go, q the data of an allocated chunk of ⌈24L/32⌉ + 1 units, the payload (the
    elements' encodings) inside an allocated chunk that is not q's: either the model's `realloc` of q
    to ⌈24(L + c')/32⌉ units (c' = min(left, L)) gives a block r and state `s'`, and the reader reads
    the batch's c' elements (`loopBO`) into r, reaching the batch end again with ω₇ = L + c', the `Vec`
    `{cap L + c', ptr r, len L + c'}`, r holding q's first 24L octets (the old headers) and the new
    elements' headers, r the data of an allocated chunk of ⌈24(L + c')/32⌉ + 1 units, the new
    elements' blocks fresh allocated chunks (`cs`), every allocated chunk of `s` other than q's still
    allocated, not r's, with its data; or the run reaches a failed allocator call (`Exhausts`). -/
theorem batchBO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ ItemsOwn es cs qs L (L + min left L)) ∨
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
  rcases loopBO (p := p) (P := P) (hb := hb) env cap hcap1 hcap x S r rd ptr0 len0 pb S0 S1 (L + c') cr cp es
      hS hsp ⟨by omega, by omega⟩ hes hrd (Ne.symm hcpne) (by omega) (by rw [hcrs]; omega) hcp1 hcp2 hlen
      c' L s' ω6 μ6 (by omega) hc1.1 H6 hcrm hcru hcp' hcpu d1 d6 d32 d40
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s48)
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s24)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by rw [Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)]; exact hpd) with
    ⟨s2, ω7, μ7, cs1, qs1, run7, g1, g7, gel, g48, gR0, gR8, H7, keep7, kd7, hcs7, hrep7, gfr, ggl, gown⟩ | ex
  all_goals subst hcdef
  rotate_left
  · exact Or.inr ((Exhausts.pre run16 ex).mono (by omega))
  have h76 : ∀ a, S ≤ a → a < S + 48 → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ6.read a := fun a h1 h2 h3 =>
    gfr a (by omega) h1 (Or.inl h2) h3
  have hcr2 := keep7 cr hcrm hcru
  refine Or.inl ⟨ω7, μ7, s2, r, cs1, qs1, (run16.trans run7).mono (by omega), g1, g7, ?_, ?_, ?_, ?_, g48, ?_,
    gR0, gR8, H7, ⟨cr, hcr2, hcra, hcru, hcrs⟩, ?_, ?_, ?_, fun j hj hLj => gel j hj hLj,
    fun μ'' hag j hj hLj => hrep7 μ'' hag j hj hLj, ?_, gown⟩
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

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **The reader's batches, the payload in the heap** (from the batch end 77 to the reader's return
    t): at the batch end with L ≥ 1 elements read, their headers in the buffer q (the data of an
    allocated chunk of ⌈24L/32⌉ + 1 units) with the items' blocks qs j in the chunks `cs` (allocated,
    not q's, not protected), the protected chunks `K` (allocated, not q's, one of them holding the
    payload), the reader's frame (O at S + 16, ret, v5, v6 at S + 120, S + 112, S + 104) and left ≥ 0
    to go: as `batchBO` per batch, until the reader returns to t with the `Vec` `{cap n, ptr q', len n}`
    at O (n = |es| = L + left), element j at q' + 24j as `{|es[j]|, qs' j, |es[j]|}` with qs' j holding
    es[j] in the chunks `cs'`, q' the data of an allocated chunk of exactly ⌈24n/32⌉ + 1 units, the
    context kept for the final state, every protected chunk still allocated, not q''s, with its data,
    and memory from S + 128 up kept off the reader and O; or the run reaches a failed allocator call
    (`Exhausts`). -/
theorem bloopBO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
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
      ∀ j (hj : j < L), μ''.readN (qs j) (es[j]'(by omega)).length = es[j]'(by omega))
    (hown : ItemsOwn es cs qs 0 L) :
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ ItemsOwn es cs' qs' 0 es.length) ∨
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
      fun a h0 h1 h2 h3 => fr3 a h0 (Or.inr (by omega)) h3, fun a ha => hlow3 a (by unfold Glob at ha; omega), by rw [← hLn]; exact hown⟩
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
  rcases batchBO (p := p) (P := P) env cap hcap1 hcap x ω μ hb s S rd q L c left ptr0 len0 pb S0 S1 es H
      ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ ⟨cp, hcpm, hcpu, hcpq, hcp1, hcp2⟩ hS hsp h1 h7 hL hc hl1 hLl hn hes hlen
      s8 s0 s24 s32 s40 s48 hrd hR0 hR8 hpd with
    ⟨ω1, μ1, s', r, cs1, qs1, run1, a1, a7, m8, m0, m32, m40, m48, fr1, rR0, rR8, H1, hc1, hK1, hcs1, hdat1,
      hhd1, hrep1, gl1, own1⟩ | hex
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
  have hown' : ItemsOwn es (cs ++ cs1) (fun j => if j < L then qs j else qs1 j) 0 (L + min left L) :=
    ItemsOwn.append (mid := L) H1.wf
      (hown.congr (fun c hc => hc) (fun j _ h2 => by simp only [h2, ↓reduceIte]))
      (own1.congr (fun c hc => hc) (fun j h1 _ => by simp only [show ¬ j < L by omega, ↓reduceIte]))
      (fun c hc => (hcs' c (List.mem_append_left _ hc)).1) (fun c hc => (hcs1 c hc).1)
      (fun c hc d hd e => (hcs1 d hd).2.2.2 c (hcs c hc).1 (hcs c hc).2.1 (hcs c hc).2.2.1 e)
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
      rR0 rR8 hpd1 hhd' hrep' hown' with
    ⟨ω', μ', s'', q', cs', qs', run', z0, z1, z5, z6, zO, zO8, zO16, zR0, zR8, zH, zc, zK, zcs, zhd, zrep, zfr, zgl, zown⟩ | hex
  · refine Or.inl ⟨ω', μ', s'', q', cs', qs', (run1.trans run').mono hsteps, z0, z1, z5, z6, zO, zO8, zO16, zR0,
      zR8, zH, zc, fun d hd => ?_, zcs, zhd, zrep,
      fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (by omega)) h2),
      fun a ha => (zgl a ha).trans (gl1 a ha), zown⟩
    obtain ⟨k1, k2, k3, k4⟩ := zK d hd
    exact ⟨k1, k2, k3, fun a ha => (k4 a ha).trans ((hK' d hd).2.2.2 a ha)⟩
  · exact Or.inr ((Exhausts.pre run1 hex).mono hsteps)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop in
/-- **Reading n ≥ 1 byte strings of any lengths into a fresh `Vec<Vec<u8>>`, the payload in the heap**
    (8): as `vec_vec_u8_heap`, for any n = |es| ≥ 1 with 24n < 2³⁰ − 64 and every element shorter than
    2³⁰ − 64 octets, with the stack pointer at least S0 + 584 (`vec_u8_heap_big`'s and the `realloc`
    wrapper's frames below the reader's). The first min(n, 682) elements go into the block of the
    model's `alloc`; then the reader's batches (`bloopBO`) grow the buffer with `realloc` to L + min(left,
    L) elements per batch until all n are read; each element is read by `vec_u8_heap` (at most 16384
    octets) or `vec_u8_heap_big` (more). Either the reader returns to t with the `Vec` `{cap n, ptr q,
    len n}` at O, element j at q + 24j as the `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` with qs j holding
    es[j]; the buffer and the elements' blocks are fresh allocated chunks (`cs`), and the context,
    every allocated chunk of `s` with its data, the stack from sp up off the reader and O, memory below
    196608 and the access of everything from S0 up are kept; or the run reaches a failed allocator call
    (`Exhausts`): an `alloc` or a `realloc` (of the buffer or of an element's block) fails. The
    globals below the allocator (`Glob`) are kept too, as `vec_vec_u8_heap` states. -/
theorem vec_vec_u8_heap_bigO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a) ∧
      (∃ co ∈ cs, co.addr + 32 = q ∧ q + 24 * es.length ≤ co.addr + 32 * co.size) ∧
      ItemsOwn es cs qs 0 es.length ∧ (∀ j (hj : j < es.length), es[j].length ≠ 0 → qs j ≠ q)) ∨
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
  rcases loopBO (p := p) (P := P) (hb := hb) env cap hcap1 hcap x (sp - 128) q rd ptr len pb S0 S1 c
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
    ⟨s2, ω7, μ7, cs, qs, run7, g1, g7, gel, g48, gR0, gR8, H7, keep7, kd7, hcs7, hrep7, gfr, ggl, gown⟩ | ex
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
  rcases bloopBO (p := p) (P := P) env cap hcap1 hcap x ω7 μ7 hb s2 (fun d => d ∈ chunks s ∧ d.used = true)
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
      (fun j hj => gel j hj (Nat.zero_le _)) (fun μ'' hag j hj => hrep7 μ'' hag j hj (Nat.zero_le _)) gown with
    ⟨ω', μ', s'', q', cs', qs', run', z0, z1, z5, z6, zO, zO8, zO16, zR0, zR8, zH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, zK, zcs, zhd, zrep, zfr, zgl, zown⟩ | ex
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
    fun d hd hu => (zK d ⟨hd, hu⟩).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact ⟨_, List.mem_cons_self, by simp only; omega, by simp only; omega⟩
  · exact zown.congr (fun c hc => List.mem_cons_of_mem _ hc) (fun _ _ _ => rfl)
  · intro j hj hl
    obtain ⟨c, hc, hca, -⟩ := (zown.1 j hj (Nat.zero_le _) hj).2 hl
    rw [← hca]
    exact (zcs c hc).2.2.1

end Services.Bootstrap.Decode.VecVecU8

namespace Services.Bootstrap.Decode.VariantsBig

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Alloc
  JAM Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecEmpty

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`DeleteItems` (5), `Export` (10) or `Imported` (19) with any n ≥ 1 items of any length, the
    payload in the heap** (GP v0.8.0 B.7): from 20626 with the tag read without error (its handler h
    and return addresses r1, r2, r3 and discriminant word W as in `VecVecElem.vecvec_elem`), the
    reader `{ptr, len}` at rd (ω₆) holding ℰ(n) (w octets) and the items' encodings (each
    ℰ(|e|) ++ e, L octets in all), all inside an allocated chunk of the allocator's state `s` (context
    `HeapCtx`, under `refineContractK cap`), with 24n < 2³⁰ − 64, every item shorter than 2³⁰ − 64
    octets and A at least S0 + 632 (the reader at A − 48 needing S0 + 584,
    `VecVecU8.vec_vec_u8_heap_bigO`): either `Instruction::decode` returns the variant in O (the
    discriminant word W and the `Vec` `{cap n, ptr q, len n}` at O + 8, item j at q + 24j the
    `Vec<u8>` `{|es[j]|, qs j, |es[j]|}` with qs j holding es[j], in the fresh allocated chunks `cs`),
    the reader advanced by w + L, the context kept for the final state `s'` and every allocated chunk
    of `s` kept with its data; or the run reaches a failed allocator call (`Exhausts`). The globals
    below the allocator (`Glob`) are kept. -/
theorem vecvec_heap_bigO {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a) ∧
      (∃ co ∈ cs, co.addr + 32 = q ∧ q + 24 * es.length ≤ co.addr + 32 * co.size) ∧
      VecVecU8.ItemsOwn es cs qs 0 es.length ∧ (∀ j (hj : j < es.length), es[j].length ≠ 0 → qs j ≠ q)) ∨
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
  rcases VecVecU8.vec_vec_u8_heap_bigO (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω4 μ3 s (A - 48) (A - 48)
      rd (ptr + w) (len - w) r3 _ O rd pb S0 S1 es H3 ⟨cp, hcpm, hcpu, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) (by rw [c6, d6, b6]) c7
      (by rw [c8, d6, b6]) c9 hr3 rfl bs3 hO64 (by omega) hn hes
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩ (Or.inl (by omega)) dR0 dR8
      (by rw [hLd, Memory.readN_congr (fun j hj => b3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]; exact hpd) with
    ⟨s', ω5, μ5, q, cs, qs, run5, hq, v0, v1, v5', v6', vc, vp, vl, vR0, vR8, H5, keep, kd5, hcs, hrep, vfr, vlo, vgl, vwr, vco, vown, vne⟩ |
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
    H6, keep, ?_, hcs, fun μ'' hag => ?_, hfar, ?_, ?_, ?_, vco, vown, vne⟩
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

namespace Services.Bootstrap.Decode.VecVecOwn

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.VecVecElem
  Services.Bootstrap.Decode.VecVecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **A `Vec<Vec<u8>>` variant's slot, with the chunks holding its buffers** (`VecVecRep` and the
    ownership a consumer freeing the buffers needs), for the list `cs` of chunks the decoder returns:
    the discriminant word W; the `Vec` `{cap n, ptr q, len n}` (n = |es|), item j at q + 24j the
    `Vec<u8>` `{cap |es[j]|, ptr qs j, len |es[j]|}` with es[j] at qs j (in μ); and
    1. the buffer q is the data of a chunk co ∈ cs (co.addr + 32 = q), allocated, holding the 24n
       octets of headers;
    2. an empty item has the dangling pointer 1; a non-empty item j is the data of a chunk of cs
       (allocated, not co, its data starting at qs j and holding the |es[j]| octets);
    3. the non-empty items' pointers differ from q and from each other;
    4. q + 24n + 8 ≤ 2³¹ and qs j + |es[j]| ≤ 2³¹.
    The capacities are the lengths: n for the outer `Vec` (slot word 8), |es[j]| for item j (header
    word 0). -/
def VecVecRepC (W : Nat) (es : List (List UInt8)) (cs : List Chunk) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 W ∧
  ∃ q, ∃ qs : Nat → Nat, ∃ co : Chunk, (bs.drop 8).take 8 = Num.encodeLE 8 es.length ∧
    (bs.drop 16).take 8 = Num.encodeLE 8 q ∧ (bs.drop 24).take 8 = Num.encodeLE 8 es.length ∧
    (∀ j (hj : j < es.length),
      μ.readN (q + 24 * j) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ.readN (qs j) es[j].length = es[j]) ∧
    co ∈ cs ∧ co.used = true ∧ co.addr + 32 = q ∧ q + 24 * es.length ≤ co.addr + 32 * co.size ∧
    (∀ j (hj : j < es.length), es[j].length = 0 → qs j = 1) ∧
    (∀ j (hj : j < es.length), es[j].length ≠ 0 → ∃ c ∈ cs, c.used = true ∧ c ≠ co ∧
      c.addr + 32 = qs j ∧ qs j + es[j].length ≤ c.addr + 32 * c.size) ∧
    (∀ j (hj : j < es.length), es[j].length ≠ 0 → qs j ≠ q) ∧
    (∀ j j' (hj : j < es.length) (hj' : j' < es.length), j ≠ j' → es[j].length ≠ 0 → es[j'].length ≠ 0 →
      qs j ≠ qs j') ∧
    q + 24 * es.length + 8 ≤ 2147483648 ∧ (∀ j (hj : j < es.length), qs j + es[j].length ≤ 2147483648)

/-- `VecVecRepC` forgets to `VecVecRep`. -/
theorem VecVecRepC.toRep {W : Nat} {es : List (List UInt8)} {cs : List Chunk} {bs : List UInt8} {μ : Memory}
    (h : VecVecRepC W es cs bs μ) : VecVecRep W es bs μ := by
  obtain ⟨h0, q, qs, -, h8, h16, h24, hj, -⟩ := h
  exact ⟨h0, q, qs, h8, h16, h24, hj⟩

/-- A stretch [x, x + m) starting at a chunk's data and ending inside it is in its data. -/
theorem inData_of {c : Chunk} {x m : Nat} (h1 : c.addr + 32 = x) (h2 : x + m ≤ c.addr + 32 * c.size) :
    ∀ a, x ≤ a → a < x + m → InData c a := fun a ha hb => ⟨by omega, by omega⟩

/-- **`ElemOkAF` with the representation seeing the returned chunks**: as `LoopA.ElemOkAF`, the
    predicate `Rep cs` of the slot for the fresh allocated chunks `cs` the element returns. -/
def ElemOkAFC (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program) (F RD N : Nat)
    (enc : List UInt8) (Rep : List Chunk → List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat) (s : State),
    ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (F + 120) → ω[6] = UInt64.ofNat RD →
    ω[7] = UInt64.ofNat 0 → μ.read F = enc.headD 0 →
    μ.readN RD 8 = Num.encodeLE 8 ptr → μ.readN (RD + 8) 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN (F + 48) 8 = Num.encodeLE 8 18 → μ.readN (F + 40) 8 = Num.encodeLE 8 v5 →
    μ.readN (F + 32) 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true) →
    (∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true) →
    HeapCtx env pb S0 S1 μ s → (∀ a, Glob a → μ.read a = gl a) →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + (enc.length - 1) ≤ c.addr + 32 * c.size) →
    (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 20626 ω μ x 723 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN RD 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN (RD + 8) 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN (F + 120) 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          Rep cs (μ'.readN (F + 120) 232) μ'') ∧
      (∀ a, (F + 32) ≤ a → a < 4294967296 →
        (a < RD ∨ (RD + 16) ≤ a) → (a < (F + 120) ∨ (F + 352) ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x N

/-- **`ElemOkAFG` with the representation seeing the returned chunks**: as `LoopA.ElemOkAF`, the
    predicate `Rep cs` of the slot for the fresh allocated chunks `cs` the element returns; under any
    host fit for the allocator (`ElemOkAFC`'s host-generic form). -/
def ElemOkAFCG {X : Type} (env : HeapHost X) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program) (F RD N : Nat)
    (enc : List UInt8) (Rep : List Chunk → List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : X) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat) (s : State),
    ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (F + 120) → ω[6] = UInt64.ofNat RD →
    ω[7] = UInt64.ofNat 0 → μ.read F = enc.headD 0 →
    μ.readN RD 8 = Num.encodeLE 8 ptr → μ.readN (RD + 8) 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN (F + 48) 8 = Num.encodeLE 8 18 → μ.readN (F + 40) 8 = Num.encodeLE 8 v5 →
    μ.readN (F + 32) 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true) →
    (∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true) →
    HeapCtxC env.code pb S0 S1 μ s → (∀ a, Glob a → μ.read a = gl a) →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + (enc.length - 1) ≤ c.addr + 32 * c.size) →
    (∃ ω' μ' s', FreeStepsH p (env.rel cap) 20626 ω μ x 723 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN RD 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN (RD + 8) 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN (F + 120) 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          Rep cs (μ'.readN (F + 120) 232) μ'') ∧
      (∀ a, (F + 32) ≤ a → a < 4294967296 →
        (a < RD ∨ (RD + 16) ≤ a) → (a < (F + 120) ∨ (F + 352) ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)) ∨
    ExhaustsG env cap pb p P 20626 ω μ x N

/-- `ElemOkAFC` is `ElemOkAFCG` for the refine contract (`refineHeap env`). -/
theorem ElemOkAFC_iff {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {F RD N : Nat} {enc : List UInt8} {Rep : List Chunk → List UInt8 → Memory → Prop} :
    ElemOkAFC env cap pb gl p P F RD N enc Rep ↔ ElemOkAFCG (refineHeap env) cap pb gl p P F RD N enc Rep :=
  Iff.rfl

/-- `ElemOkAFCG` gives `ElemOkAFG` for any representation its own implies, chunk by chunk. -/
theorem ElemOkAFCG.toAF {X : Type} {env : HeapHost X} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {F RD N : Nat} {enc : List UInt8} {Rep : List Chunk → List UInt8 → Memory → Prop}
    {Rep' : List UInt8 → Memory → Prop} (h : ElemOkAFCG env cap pb gl p P F RD N enc Rep)
    (hR : ∀ cs bs μ, Rep cs bs μ → Rep' bs μ) : ElemOkAFG env cap pb gl p P F RD N enc Rep' := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hg hc
  rcases h x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hg hc
    with ⟨ω', μ', s', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ⟨cs, hcs, hrep⟩, a12⟩ | ex
  · exact Or.inl ⟨ω', μ', s', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      ⟨cs, hcs, fun μ'' hag => hR _ _ _ (hrep μ'' hag)⟩, a12⟩
  · exact Or.inr ex

/-- `ElemOkAFCG.toAF` for the refine contract (`refineHeap env`). -/
theorem ElemOkAFC.toAF {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {F RD N : Nat} {enc : List UInt8} {Rep : List Chunk → List UInt8 → Memory → Prop}
    {Rep' : List UInt8 → Memory → Prop} (h : ElemOkAFC env cap pb gl p P F RD N enc Rep)
    (hR : ∀ cs bs μ, Rep cs bs μ → Rep' bs μ) : ElemOkAF env cap pb gl p P F RD N enc Rep' :=
  ElemOkAFCG.toAF (env := refineHeap env) (P := P) h hR

/-- **`DeleteItems` (5), `Export` (10) or `Imported` (19), as an element of the decode loop, with any
    n ≥ 1 items of any length, with the chunks holding the buffers** (GP v0.8.0 B.7): as
    `ElemsBig.vecvec_elem_big`, its slot `VecVecRepC` for the fresh allocated chunks `cs` it returns
    (the buffer's chunk, each non-empty item's chunk, the pointers distinct and below 2³¹). -/
theorem vecvec_elem_bigC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (tag h r1 r2 r3 W : Nat)
    (htag : (tag = 5 ∧ h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ W = 9223372036854775812) ∨
      (tag = 10 ∧ h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ W = 9223372036854775826))
    (es : List (List UInt8)) (hn : 1 ≤ es.length ∧ 24 * es.length < 1073741760)
    (hes : ∀ e ∈ es, e.length < 1073741760) :
    ElemOkAFC env cap pb gl p P F RD (9 * (encs es).flatten.length + 70300 * es.length + 41200)
      (UInt8.ofNat tag :: (Blob.encodeNat es.length ++ (encs es).flatten)) (VecVecRepC W es) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tagr rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat es.length).length = w := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L, (encs es).flatten.length = L := ⟨_, rfl⟩
  have hlen' : (UInt8.ofNat tag :: (Blob.encodeNat es.length ++ (encs es).flatten)).length - 1 = w + L := by
    simp [hW, hLd]
  simp only [hlen', List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tagr ⊢
  have hencw : μ.readN ptr w = Blob.encodeNat es.length := by
    have := readN_sub μ ptr (w + L) 0 w _ pay (by omega)
    simp only [Nat.add_zero] at this
    rw [this, List.drop_zero, List.take_left' hW]
  have hpd : μ.readN (ptr + w) L = (encs es).flatten := by
    rw [readN_sub μ ptr (w + L) w L _ pay (by omega), List.drop_left' hW]
    exact List.take_of_length_le (by omega)
  have hWb : W < 18446744073709551616 ∧ W ≠ 18446744073709551614 := by
    rcases htag with ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ | ⟨-, -, -, -, -, rfl⟩ <;> decide
  rcases VariantsBig.vecvec_heap_bigO (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len pb S0 S1 Fr tag h r1 r2 r3 W htag es h6 h7 tagr tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn hes ⟨by rw [hW, hLd]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW, hLd]; omega⟩ rP rL (by rw [hW]; exact hencw)
      (by rw [hW, hLd]; exact hpd) with
    ⟨s', ω', μ', q, cs, qs, run, -, -, g1, g5, g6, gO, gO8, gO16, gO24, gR0, gR8, H', keep, kd, hcs, hrep,
      gfr, glo, ggl, gwr, gco, gown, gne⟩ | ex
  · rw [hW, hLd] at gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0, Nat.add_assoc],
      by rw [gR8, Nat.sub_sub], ⟨W, hWb.1, gO, hWb.2⟩, H', keep, kd, ⟨cs, hcs, fun μ'' hag => ?_⟩,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    obtain ⟨co, hco, hcoa, hcoe⟩ := gco
    have hba : s'.base % 8 = 0 := by have := H'.wf.2.1; omega
    have hbT' := H'.hbT
    obtain ⟨hcom, hcou, -⟩ := hcs co hco
    have hcoT := (VecU8.chunk_in H'.wf hcom hcou).2.2
    refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, qs, co, ?_, ?_, ?_,
      fun j hj => hrep μ'' hag j hj, hco, hcou, hcoa, hcoe,
      fun j hj h0 => (gown.1 j hj (Nat.zero_le _) hj).1 h0, fun j hj hl => ?_, gne,
      fun j j' hj hj' hne hl hl' => gown.2 j j' hj hj' (Nat.zero_le _) hj (Nat.zero_le _) hj' hne hl hl',
      by omega, fun j hj => ?_⟩
    · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
    · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
    · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
    · obtain ⟨c, hc, hca, hce⟩ := (gown.1 j hj (Nat.zero_le _) hj).2 hl
      exact ⟨c, hc, (hcs c hc).2.1, fun e => gne j hj hl (by rw [← hca, e, hcoa]), hca, hce⟩
    · by_cases hl : es[j].length = 0
      · rw [(gown.1 j hj (Nat.zero_le _) hj).1 hl, hl]; decide
      · obtain ⟨c, hc, hca, hce⟩ := (gown.1 j hj (Nat.zero_le _) hj).2 hl
        have := (VecU8.chunk_in H'.wf (hcs c hc).1 (hcs c hc).2.1).2.2
        omega
  · exact Or.inr (ex.mono (by omega))

/-- **`Export` (tag 10, ExportSegs), with the chunks holding the buffers**: `vecvec_elem_bigC` at tag 10,
    the discriminant word 2⁶³ − 1 + 10 (as `Refine.LoopAll.ExportOk` reads it). -/
theorem export_elem_bigC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (es : List (List UInt8)) (hn : 1 ≤ es.length ∧ 24 * es.length < 1073741760)
    (hes : ∀ e ∈ es, e.length < 1073741760) :
    ElemOkAFC env cap pb gl p P F RD (9 * (encs es).flatten.length + 70300 * es.length + 41200)
      (UInt8.ofNat 10 :: (Blob.encodeNat es.length ++ (encs es).flatten))
      (VecVecRepC (9223372036854775807 + 10) es) :=
  vecvec_elem_bigC env cap pb hcap1 hcap gl F RD hL 10 21871 1010 1110 1112 _
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) es hn hes

end Services.Bootstrap.Decode.VecVecOwn
