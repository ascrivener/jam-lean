import Services.Bootstrap.Decode.VariantsBig
import Services.Bootstrap.Decode.VariantsBig2
import Services.Bootstrap.Decode.ImportElem
import Services.Bootstrap.Decode.VecVecElem
import Services.Bootstrap.Decode.BlessHeap
import Services.Bootstrap.Decode.RandomStorageOk
import Services.Bootstrap.Decode.DesignateHeap
import Services.Bootstrap.Decode.AssignGas
import Services.Bootstrap.Decode.LookupProvideElem
import Services.Bootstrap.Decode.CreateServiceElem

/-!
# The decode loop's elements with the large readers

The `ElemOkAF` adapters (`LoopA`) of the variants carrying a vector, for the counts and lengths
beyond the small readers' limits (GP v0.8.0 B.7, the bootstrap service's instruction list): each
mirrors its small adapter line for line, with the variant-level composition of `VariantsBig` /
`VariantsBig2` in place of the small one, at any frame F with `Lay F RD` (so F ≥ S0 + 2048, which
covers every big composition's stack bound, the largest `designate_heap_big`'s S0 + 1648):

* `import_elem_big` (`Import`, n > 1024 items), `vecvec_elem_big` (`DeleteItems` / `Export` /
  `Imported`, 1 ≤ n with 24n < 2³⁰ − 64 items of any length below 2³⁰ − 64);
* `bless_elem_big` (n > 1024), `random_storage_ok_elem_big` (n > 512), `designate_elem_big` (n > 48),
  `assign_gas_elem_big` (n > 512);
* `looked_up_some_elem_big`, `provide_inline_elem_big`, `create_service_some_elem_big` (more than
  16384 octets).

The failure branch of each is `Exhausts`: a failed allocator call (`alloc` or `realloc`), which is
what the big compositions give.
-/

namespace Services.Bootstrap.Decode.ElemsBig

open Services.Bootstrap.CodeX

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.ImportElem

/-- **`Import`, as an element of the decode loop, with more than 1024 items** (GP v0.8.0 B.7, tag 9): as
    `ImportElem.import_elem`, for 1024 < n with 16n < 2³⁰ − 64, from `VariantsBig.import_heap_big`: the
    encoding [9] ++ ℰ(n) ++ items decodes to `ImportRep`, its items a fresh `Vec` in the heap; or an
    allocator call fails (`Exhausts`). -/
theorem import_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1024 < n ∧ 16 * n < 1073741760) (items : List UInt8) (hit : items.length = 16 * n) :
    ElemOkAF env cap pb gl p P F RD (268200 + VecPairs.pairSteps 1024 (n - 1024)) (9 :: (Blob.encodeNat n ++ items)) (ImportRep n items) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (9 :: (Blob.encodeNat n ++ items)).length - 1 = w + 16 * n := by simp [hW, hit]
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have henc : μ.readN ptr w = Blob.encodeNat n := by
    have := readN_sub μ ptr (w + 16 * n) 0 w _ pay (by omega)
    simp only [Nat.add_zero] at this
    rw [this, List.drop_zero, List.take_left' hW]
  have hitems : μ.readN (ptr + w) (16 * n) = items := by
    rw [readN_sub μ ptr (w + 16 * n) w (16 * n) _ pay (by omega), List.drop_left' hW]
    exact List.take_of_length_le (by omega)
  have Fr : Frame P F (F + 120) 18 723 v5 v6 ω μ :=
    ⟨by omega, by omega, Or.inr (by omega), h1, h5, hv5, hv6, s0, s5, s6, by decide, jte_8, bs_723,
      fun a h1 h2 => ws a (by omega) (by omega),
      fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega))⟩
  rcases VariantsBig.import_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H ⟨by unfold S0; omega, by unfold S1; omega⟩
      ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩ ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩
      (Or.inl (by omega)) ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, g0, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ex
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), by rw [g1]; try (congr 1; omega), g5, g6, by rw [gR0, Nat.add_assoc],
      by rw [gR8]; try (congr 1; omega), ⟨9223372036854775816, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (16 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
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
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.Bless Services.Bootstrap.Decode.U32Hash

/-- **`Bless`, as an element of the decode loop, with more than 1024 always-accumulate entries** (GP v0.8.0
    B.7, tag 11): as `Bless.bless_elem`, for 1024 < n with 16n < 2³⁰ − 64, from
    `VariantsBig2.bless_heap_big`: decodes to `BlessRep`, the pairs a fresh chunk of the heap; or an
    allocator call fails (`Exhausts`). -/
theorem bless_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (m a d r : List UInt8) (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4)
    (hr4 : r.length = 4) (n : Nat) (hn : 1024 < n ∧ 16 * n < 1073741760) (items : List UInt8) (hi : items.length = 12 * n) :
    ElemOkAF env cap pb gl p P F RD (268200 + VecPairs.pairSteps 1024 (n - 1024)) (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items))
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
  rcases VariantsBig2.bless_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ st F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gO32, gO36, gO40, gO44, gdat, gR0, gR8, H',
      keep, hnew, hfresh, kd, -, gfr, glo, ggl, gwr⟩ | ex
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
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.RandomStorage

/-- **`RandomStorageAccumulate(Ok(v))`, as an element of the decode loop, with more than 512 hashes** (GP
    v0.8.0 B.7, tag 22): as `RandomStorage.random_storage_ok_elem`, for 512 < n with 32n < 2³⁰ − 64,
    from `VariantsBig2.random_storage_ok_heap_big`: decodes to `RandomStorageOkRep`, the hashes a fresh
    chunk of the heap; or an allocator call fails (`Exhausts`). -/
theorem random_storage_ok_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 512 < n ∧ 32 * n < 1073741760) (hs : List UInt8) (hh : hs.length = 32 * n) :
    ElemOkAF env cap pb gl p P F RD (268300 + VecHash32.hashSteps 512 (n - 512)) (22 :: 0 :: (Blob.encodeNat n ++ hs))
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
  rcases VariantsBig2.random_storage_ok_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hok (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ex
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
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.Designate Services.Bootstrap.Decode.VecKey336

/-- **`Designate { keys }`, as an element of the decode loop, with more than 48 keys** (GP v0.8.0 B.7,
    tag 13): as `Designate.designate_elem`, for 48 < n ≤ (3·𝖢) mod 2^16 with 336n < 2³⁰ − 64, from
    `VariantsBig2.designate_heap_big` (its stack bound S0 + 1648 ≤ F within `Lay`'s S0 + 2048):
    decodes to `DesignateRep`, the keys a fresh chunk of the heap; or an allocator call fails
    (`Exhausts`). -/
theorem designate_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (C : Nat) (gv : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 C)
    (n : Nat) (hn : 48 < n ∧ 336 * n < 1073741760) (hnC : n ≤ 3 * C % 65536) (ks : List UInt8) (hk : ks.length = 336 * n) :
    ElemOkAF env cap pb gl p P F RD (396000 + VecKey336.keySteps 48 (n - 48)) (13 :: (Blob.encodeNat n ++ ks))
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
  rcases VariantsBig2.designate_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n C pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt (glob_core gv hg) hnC H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ex
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
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.LookupProvideElem

/-- **`LookedUp { data: Some(bytes) }`, as an element of the decode loop, with more than 16384 octets**
    (GP v0.8.0 B.7, tag 18): as `LookupProvideElem.looked_up_some_elem`, for 16384 < n = |bytes| <
    2³⁰ − 64, from `VariantsBig2.looked_up_heap_big`: decodes to `LookedUpSomeRep`, the octets a fresh
    chunk of the heap; or an allocator call fails (`Exhausts`). -/
theorem looked_up_some_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 16384 < n ∧ n < 1073741760) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (34800 + VecU8.loopSteps 16384 (n - 16384)) (18 :: 1 :: (Blob.encodeNat n ++ bytes))
      (LookedUpSomeRep n bytes) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (18 :: 1 :: (Blob.encodeNat n ++ bytes)).length - 1 = 1 + w + n := by simp [hW, hb]; omega
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have hsome : μ.read ptr = 1 := by
    have := readN_sub μ ptr (1 + w + n) 0 1 _ pay (by omega)
    simpa [Memory.readN] using this
  have henc : μ.readN (ptr + 1) w = Blob.encodeNat n := by
    rw [readN_sub μ ptr (1 + w + n) 1 w _ pay (by omega), List.drop_succ_cons, List.drop_zero,
      List.take_left' hW]
  have hitems : μ.readN (ptr + 1 + w) n = bytes := by
    have := readN_sub μ ptr (1 + w + n) (w + 1) n _ pay (by omega)
    rw [List.drop_succ_cons, List.drop_left' hW, List.take_of_length_le (by omega)] at this
    rw [show ptr + 1 + w = ptr + (w + 1) by omega]
    exact this
  rcases VariantsBig2.looked_up_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hsome (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ex
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1 <;> omega,
      by rw [gR8]; congr 1 <;> omega, ⟨9223372036854775825, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
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
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.LookupProvideElem

/-- **`Provide { service, preimage: Inline(bytes) }`, as an element of the decode loop, with more than
    16384 octets** (GP v0.8.0 B.7, tag 17): as `LookupProvideElem.provide_inline_elem`, for 16384 < n =
    |bytes| < 2³⁰ − 64, from `VariantsBig2.provide_inline_heap_big`: decodes to `ProvideInlineRep`, the
    octets a fresh chunk of the heap; or an allocator call fails (`Exhausts`). -/
theorem provide_inline_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (s : List UInt8) (hs : s.length = 4) (n : Nat) (hn : 16384 < n ∧ n < 1073741760)
    (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (35100 + VecU8.loopSteps 16384 (n - 16384)) (17 :: (s ++ 1 :: (Blob.encodeNat n ++ bytes)))
      (ProvideInlineRep s n bytes) := by
  intro x ω μ ptr len v5 v6 st h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hL : (17 :: (s ++ 1 :: (Blob.encodeNat n ++ bytes))).length - 1 = 5 + w + n := by
    simp [hW, hb, hs]; omega
  simp only [hL, List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have pay' : μ.readN ptr (5 + w + n) = (s ++ [1] ++ Blob.encodeNat n) ++ bytes := by rw [pay]; simp
  have hl5 : (s ++ [1]).length = 5 := by simp [hs]
  have hl5w : (s ++ [1] ++ Blob.encodeNat n).length = 5 + w := by simp [hs, hW]; omega
  have hs4 : μ.readN ptr 4 = s := by
    rw [← readN_take _ _ (5 + w + n) 4 (by omega), pay, List.take_left' hs]
  have hinl : μ.read (ptr + 4) = 1 := by
    have := readN_sub μ ptr (5 + w + n) 4 1 _ pay (by omega)
    rw [List.drop_left' hs] at this
    simpa [Memory.readN] using this
  have henc : μ.readN (ptr + 5) w = Blob.encodeNat n := by
    have pay5 : μ.readN ptr (5 + w + n) = (s ++ [1]) ++ (Blob.encodeNat n ++ bytes) := by rw [pay]; simp
    rw [readN_sub μ ptr (5 + w + n) 5 w _ pay5 (by omega), List.drop_left' hl5, List.take_left' hW]
  have hitems : μ.readN (ptr + 5 + w) n = bytes := by
    rw [Nat.add_assoc, readN_sub μ ptr (5 + w + n) (5 + w) n _ pay' (by omega), List.drop_left' hl5w]
    exact List.take_of_length_le (by omega)
  rcases VariantsBig2.provide_inline_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ st F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hinl (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gO32, gO48, gdat, gR0, gR8, H', keep, hnew,
      hfresh, kd, -, gfr, glo, ggl, gwr⟩ | ex
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1 <;> omega,
      by rw [gR8]; congr 1 <;> omega, ⟨9223372036854775824, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, ?_, ?_, q, ?_, ?_, ?_, ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 8 1 _ rfl (by decide)]; simp [Memory.readN, gO8]
      · rw [← readN_sub μ' (F + 120) 232 48 4 _ rfl (by decide), gO48]; exact hs4
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [← readN_sub μ' (F + 120) 232 32 8 _ rfl (by decide)]; exact gO32
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
  Services.Bootstrap.Decode.CreateServiceElem

/-- **`CreateService` with `Some(bytes)`, as an element of the decode loop, with more than 16384 octets**
    (GP v0.8.0 B.7, tag 0): as `CreateServiceElem.create_service_some_elem`, for 16384 < n = |bytes| <
    2³⁰ − 64, from `VariantsBig2.create_service_heap_big`: decodes to `CreateServiceSomeRep`, the octets
    a fresh chunk of the heap; or an allocator call fails (`Exhausts`). -/
theorem create_service_some_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) (n : Nat) (hn : 16384 < n ∧ n < 1073741760) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (38400 + VecU8.loopSteps 16384 (n - 16384))
      (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CreateServiceSomeRep n bytes h u1 u2 u3 u4 arr u5 ou) := by
  intro x ω μ ptr len v5 v6 st g1 g5 g6 g7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 g1 g5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  have hol := hou.length
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, ou.length = k := ⟨_, rfl⟩
  have hL0 : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou)).length - 1
      = 201 + w + n + k := by
    simp [hh, h1, h2, h3, h4, harr, h5, hk, hW, hb]; omega
  simp only [hL0, List.headD_cons, List.tail_cons] at tag hl hp' pay rpay hcph ⊢
  have sub : ∀ i m, i + m ≤ 201 + w + n + k → μ.readN (ptr + i) m =
      ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou).drop i).take m :=
    fun i m him => readN_sub μ ptr (201 + w + n + k) i m _ pay him
  have hF : F = (F - 384) + 384 := by omega
  rw [hF] at Fr tag
  rw [show F - 384 + 384 + 120 = F + 120 by omega] at Fr
  have hsome : μ.read (ptr + 192) = 1 := by
    have e := sub 192 1 (by omega)
    have : ((h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou).drop 192).take 1
        = [1] := by cs_pieces
    rw [this] at e
    simpa [Memory.readN] using e
  have henc : μ.readN (ptr + 193) (Blob.encodeNat n).length = Blob.encodeNat n := by
    rw [sub 193 _ (by omega)]
    rw [show h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou =
      (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1]) ++ Blob.encodeNat n ++ (bytes ++ u5 ++ ou) by simp]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr]) rfl
  have hitems : μ.readN (ptr + 193 + w) n = bytes := by
    rw [show ptr + 193 + w = ptr + (193 + w) by omega, sub (193 + w) n (by omega)]
    rw [show h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou =
      (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1] ++ Blob.encodeNat n) ++ bytes ++ (u5 ++ ou) by simp]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW]; omega) hb
  have hu5 : μ.readN (ptr + 193 + w + n) 8 = u5 := by
    rw [show ptr + 193 + w + n = ptr + (193 + w + n) by omega, sub (193 + w + n) 8 (by omega)]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW, hb]; omega) h5
  have hpay : μ.readN (ptr + 201 + w + n) ou.length = ou := by
    rw [show ptr + 201 + w + n = ptr + (201 + w + n) by omega, sub (201 + w + n) ou.length (by omega)]
    rw [← List.append_nil (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou)]
    exact piece _ _ _ _ _ (by simp [hh, h1, h2, h3, h4, harr, hW, hb, h5]; omega) rfl
  rcases VariantsBig2.create_service_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ st (F - 384)
      (F + 120) 18 723 v5 v6 RD ptr len n pb S0 S1 ou Fr g6 g7 tag tab rt H (by unfold S0; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by unfold S1; omega⟩ hn hou
      ⟨by rw [hW]; omega, hl'⟩ ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hsome henc
      (by rw [hW]; exact hpay) with
    ⟨q, s', ω', μ', run, -, e1, e5, e6, eO, eO8, eO16, edat, e24, e28, e32, e64, e72, e80, e88, e96, e224,
      eR0, eR8, H', keep, hnew, hfresh, kd, efr, elo, egl, ewr⟩ | ex
  · rw [hW] at edat eR0 eR8 e224
    refine Or.inl ⟨ω', μ', s', run, by rw [e1]; congr 1; omega, e5, e6, by rw [eR0]; congr 1; omega,
      by rw [eR8]; congr 1; omega, ⟨n, by omega, eO, by omega⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => efr a h1 (by omega) h2 (by omega), fun a ha => (elo a ha).1,
      fun a ha => (elo a ha).2, egl, fun a ha => ewr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨⟨q, by rw [readN_take _ _ 232 8 (by decide)]; exact eO, ?_, ?_, ?_⟩,
        cs_fields μ' (F + 120) h u1 u2 u3 u4 arr u5 ou e24 e28 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact eO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact eO16
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), edat]
        exact hitems
      · rw [e32, show ptr = ptr + 0 by rfl, sub 0 32 (by omega)]; cs_pieces
      · rw [e64, sub 32 8 (by omega)]; cs_pieces
      · rw [e72, sub 40 8 (by omega)]; cs_pieces
      · rw [e80, sub 48 8 (by omega)]; cs_pieces
      · rw [e88, sub 56 8 (by omega)]; cs_pieces
      · rw [e96, sub 64 128 (by omega)]; cs_pieces
      · rw [e224]; exact hu5
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.VecVecElem
  Services.Bootstrap.Decode.VecVecU8

/-- **`DeleteItems` (5), `Export` (10) or `Imported` (19), as an element of the decode loop, with any
    n ≥ 1 items of any length** (GP v0.8.0 B.7): as `VecVecElem.vecvec_elem`, for 1 ≤ n = |es| with
    24n < 2³⁰ − 64 and every item shorter than 2³⁰ − 64 octets, from `VariantsBig.vecvec_heap_big`:
    the encoding [tag] ++ ℰ(n) ++ the items' encodings decodes to `VecVecRep`, the items in fresh
    chunks of the heap; or an allocator call fails (`Exhausts`). -/
theorem vecvec_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (tag h r1 r2 r3 W : Nat)
    (htag : (tag = 5 ∧ h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ W = 9223372036854775812) ∨
      (tag = 10 ∧ h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ W = 9223372036854775826))
    (es : List (List UInt8)) (hn : 1 ≤ es.length ∧ 24 * es.length < 1073741760)
    (hes : ∀ e ∈ es, e.length < 1073741760) :
    ElemOkAF env cap pb gl p P F RD (9 * (encs es).flatten.length + 70300 * es.length + 41200)
      (UInt8.ofNat tag :: (Blob.encodeNat es.length ++ (encs es).flatten)) (VecVecRep W es) := by
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
  rcases VariantsBig.vecvec_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len pb S0 S1 Fr tag h r1 r2 r3 W htag es h6 h7 tagr tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn hes ⟨by rw [hW, hLd]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW, hLd]; omega⟩ rP rL (by rw [hW]; exact hencw)
      (by rw [hW, hLd]; exact hpd) with
    ⟨s', ω', μ', q, cs, qs, run, -, -, g1, g5, g6, gO, gO8, gO16, gO24, gR0, gR8, H', keep, kd, hcs, hrep,
      gfr, glo, ggl, gwr⟩ | ex
  · rw [hW, hLd] at gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0, Nat.add_assoc],
      by rw [gR8, Nat.sub_sub], ⟨W, hWb.1, gO, hWb.2⟩, H', keep, kd, ⟨cs, hcs, fun μ'' hag => ?_⟩,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, qs, ?_, ?_, ?_, fun j hj => hrep μ'' hag j hj⟩
    · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
    · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
    · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
  · exact Or.inr (ex.mono (by omega))

end

section

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.U32Hash
  Services.Bootstrap.Decode.AssignGas

/-- **`AssignForGasCost`, as an element of the decode loop, with more than 512 hashes** (GP v0.8.0 B.7,
    tag 24): as `AssignGas.assign_gas_elemF`, for 512 < n with 32n < 2³⁰ − 64, from
    `VariantsBig2.assign_gas_heap_big`: the encoding 24 :: (c ++ ℰ(n) ++ hs ++ g) decodes to
    `AssignGasRep`, the queue a fresh `Vec` in the heap; or an allocator call fails (`Exhausts`). -/
theorem assign_gas_elem_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap pb : Nat) (F RD : Nat) (hL : Lay F RD)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (n : Nat) (hn : 512 < n ∧ 32 * n < 1073741760)
    (c hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n) (hg : g.length = 4) :
    ElemOkAF env cap pb gl p P F RD (267800 + VecHash.hashSteps 512 (n - 512))
      (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)) (AssignGasRep c n hs g) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have Fr := loopFrame (p := p) (P := P) F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hLen : (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)).length = 7 + w + 32 * n := by
    simp [hc, hW, hh, hg]; omega
  simp only [hLen, show 7 + w + 32 * n - 1 = 2 + w + 32 * n + 4 by omega,
    List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have hsplit : μ.readN ptr (2 + w + 32 * n + 4) = μ.readN ptr 2 ++ (μ.readN (ptr + 2) w ++
      (μ.readN (ptr + 2 + w) (32 * n) ++ μ.readN (ptr + 2 + w + 32 * n) 4)) := by
    rw [Memory.readN_split, Memory.readN_split, Memory.readN_split]
    simp only [Nat.add_assoc, List.append_assoc]
  rw [hsplit] at pay
  simp only [List.append_assoc] at pay
  obtain ⟨pc, pay1⟩ := List.append_inj pay (by simp [hc])
  obtain ⟨pe, pay2⟩ := List.append_inj pay1 (by simp [hW])
  obtain ⟨phs, pg⟩ := List.append_inj pay2 (by simp [hh])
  rcases VariantsBig2.assign_gas_heap_big (p := p) (P := P) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact pe) with
    ⟨q, s', ω', μ', run, -, g1, g5, g6, gO, gO8, gO16, gO24, gO32, gO36, gdat, gR0, gR8, H', keep, hnew, hfresh,
      kd, -, gfr, glo, ggl, gwr⟩ | ex
  · rw [hW] at gdat gR0 gR8 gO32
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), g1, g5, g6, by rw [gR0]; congr 1; omega,
      by rw [gR8]; congr 1; omega, ⟨9223372036854775831, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (32 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      have hb' := H'.hb0
      simp only at hqm
      refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, ?_, ?_, q, ?_, ?_, ?_, ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 32 4 _ rfl (by decide), gO32]; exact pg
      · rw [← readN_sub μ' (F + 120) 232 36 2 _ rfl (by decide), gO36]; exact pc
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact phs
  · exact Or.inr (ex.mono (by omega))

end

end Services.Bootstrap.Decode.ElemsBig
