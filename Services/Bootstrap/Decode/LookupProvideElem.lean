import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Decode.LookedUpHeap
import Services.Bootstrap.Decode.ProvideInlineHeap

/-!
# `LookedUp` and `Provide`, as elements of the decode loop

The four shapes of `LookedUp { data }` (tag 18) and `Provide { service, preimage }` (tag 17) (GP v0.8.0
B.7, the bootstrap service's instruction list), stated at the decode loop's frame base F (the tag at F,
the slot at F + 120, the reader at RD, laid out as `Lay F RD`):

* `looked_up_noneF`, `provide_hashF`: the fixed-size shapes (`data: None`, `preimage: Hash(h)`), as
  `ElemOkF`s, from `LookedUp.looked_up_none` and `Provide.provide_hash`;
* `looked_up_some_elem`, `provide_inline_elem`: the shapes carrying a `Vec<u8>` of 1 … 16384 octets
  (`data: Some(bytes)`, `preimage: Inline(bytes)`), as `ElemOkAF`s, from `LookedUp.looked_up_heap` and
  `Provide.provide_inline_heap`: the octets land in a fresh chunk of the heap, or the `alloc` fails.
-/

namespace Services.Bootstrap.Decode.LookupProvideElem

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## The fixed-size shapes -/

/-- **`LookedUp { data: None }`** (tag 18): the encoding [18, 0] decodes to a slot holding the
    discriminant 2^63 + 17 and then the `None` niche, the word 2^64 − 1. -/
theorem looked_up_noneF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD) :
    ElemOkF p P F RD [18, 0] (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
      (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_one_sub_one, List.headD_cons,
    List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have hnone : μ.read ptr = 0 := by simpa [Memory.readN] using pay
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eR0, eR8, efr, erd, ewr⟩ := LookedUp.looked_up_none (p := p)
    (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) (by omega) h6 h7 tag tab rt ⟨by omega, by omega⟩
    ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ rP rL hnone (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (Or.inl (by omega)) (by omega) (fun a h1 h2 => ws a (by omega) (by omega)) wr
    (fun a h1 h2 => ws a (by omega) (by omega)) (rpay ptr (Nat.le_refl _) (by omega))
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775825, by decide, eO, by decide⟩,
    ?_, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 8 (by omega)
  exact ⟨t8.trans eO, d8.trans eO8⟩

/-- **`Provide { service, preimage: Hash(h) }`** (tag 17): the encoding 17 :: s ++ 0 :: h, with s the 4
    octets of the service and h the 32 of the hash, decodes to a slot holding the discriminant
    2^63 + 16, the `Hash` tag 0 at 8, h at 9 and s at 48. -/
theorem provide_hashF {p : ByteArray} {P : Program} [HasCode p P] (F RD : Nat) (hL : Lay F RD)
    (s h : List UInt8) (hs : s.length = 4) (hh : h.length = 32) :
    ElemOkF p P F RD (17 :: (s ++ 0 :: h)) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧
      (bs.drop 8).take 1 = [0] ∧ (bs.drop 9).take 32 = h ∧ (bs.drop 48).take 4 = s) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro X R x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hlen hlen' hptr hpb pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr
  simp only [List.length_cons, List.length_append, hs, hh, Nat.reduceAdd, Nat.add_one_sub_one,
    List.headD_cons, List.tail_cons] at tag hlen hptr hpb pay rpay ⊢
  have pay' : μ.readN ptr 37 = (s ++ [0]) ++ h := by rw [pay]; simp
  have hl5 : (s ++ [0]).length = 5 := by simp [hs]
  have hs4 : μ.readN ptr 4 = s := by
    rw [← readN_take _ _ 37 4 (by omega), pay, List.take_left' hs]
  have hhash : μ.read (ptr + 4) = 0 := by
    have := readN_sub μ ptr 37 4 1 _ pay (by omega)
    rw [List.drop_left' hs] at this
    simpa [Memory.readN] using this
  have hh' : μ.readN (ptr + 5) 32 = h := by
    rw [readN_sub μ ptr 37 5 32 _ pay' (by omega), List.drop_left' hl5]
    exact List.take_of_length_le (by omega)
  obtain ⟨ω', μ', run, -, e1, e5, e6, eO, eO8, eO9, eO48, eR0, eR8, efr, erd, ewr⟩ := Provide.provide_hash
    (p := p) (P := P) (R := R) x ω μ F (F + 120) 18 723 v5 v6 RD ptr len
    (loopFrame F RD hL ω μ v5 v6 h1 h5 s0 s5 s6 hv5 hv6 ws) ⟨by omega, l2⟩ h6 h7 tag tab rt
    ⟨by omega, by omega⟩ ⟨hptr, by omega⟩ ⟨hlen, hlen'⟩ hhash rP rL (Or.inr (by omega)) (Or.inl (by omega))
    (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
    (fun a h1 h2 => ws a (by omega) (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega)) rpay
  refine ⟨ω', μ', run.mono (by omega), e1, e5, e6, eR0, eR8, ⟨9223372036854775824, by decide, eO, by decide⟩,
    ?_, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 (by omega), erd, ewr⟩
  obtain ⟨t8, d8⟩ := slot_parts μ' (F + 120) 8 1 (by omega)
  obtain ⟨-, d9⟩ := slot_parts μ' (F + 120) 9 32 (by omega)
  obtain ⟨-, d48⟩ := slot_parts μ' (F + 120) 48 4 (by omega)
  refine ⟨t8.trans eO, d8.trans (by simp [Memory.readN, eO8]), d9.trans (eO9.trans hh'),
    d48.trans (eO48.trans hs4)⟩

/-! ## The shapes with a `Vec<u8>` in the heap -/

/-- **`LookedUp { data: Some(bytes) }`'s slot**: the discriminant word 2^63 + 17, then the `Vec`
    `{cap n, ptr q, len n}` for some q whose n octets are `bytes` (in the heap μ). -/
def LookedUpSomeRep (n : Nat) (bytes : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes

/-- **`LookedUp { data: Some(bytes) }`, as an element of the decode loop** (tag 18): the encoding
    18 :: 1 :: ℰ(n) ++ bytes, with 1 ≤ n = |bytes| ≤ 16384, decodes to `LookedUpSomeRep`, the octets a
    fresh chunk of the heap; or the `alloc` fails. -/
theorem looked_up_some_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (2 * n + 2000) (18 :: 1 :: (Blob.encodeNat n ++ bytes))
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
  rcases LookedUp.looked_up_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hsome (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
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
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

/-- **`Provide { service, preimage: Inline(bytes) }`'s slot**: the discriminant word 2^63 + 16, the
    `Inline` tag 1 at 8, the service's 4 octets s at 48, and the `Vec` `{cap n, ptr q, len n}` at 16 for
    some q whose n octets are `bytes` (in the heap μ). -/
def ProvideInlineRep (s : List UInt8) (n : Nat) (bytes : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧ (bs.drop 8).take 1 = [1] ∧ (bs.drop 48).take 4 = s ∧
  ∃ q, (bs.drop 16).take 8 = Num.encodeLE 8 n ∧ (bs.drop 24).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 32).take 8 = Num.encodeLE 8 n ∧ μ.readN q n = bytes

/-- **`Provide { service, preimage: Inline(bytes) }`, as an element of the decode loop** (tag 17): the
    encoding 17 :: s ++ 1 :: ℰ(n) ++ bytes, with s the 4 octets of the service and 1 ≤ n = |bytes| ≤
    16384, decodes to `ProvideInlineRep`, the octets a fresh chunk of the heap; or the `alloc` fails. -/
theorem provide_inline_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (s : List UInt8) (hs : s.length = 4) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384)
    (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAF env cap pb gl p P F RD (2 * n + 2300) (17 :: (s ++ 1 :: (Blob.encodeNat n ++ bytes)))
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
  rcases Provide.provide_inline_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ st F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hinl (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gO32, gO48, gdat, gR0, gR8, H', keep, hnew,
      hfresh, kd, -, gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
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
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end Services.Bootstrap.Decode.LookupProvideElem
