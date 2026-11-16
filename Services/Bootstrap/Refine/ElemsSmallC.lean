import Services.Bootstrap.Refine.ElemsBigC
import Services.Bootstrap.Decode.BlessHeap
import Services.Bootstrap.Decode.RandomStorageOk
import Services.Bootstrap.Decode.DesignateHeap
import Services.Bootstrap.Decode.LookupProvideElem
import Services.Bootstrap.Decode.CreateServiceElem
import Services.Bootstrap.Decode.AssignGas
import Services.Bootstrap.Decode.Assign

/-!
# The decode loop's small heap elements, with the chunks holding their buffers

The small-size counterparts of `ElemsBigC` (GP v0.8.0 B.7): each `Decode` adapter for the sizes below the large readers'
limits restated as `VecVecOwn.ElemOkAFC`, the slot's buffer word naming the returned chunk that holds the buffer
(`ElemsBigC.OwnsBuf`). Each proof is the `Decode` adapter's, with that chunk named.
-/

namespace Services.Bootstrap.Refine.ElemsSmallC

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Services.Bootstrap.Decode Services.Bootstrap.Decode.VecVecOwn Services.Bootstrap.Refine.ElemsBigC

section
open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.U32Hash Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA
open Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
open Services.Bootstrap.Decode.Bless

/-- **`bless_elem` with its chunk**: `Bless.bless_elem`, the buffer (slot word 16) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem bless_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (m a d r : List UInt8) (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4)
    (hr4 : r.length = 4) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 1024) (items : List UInt8) (hi : items.length = 12 * n) :
    ElemOkAFC env cap pb gl p P F RD (260 * n + 2000) (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items))
      (fun cs bs μ => BlessRep m a d r n items bs μ ∧ OwnsBuf cs bs 16 (16 * n)) := by
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
      have hbT' := H'.hbT
      refine ⟨⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, ?_, ?_, ?_, ?_, q, ?_, ?_, ?_,
        fun j hj => ⟨?_, ?_⟩⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
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
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact gO16
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems
open Services.Bootstrap.Decode.RandomStorage

/-- **`random_storage_ok_elem` with its chunk**: `RandomStorage.random_storage_ok_elem`, the buffer (slot word 16) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem random_storage_ok_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 512) (hs : List UInt8) (hh : hs.length = 32 * n) :
    ElemOkAFC env cap pb gl p P F RD (550 * n + 2000) (22 :: 0 :: (Blob.encodeNat n ++ hs))
      (fun cs bs μ => RandomStorageOkRep n hs bs μ ∧ OwnsBuf cs bs 16 (32 * n)) := by
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
  rcases random_storage_ok_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H
      ⟨by unfold S0; omega, by unfold S1; omega⟩ ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩
      ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩ (Or.inl (by omega))
      ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hok (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, -, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
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
      have hbT' := H'.hbT
      refine ⟨⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, ?_, ?_, ?_, ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact gO16
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.Elems Services.Bootstrap.Decode.VecKey336
open Services.Bootstrap.Decode.Designate

/-- **`designate_elem` with its chunk**: `Designate.designate_elem`, the buffer (slot word 16) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem designate_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (C : Nat) (gv : (List.range 2).map (fun k => gl (196616 + k)) = Num.encodeLE 2 C)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 48) (hnC : n ≤ 3 * C % 65536) (ks : List UInt8) (hk : ks.length = 336 * n) :
    ElemOkAFC env cap pb gl p P F RD (8200 * n + 2000) (13 :: (Blob.encodeNat n ++ ks))
      (fun cs bs μ => DesignateRep n ks bs μ ∧ OwnsBuf cs bs 16 (336 * n)) := by
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
      have hbT' := H'.hbT
      refine ⟨⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, ?_, ?_, ?_, ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat, hitems]
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact gO16
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems
open Services.Bootstrap.Decode.LookupProvideElem

/-- **`looked_up_some_elem` with its chunk**: `LookupProvideElem.looked_up_some_elem`, the buffer (slot word 16) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem looked_up_some_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAFC env cap pb gl p P F RD (2 * n + 2000) (18 :: 1 :: (Blob.encodeNat n ++ bytes))
      (fun cs bs μ => LookedUpSomeRep n bytes bs μ ∧ OwnsBuf cs bs 16 (n)) := by
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
      have hbT' := H'.hbT
      refine ⟨⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, ?_, ?_, ?_, ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact gO16
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems
open Services.Bootstrap.Decode.LookupProvideElem

/-- **`provide_inline_elem` with its chunk**: `LookupProvideElem.provide_inline_elem`, the buffer (slot word 24) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem provide_inline_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (s : List UInt8) (hs : s.length = 4) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384)
    (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAFC env cap pb gl p P F RD (2 * n + 2300) (17 :: (s ++ 1 :: (Blob.encodeNat n ++ bytes)))
      (fun cs bs μ => ProvideInlineRep s n bytes bs μ ∧ OwnsBuf cs bs 24 (n)) := by
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
      have hbT' := H'.hbT
      refine ⟨⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, ?_, ?_, q, ?_, ?_, ?_, ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ' (F + 120) 232 8 1 _ rfl (by decide)]; simp [Memory.readN, gO8]
      · rw [← readN_sub μ' (F + 120) 232 48 4 _ rfl (by decide), gO48]; exact hs4
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [← readN_sub μ' (F + 120) 232 32 8 _ rfl (by decide)]; exact gO32
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact gO24
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Decode.Elems
open Services.Bootstrap.Decode.CreateServiceElem

/-- **`create_service_some_elem` with its chunk**: `CreateServiceElem.create_service_some_elem`, the buffer (slot word 8) a returned chunk holding its
    octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem create_service_some_elemC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (F RD : Nat) (hL : Lay F RD)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 16384) (bytes : List UInt8) (hb : bytes.length = n) :
    ElemOkAFC env cap pb gl p P F RD (2 * n + 5600)
      (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (fun cs bs μ => CreateServiceSomeRep n bytes h u1 u2 u3 u4 arr u5 ou bs μ ∧ OwnsBuf cs bs 8 (n)) := by
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
  rcases CreateService.create_service_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ st (F - 384)
      (F + 120) 18 723 v5 v6 RD ptr len n pb S0 S1 ou Fr g6 g7 tag tab rt H (by unfold S0; omega)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by unfold S1; omega⟩ hn hou
      ⟨by rw [hW]; omega, hl'⟩ ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL hsome henc
      (by rw [hW]; exact hpay) with
    ⟨q, s', ω', μ', ha, run, -, e1, e5, e6, eO, eO8, eO16, edat, e24, e28, e32, e64, e72, e80, e88, e96, e224,
      eR0, eR8, H', keep, hnew, hfresh, kd, efr, elo, egl, ewr⟩ | ⟨hna, ω', μ', run, f7⟩
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
      have hbT' := H'.hbT
      refine ⟨⟨⟨q, by rw [readN_take _ _ 232 8 (by decide)]; exact eO, ?_, ?_, ?_⟩,
        cs_fields μ' (F + 120) h u1 u2 u3 u4 arr u5 ou e24 e28 ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
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
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact eO8
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end

section
open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash
  Services.Bootstrap.Decode.Assign
open Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop
open Services.Bootstrap.Decode.AssignGas

/-- **`assign_gas_elemF` with its chunk**: `AssignGas.assign_gas_elemF`, the buffer (slot word 16) a returned chunk holding its
    32n octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem assign_gas_elemFC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (F RD : Nat) (hL : Lay F RD)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 512)
    (c hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n) (hg : g.length = 4) :
    ElemOkAFC env cap pb gl p P F RD (1500 + 550 * n) (24 :: (c ++ Blob.encodeNat n ++ hs ++ g))
      (fun cs bs μ => AssignGasRep c n hs g bs μ ∧ OwnsBuf cs bs 16 (32 * n)) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hgl
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hw15 := encodeNat_len_le5 n (by omega)
  rw [hW] at hw15
  have hLen : (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)).length = 7 + w + 32 * n := by
    simp [hc, hW, hh, hg]; omega
  simp only [hLen, show 7 + w + 32 * n - 1 = 2 + w + 32 * n + 4 by omega,
    List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have hst : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.writable a = true := H.st
  have ht0 := H.wf.2.2.2.1
  unfold TilesOk at ht0
  have htop0 : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcpm' := ht0.mem_lt cp hcp
  have hT0 := H.hbT
  have hb00 := H.hb0
  have hp31 : ptr + (2 + w + 32 * n + 4) < 2147483648 := by omega
  -- the payload's parts
  have hsplit : μ.readN ptr (2 + w + 32 * n + 4) = μ.readN ptr 2 ++ (μ.readN (ptr + 2) w ++
      (μ.readN (ptr + 2 + w) (32 * n) ++ μ.readN (ptr + 2 + w + 32 * n) 4)) := by
    rw [Memory.readN_split, Memory.readN_split, Memory.readN_split]
    simp only [Nat.add_assoc, List.append_assoc]
  rw [hsplit] at pay
  simp only [List.append_assoc] at pay
  obtain ⟨pc, pay1⟩ := List.append_inj pay (by simp [hc])
  obtain ⟨pe, pay2⟩ := List.append_inj pay1 (by simp [hW])
  obtain ⟨phs, pg⟩ := List.append_inj pay2 (by simp [hh])
  have hcv : Num.decodeLE c < 65536 := by have := decodeLE_lt c; rw [hc] at this; simpa using this
  have ec : Num.encodeLE 2 (Num.decodeLE c) = c := by have := encodeLE_decodeLE c; rwa [hc] at this
  have hgv : Num.decodeLE g < 4294967296 := by have := decodeLE_lt g; rw [hg] at this; simpa using this
  have eg : Num.encodeLE 4 (Num.decodeLE g) = g := by have := encodeLE_decodeLE g; rwa [hg] at this
  -- the dispatch and the handler's frame
  obtain ⟨ω1, run1, d0, d1, d5, d6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ
    F 24 (by omega) (by omega) h1 h7 (by simpa using tag) tab
    (Memory.readable_of_writable (hst _ (by omega) (by omega))) rt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    ag1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ F (F + 120) RD
      ⟨by omega, by omega⟩ (d1.trans h1) (d5.trans h5) (d6.trans h6) (by omega) (by omega)
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- the core, into S + 32
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1174 25390 (F - 80) RD
      (F - 48) ptr len 2 f0 f1 f7 f8 f9 (by omega) jte_586 bs_25390 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hl'
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact rpay a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rL)
  have low3 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha =>
    (gfr a (by omega) (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  -- the core parked, and the call of decodeU32
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k24, kfr, krd, kwr⟩ :=
    ag2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (F - 80) (F + 120) RD
      (Num.decodeLE c) ⟨by omega, by omega⟩ (g1.trans f1) (g5.trans f5) (g6.trans f6) g7
      (by omega) hcv
      (by rw [show F - 80 + 32 = F - 48 by omega, gbuf,
        Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), pc, ec])
      (fun a h1 h2 => by rw [gwr, fwr]; exact hst a (by omega) (by omega))
  have low4 : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a ha =>
    (kfr a (by omega) (Or.inl (by omega))).trans (low3 a ha)
  -- the length ℰ(n)
  obtain ⟨ω5, μ5, run5, ⟨e0, e1, -, -, -, e5, e6, -, e7, e8, eR0, eR8, efr, erd, ewr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 1176 25408 (F - 80) RD (ptr + 2)
      (len - 2) k0 k1 k7 (by decide) jte_587 bs_25408 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact wr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR8)
      n (by omega) (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd, frd]; exact rpay a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => low4 _ (by omega))]; exact pe)
  rw [hW] at eR0 eR8
  have low5 : ∀ a, a < 2147483648 → μ5.read a = μ.read a := fun a ha =>
    (efr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (low4 a ha)
  have H5 : HeapCtx env pb S0 S1 μ5 s := heap_of_high H low5 (fun a => by rw [ewr, kwr, gwr, fwr])
  -- the call of the hash-Vec decoder
  obtain ⟨ω6, run6, a0, a1, a5, a6, a7, a8, a9⟩ :=
    ag3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (F - 80) (F + 120) RD n (by omega)
      (by rw [e1, k1]) (by rw [e5, k5]) (by rw [e6, k6]) e7 e8 (by omega) (by omega)
  -- the queue: n hashes, into a fresh Vec at S + 32
  rcases VecHash.vec_hash (p := p) (P := P) env cap pb hcap1 hcap x ω6 μ5 s cp (F - 232) n RD (ptr + 2 + w)
      (len - 2 - w) (F - 48) 1178 25431 (F + 120) RD (fun k => μ.readN (ptr + 2 + w + 32 * k) 32) H5 a0
      (by rw [a1]; congr 1; omega) a5 a6 (by rw [a7]; congr 1; omega) a8 a9 hn
      ⟨by simp only [LoopA.S0]; omega, by omega, by omega⟩ (by simp only [LoopA.S1]; omega)
      ⟨by omega, by simp only [LoopA.S1]; omega⟩
      (Or.inr (by omega)) ⟨hcp, hcpu⟩
      (fun a h1 h2 => by unfold InData; omega)
      (fun k hk => Memory.readN_congr (fun j hj => low5 _ (by omega)))
      (by rw [show ptr + 2 + w = ptr + 2 + w from rfl]; exact eR0)
      (by rw [show len - 2 - w = len - 2 - w from rfl]; exact eR8)
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ jte_588 bs_25431 with
    ⟨q, s', ω7, μ7, ha, run7, v0, v1, v5', v6', vO, vO8, vO16, vel, vR0, vR8, H7, hnew, hfresh, keepU, keepD, vfr,
      vlow, vglob, vwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) ex).mono
      (by omega))
  -- the new chunk's place
  have ht7 := H7.wf.2.2.2.1
  unfold TilesOk at ht7
  have htop7 : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hqm := ht7.mem_lt _ hnew
  simp only at hqm
  have hT7 := H7.hbT
  have hb07 := H7.hb0
  have hq31 : 206896 ≤ q ∧ q + 32 * n < 2147483648 := by omega
  have hst7 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ7.writable a = true := H7.st
  -- the Vec copied, and the assigner's call
  obtain ⟨ω8, μ8, run8, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    ag4 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (F - 80) (F + 120) RD n q n
      ⟨by omega, by omega⟩ (by rw [v1]; congr 1; omega) v5' v6' (by omega) (by omega) (by omega)
      (by omega) (by rw [show F - 80 + 32 = F - 48 by omega]; exact vO)
      (by rw [show F - 80 + 40 = F - 48 + 8 by omega]; exact vO8)
      (by rw [show F - 80 + 48 = F - 48 + 16 by omega]; exact vO16)
      (fun a h1 h2 => hst7 a (by omega) (by omega))
  have pg8 : μ8.readN (ptr + 2 + w + 32 * n) 4 = g := by
    rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((keepD cp hcp hcpu _ ⟨by omega, by omega⟩).trans (low5 _ (by omega))))]
    exact pg
  obtain ⟨ω9, μ9, run9, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 1180 25470 (F - 80) RD
      (F - 48) (ptr + 2 + w + 32 * n) (len - 2 - w - 32 * n) 4 m0 m1 m7 (by rw [m8]; congr 1; omega) m9
      (by omega) jte_589 bs_25470
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [mrd]; exact Memory.readable_of_writable
          (heap_writable_data H7 (keepU cp hcp hcpu) hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR0)
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR8)
  -- the frame above S, from the start to before the store
  have up9 : ∀ a, (F - 24) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ9.read a = μ2.read a := fun a h0 h1 h3 =>
    (nfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))).trans
      ((mfr a h1 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((vfr a (by omega) h1 h3 (Or.inr (by omega))).trans
      ((efr a h1 (Or.inr (by omega)) h3).trans ((kfr a h1 (Or.inr (by omega))).trans
        (gfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega)))))))
  have up2 : ∀ a, F ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h0 h1 =>
    ffr a h1 (Or.inr h0)
  have sv : ∀ a v, a + 8 ≤ RD → F ≤ a → μ.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up9 _ (by omega) (by omega) (by omega)).trans
      (up2 _ (by omega) (by omega)))]; exact h
  have sH : ∀ a v, (F - 80) ≤ a → a + 8 ≤ (F - 56) → μ8.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))]
    exact h
  have sK4 : ∀ a v, (F - 56) ≤ a → a + 8 ≤ (F - 48) → μ4.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((mfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans ((vfr _ (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega))).trans (efr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))))))]
    exact h
  have sA : ∀ a v, (F - 24) ≤ a → a + 8 ≤ F → μ2.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up9 _ (by omega) (by omega) (by omega))]; exact h
  have hst9 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ9.writable a = true := fun a h1 h2 => by
    rw [nwr, mwr]; exact hst7 a h1 h2
  -- the variant, into the slot O, and the returns
  obtain ⟨ω10, μ10, run10, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    ag5 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 (F - 80) (F + 120) 18 723 v5 v6 RD
      n q n (Num.decodeLE g) (Num.decodeLE c) (by omega) (by omega) (Or.inr (by omega)) (n1.trans m1)
      (n5.trans m5) n7 hv5 hv6 (by omega) (by omega) (by omega) (by omega) (by omega) hgv hcv
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24)
      (by rw [show F - 80 + 32 = F - 48 by omega, nbuf, pg8, eg])
      (by rw [show F - 80 + 72 = F - 8 by omega]; exact sA _ _ (by omega) (by omega) f72)
      (by rw [show F - 80 + 64 = F - 16 by omega]; exact sA _ _ (by omega) (by omega) f64)
      (by rw [show F - 80 + 56 = F - 24 by omega]; exact sA _ _ (by omega) (by omega) f56)
      (by rw [show F - 80 + 128 = F + 48 by omega]; exact sv _ _ (by omega) (by omega) s0)
      (by rw [show F - 80 + 120 = F + 40 by omega]; exact sv _ _ (by omega) (by omega) s5)
      (by rw [show F - 80 + 112 = F + 32 by omega]; exact sv _ _ (by omega) (by omega) s6)
      ⟨by omega, by omega, by omega⟩ jte_8 bs_723
      (fun a h1 h2 => hst9 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst9 a (by omega) (by omega)))
  have low10 : ∀ a, a < 2147483648 → μ10.read a = μ7.read a := fun a ha =>
    (ofr a (by omega) (Or.inl (by omega))).trans ((nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))))
  refine Or.inl ⟨ω10, μ10, s', (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans (run8.trans (run9.trans run10))))))))).mono (by omega), (by rw [o1]; congr 1; omega), o5, o6, ?_, ?_,
    ⟨9223372036854775831, by omega, oO, by omega⟩,
    heap_of_high H7 low10 (fun a => by rw [owr, nwr, mwr]), keepU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR0]; congr 1; omega
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR8]; congr 1; omega
  · intro c' hc' hu a ha
    have hcm := ht0.mem_lt c' hc'
    have hd := ha
    unfold InData at hd
    rw [low10 a (by omega), keepD c' hc' hu a ha, low5 a (by omega)]
  · refine ⟨[⟨q - 32, n + 1, true⟩], fun c' hc' => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc'
      subst hc'
      exact ⟨hnew, rfl, hfresh⟩
    have hqm := VecU8.chunk_in H7.wf hnew rfl
    have hb' := H7.hb0
    have hbT' := H7.hbT
    simp only at hqm
    · refine ⟨⟨by rw [readN_take _ _ 232 8 (by omega)]; exact oO, ?_, ?_, q, ?_, ?_, ?_, ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ10 (F + 120) 232 32 4 _ rfl (by omega)]; rw [oO32, eg]
      · rw [← readN_sub μ10 (F + 120) 232 36 2 _ rfl (by omega)]; rw [oO36, ec]
      · rw [← readN_sub μ10 (F + 120) 232 8 8 _ rfl (by omega)]; exact oO8
      · rw [← readN_sub μ10 (F + 120) 232 16 8 _ rfl (by omega)]; exact oO16
      · rw [← readN_sub μ10 (F + 120) 232 24 8 _ rfl (by omega)]; exact oO24
      · rw [Memory.readN_congr (fun j hj => (hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩).trans (low10 _ (by omega))),
          readN_of_pieces μ μ7 q (ptr + 2 + w) n (fun k hk => vel k hk)]
        exact phs
      · rw [← readN_sub μ10 (F + 120) 232 16 8 _ rfl (by omega)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact oO16
  · intro a h0 h1 h2 h3
    rw [ofr a h1 (by omega), up9 a (by omega) h1 h2]; exact up2 a (by omega) h1
  · intro a ha
    rw [low10 a (by omega), (vlow a ha).1, low5 a (by omega)]
  · intro a ha
    rw [ord, nrd, mrd, (vlow a ha).2, erd, krd, grd, frd]
  · intro a ha
    have h' := ha; unfold Glob at h'
    rw [low10 a (by omega), vglob a ha, low5 a (by omega)]
  · intro a ha
    rw [owr, nwr, mwr, vwr a ha, ewr, kwr, gwr, fwr]
end

section
open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash
open Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop
open Services.Bootstrap.Decode.Assign

/-- **`assign_elemF` with its chunk**: `Assign.assign_elemF`, the buffer (slot word 16) a returned chunk holding its
    32n octets (`OwnsBuf`). GP v0.8.0 B.7. -/
theorem assign_elemFC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (F RD : Nat) (hL : Lay F RD)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (G : Nat)
    (hG : G < 18446744073709551616)
    (gv : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 G)
    (hn : 1 ≤ G % 4294967296 ∧ G % 4294967296 ≤ 512)
    (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * (G % 4294967296))
    (hw4 : w4.length = 4) :
    ElemOkAFC env cap pb gl p P F RD (1000 + 550 * (G % 4294967296)) (12 :: (c2 ++ hb ++ w4))
      (fun cs bs μ => AssignRep (G % 4294967296) c2 hb w4 bs μ ∧ OwnsBuf cs bs 16 (32 * (G % 4294967296))) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hg
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have hL : (12 :: (c2 ++ hb ++ w4)).length = 7 + 32 * (G % 4294967296) := by
    simp [hc2, hhb, hw4]; omega
  simp only [hL, show 7 + 32 * (G % 4294967296) - 1 = 2 + 32 * (G % 4294967296) + 4 by omega,
    List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  obtain ⟨n, hnG⟩ : ∃ n, n = G % 4294967296 := ⟨_, rfl⟩
  rw [← hnG] at hn hhb hl hp' pay rpay hcph ⊢
  have hst : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.writable a = true := H.st
  have ht0 := H.wf.2.2.2.1
  unfold TilesOk at ht0
  have htop0 : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcpm' := ht0.mem_lt cp hcp
  have hT0 := H.hbT
  have hb00 := H.hb0
  have hp31 : ptr + (2 + 32 * n + 4) < 2147483648 := by omega
  -- the payload's parts
  have hlist : c2 ++ hb ++ w4 = c2 ++ (hb ++ w4) := List.append_assoc _ _ _
  have pc2 : μ.readN ptr 2 = c2 := by
    have := readN_sub μ ptr (2 + 32 * n + 4) 0 2 _ pay (by omega)
    simp only [Nat.add_zero] at this
    rw [this]; simp [List.take_append, hc2]
  have phb : ∀ k, k < n → μ.readN (ptr + 2 + 32 * k) 32 = (hb.drop (32 * k)).take 32 := by
    intro k hk
    have := readN_sub μ ptr (2 + 32 * n + 4) (2 + 32 * k) 32 _ pay (by omega)
    rw [show ptr + 2 + 32 * k = ptr + (2 + 32 * k) by omega, this]
    simp [List.drop_append, List.take_append, hc2, hhb, List.drop_eq_nil_of_le]
    omega
  have pw4 : μ.readN (ptr + 2 + 32 * n) 4 = w4 := by
    have := readN_sub μ ptr (2 + 32 * n + 4) (2 + 32 * n) 4 _ pay (by omega)
    rw [show ptr + 2 + 32 * n = ptr + (2 + 32 * n) by omega, this]
    simp [List.drop_append, List.take_append, hc2, hhb, hw4, List.drop_eq_nil_of_le]
    exact List.take_of_length_le (by omega)
  have hc2v : Num.decodeLE c2 < 65536 := by have := decodeLE_lt c2; rw [hc2] at this; simpa using this
  have ec2 : Num.encodeLE 2 (Num.decodeLE c2) = c2 := by have := encodeLE_decodeLE c2; rwa [hc2] at this
  have hw4v : Num.decodeLE w4 < 4294967296 := by have := decodeLE_lt w4; rw [hw4] at this; simpa using this
  have ew4 : Num.encodeLE 4 (Num.decodeLE w4) = w4 := by have := encodeLE_decodeLE w4; rwa [hw4] at this
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, d0, d1, d5, d6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ
    F 12 (by omega) (by omega) h1 h7 (by simpa using tag) tab
    (Memory.readable_of_writable (hst _ (by omega) (by omega))) rt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f80, f72, f64, ffr, frd, fwr⟩ :=
    as1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ F (F + 120) RD
      ⟨by omega, by omega⟩ (d1.trans h1) (d5.trans h5) (d6.trans h6) (by omega) (by omega)
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- the core, into H + 40
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1152 24765 (F - 88) RD
      (F - 48) ptr len 2 f0 f1 f7 f8 f9 (by omega) jte_575 bs_24765 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hl'
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact rpay a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rL)
  have low3 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha =>
    (gfr a (by omega) (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  have hg3 : ∀ a, Glob a → μ3.read a = gl a := fun a ha => by
    have h' := ha; unfold Glob at h'; rw [low3 a (by omega)]; exact hg a ha
  have H3 : HeapCtx env pb S0 S1 μ3 s := heap_of_high H low3 (fun a => by rw [gwr, fwr])
  -- the global, and the call of the hash-Vec decoder
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, k32, k24, kfr, krd, kwr⟩ :=
    as2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (F - 88) (F + 120) RD
      (Num.decodeLE c2) G ⟨by omega, by omega⟩ (g1.trans f1) (g5.trans f5) (g6.trans f6) g7 (by omega)
      (by omega) hc2v (by rw [show F - 88 + 40 = F - 48 by omega, gbuf, Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), pc2, ec2])
      hG (glob_word gv hg3)
      (fun a h1 h2 => Memory.readable_of_writable (glob_writable H3 ⟨by omega, by omega⟩))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hst a (by omega) (by omega))
  have low4 : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a ha =>
    (kfr a (by omega) (Or.inl (by omega))).trans (low3 a ha)
  have H4 : HeapCtx env pb S0 S1 μ4 s := heap_of_high H3 (fun a ha => (kfr a (by omega) (Or.inl (by omega))))
    (fun a => by rw [kwr])
  have hcpm := hcp
  -- the queue: n hashes, into a fresh Vec at H + 40
  rcases VecHash.vec_hash (p := p) (P := P) env cap pb hcap1 hcap x ω4 μ4 s cp (F - 240) n RD (ptr + 2)
      (len - 2) (F - 48) 1154 24826 196680 RD (fun k => (hb.drop (32 * k)).take 32) H4 k0 (by rw [k1]; congr 1; omega) k5 k6 (by rw [k7]; congr 1; omega) k8
      (by rw [hnG]; exact k9) hn ⟨by simp only [LoopA.S0]; omega, by omega, by omega⟩ (by simp only [LoopA.S1]; omega)
      ⟨by omega, by simp only [LoopA.S1]; omega⟩
      (Or.inr (by omega)) ⟨hcp, hcpu⟩
      (fun a h1 h2 => by unfold InData; omega)
      (fun k hk => by
        rw [Memory.readN_congr (fun j hj => low4 _ (by omega)), show ptr + 2 + 32 * k = ptr + 2 + 32 * k from rfl]
        exact phb k hk)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR8)
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ jte_576 bs_24826 with
    ⟨q, s', ω5, μ5, ha, run5, v0, v1, v5', v6', vO, vO8, vO16, vel, vR0, vR8, H5, hnew, hfresh, keepU, keepD, vfr,
      vlow, vglob, vwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans (run2.trans (run3.trans run4))) ex).mono (by omega))
  -- the new chunk's place
  have ht5 := H5.wf.2.2.2.1
  unfold TilesOk at ht5
  have htop5 : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hqm := ht5.mem_lt _ hnew
  simp only at hqm
  have hT5 := H5.hbT
  have hb05 := H5.hb0
  have hq31 : 206896 ≤ q ∧ q + 32 * n < 2147483648 := by omega
  have hg4 : ∀ a, Glob a → μ4.read a = gl a := fun a ha => by
    have h' := ha; unfold Glob at h'; rw [low4 a (by omega)]; exact hg a ha
  have hg5 : ∀ a, Glob a → μ5.read a = gl a := fun a ha => (vglob a ha).trans (hg4 a ha)
  have hst5 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ5.writable a = true := H5.st
  -- the Vec copied, the global reloaded, and the assigner's call
  obtain ⟨ω6, μ6, run6, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    as3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (F - 88) RD n q n G
      ⟨by omega, by omega⟩ (by rw [v1]; congr 1; omega) v5' v6' (by omega) (by omega) (by omega) (by omega) (by rw [show F - 88 + 40 = F - 48 by omega]; exact vO)
      (by rw [show F - 88 + 48 = F - 48 + 8 by omega]; exact vO8) (by rw [show F - 88 + 56 = F - 48 + 16 by omega]; exact vO16) hG
      (glob_word gv hg5) (fun a h1 h2 => Memory.readable_of_writable (glob_writable H5 ⟨by omega, by omega⟩))
      (fun a h1 h2 => hst5 a (by omega) (by omega))
  have pw46 : μ6.readN (ptr + 2 + 32 * n) 4 = w4 := by
    rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((keepD cp hcp hcpu _ ⟨by omega, by omega⟩).trans (low4 _ (by omega))))]
    exact pw4
  obtain ⟨ω7, μ7, run7, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 1156 24867 (F - 88) RD
      (F - 48) (ptr + 2 + 32 * n) (len - 2 - 32 * n) 4 m0 m1 m7 (by rw [m8]; congr 1; omega) m9 (by omega) jte_577 bs_24867
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [mrd]; exact Memory.readable_of_writable
          (heap_writable_data H5 (keepU cp hcp hcpu) hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR0)
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR8)
  -- the frame above H, from the start to before the store
  have up7 : ∀ a, (F - 24) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ7.read a = μ2.read a := fun a h0 h1 h3 =>
    (nfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))).trans ((mfr a h1 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((vfr a (by omega) h1 h3 (Or.inr (by omega))).trans ((kfr a h1 (Or.inr (by omega))).trans
        (gfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))))))
  have up2 : ∀ a, F ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h0 h1 =>
    ffr a h1 (Or.inr h0)
  have sv : ∀ a v, a + 8 ≤ RD → F ≤ a → μ.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up7 _ (by omega) (by omega) (by omega)).trans
      (up2 _ (by omega) (by omega)))]; exact h
  have sH : ∀ a v, (F - 88) ≤ a → a + 8 ≤ (F - 48) → μ6.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))]
    exact h
  have sK4 : ∀ a v, (F - 88) + 24 ≤ a → a + 8 ≤ (F - 48) → μ4.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((mfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (vfr _ (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega)))))]
    exact h
  have sA : ∀ a v, (F - 88) + 64 ≤ a → a + 8 ≤ F → μ2.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up7 _ (by omega) (by omega) (by omega))]; exact h
  have hst7 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ7.writable a = true := fun a h1 h2 => by
    rw [nwr, mwr]; exact hst5 a h1 h2
  -- the variant, into the slot O, and the returns
  obtain ⟨ω8, μ8, run8, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    as4 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (F - 88) (F + 120) 18 723 v5 v6 RD
      n q n G (Num.decodeLE w4) (Num.decodeLE c2) (by omega) (by omega) (Or.inr (by omega)) (n1.trans m1)
      (n5.trans m5) n7 hG hv5 hv6 (by omega) (by omega) (by omega) (by omega) (by omega) hw4v hc2v
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24) (sK4 _ _ (by omega) (by omega) k32)
      (by rw [show F - 88 + 40 = F - 48 by omega, nbuf, pw46, ew4])
      (by rw [show F - 88 + 80 = F - 8 by omega]; exact sA _ _ (by omega) (by omega) f80)
      (by rw [show F - 88 + 72 = F - 16 by omega]; exact sA _ _ (by omega) (by omega) f72)
      (by rw [show F - 88 + 64 = F - 24 by omega]; exact sA _ _ (by omega) (by omega) f64)
      (by rw [show F - 88 + 136 = F + 48 by omega]; exact sv _ _ (by omega) (by omega) s0)
      (by rw [show F - 88 + 128 = F + 40 by omega]; exact sv _ _ (by omega) (by omega) s5)
      (by rw [show F - 88 + 120 = F + 32 by omega]; exact sv _ _ (by omega) (by omega) s6)
      ⟨by omega, by omega, by omega⟩ jte_8 bs_723
      (fun a h1 h2 => hst7 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst7 a (by omega) (by omega)))
  have low85 : ∀ a, a < 2147483648 → μ8.read a = μ5.read a := fun a ha =>
    (ofr a (by omega) (Or.inl (by omega))).trans ((nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))))
  refine Or.inl ⟨ω8, μ8, s', (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans run8))))))).mono (by omega), (by rw [o1]; congr 1; omega), o5, o6, ?_, ?_,
    ⟨9223372036854775819, by omega, oO, by omega⟩,
    heap_of_high H5 low85 (fun a => by rw [owr, nwr, mwr]), keepU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR0]; congr 1; omega
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR8]; congr 1; omega
  · intro c hc hu a ha
    have hcm := ht0.mem_lt c hc
    have hd := ha
    unfold InData at hd
    rw [low85 a (by omega), keepD c hc hu a ha, low4 a (by omega)]
  · refine ⟨[⟨q - 32, n + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    have hqm := VecU8.chunk_in H5.wf hnew rfl
    have hb' := H5.hb0
    have hbT' := H5.hbT
    simp only at hqm
    · refine ⟨⟨by rw [readN_take _ _ 232 8 (by omega)]; exact oO, q, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩, _, List.mem_singleton.mpr rfl, rfl, ?_, by simp only; omega, by simp only; omega⟩
      · rw [← readN_sub μ8 (F + 120) 232 8 8 _ rfl (by omega)]; exact oO8
      · rw [← readN_sub μ8 (F + 120) 232 16 8 _ rfl (by omega)]; exact oO16
      · rw [← readN_sub μ8 (F + 120) 232 24 8 _ rfl (by omega)]; rw [oO24, ← hnG, Nat.min_self]
      · rw [← readN_sub μ8 (F + 120) 232 32 4 _ rfl (by omega)]; rw [oO32, ew4]
      · rw [← readN_sub μ8 (F + 120) 232 36 2 _ rfl (by omega)]; rw [oO36, ec2]
      · rw [Memory.readN_congr (fun j hj => (hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩).trans (low85 _ (by omega)))]
        exact vel k hk
      · rw [← readN_sub μ8 (F + 120) 232 16 8 _ rfl (by omega)]; simp only
        rw [show q - 32 + 32 = q by omega]; exact oO16
  · intro a h0 h1 h2 h3
    rw [ofr a h1 (by omega), up7 a (by omega) h1 h2]; exact up2 a (by omega) h1
  · intro a ha
    rw [low85 a (by omega), (vlow a ha).1, low4 a (by omega)]
  · intro a ha
    rw [ord, nrd, mrd, (vlow a ha).2, krd, grd, frd]
  · intro a ha
    have h' := ha; unfold Glob at h'
    rw [low85 a (by omega), vglob a ha, low4 a (by omega)]
  · intro a ha
    rw [owr, nwr, mwr, vwr a ha, kwr, gwr, fwr]

end

end Services.Bootstrap.Refine.ElemsSmallC
