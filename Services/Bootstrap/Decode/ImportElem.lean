import Services.Bootstrap.Decode.VecPairs
import Services.Bootstrap.Decode.LoopA

/-!
# `Import`, as an element of the decode loop

`Import { items: Vec<(u64, u64)> }` (tag 9; GP v0.8.0 B.7, the bootstrap service's instruction list)
with 1 … 1024 items, stated as an `ElemOkAF`: from the decode loop's frame at F (the tag at F, the
slot at F + 120, the reader at RD, laid out as `Lay F RD`), `Instruction::decode` returns `Import`
into the slot (`ImportRep`), its items a fresh `Vec` in the heap; or the `alloc` fails. This is
`VecPairs.import_heap` at the loop's addresses.
-/

namespace Services.Bootstrap.Decode.ImportElem

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Import`'s slot**: the discriminant word 2^63 + 8, then the items, a `Vec` of capacity and
    length n at some q whose 16n octets (n pairs of little-endian `u64`s) are `items` (in the heap μ). -/
def ImportRep (n : Nat) (items : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775816 ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (16 * n) = items

/-- **`Import`, as an element of the decode loop** (tag 9): the encoding [9] ++ ℰ(n) ++ items, with
    1 ≤ n ≤ 1024 and `items` 16n octets, decodes to `Import`'s slot (`ImportRep`), its items a fresh
    `Vec` in the heap; or the `alloc` fails. -/
theorem import_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (F RD : Nat)
    (hL : Lay F RD) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 1024) (items : List UInt8) (hit : items.length = 16 * n) :
    ElemOkAF env cap pb gl p P F RD (260 * n + 2000) (9 :: (Blob.encodeNat n ++ items)) (ImportRep n items) := by
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
  rcases VecPairs.import_heap (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω μ s F (F + 120) 18 723
      v5 v6 RD ptr len n pb S0 S1 Fr h6 h7 (by simpa using tag) tab rt H ⟨by unfold S0; omega, by unfold S1; omega⟩
      ⟨by omega, l2⟩ hn ⟨by rw [hW]; omega, hl'⟩ ⟨by omega, by unfold S1; omega⟩ ⟨by omega, by unfold S1; omega⟩
      (Or.inl (by omega)) ⟨cp, hcp, hcpu, hcpl, by rw [hW]; omega⟩ rP rL (by rw [hW]; exact henc) with
    ⟨q, s', ω', μ', ha, run, g0, g1, g5, g6, gO, gO8, gO16, gO24, gdat, gR0, gR8, H', keep, hnew, hfresh, kd, -,
      gfr, glo, ggl, gwr⟩ | ⟨hna, ω', μ', run, f7⟩
  · rw [hW] at gdat gR0 gR8
    refine Or.inl ⟨ω', μ', s', run.mono (by omega), by rw [g1]; congr 1; omega, g5, g6, by rw [gR0],
      by rw [gR8]; congr 1; omega, ⟨9223372036854775816, by decide, gO, by decide⟩, H', keep, kd, ?_,
      fun a h0 h1 h2 h3 => gfr a h1 (by omega) h2 (by omega), fun a ha => (glo a ha).1,
      fun a ha => (glo a ha).2, ggl, fun a ha => gwr a (by unfold S0; omega)⟩
    refine ⟨[⟨q - 32, (16 * n + 31) / 32 + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · have hqm := VecU8.chunk_in H'.wf hnew rfl
      simp only at hqm
      refine ⟨by rw [readN_take _ _ 232 8 (by decide)]; exact gO, q, ?_, ?_, ?_, ?_⟩
      · rw [← readN_sub μ' (F + 120) 232 8 8 _ rfl (by decide)]; exact gO8
      · rw [← readN_sub μ' (F + 120) 232 16 8 _ rfl (by decide)]; exact gO16
      · rw [← readN_sub μ' (F + 120) 232 24 8 _ rfl (by decide)]; exact gO24
      · rw [Memory.readN_congr (fun j hj => hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩), gdat]
        exact hitems
  · exact Or.inr ((Exhausts.of_alloc run f7 hna).mono (by omega))

end Services.Bootstrap.Decode.ImportElem
