import Services.Bootstrap.Acc.Inputs.LoopItem

/-!
# An operand is an `ItemOk` item

The operand's encoding (GP v0.8.0 §12 𝕌, Appendix C): the tag 0, the four hashes h (128 octets), ℰ(g),
the work result O(l) (tag 0 then ↕o, or a tag e ∈ 1 … 6) and ↕t; and its slot (`item_op_ok`,
`item_op_err`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The 8-octet word at offset k of a slot's octets. -/
def wd (bs : List UInt8) (k : Nat) : Nat := Num.decodeLE ((bs.drop k).take 8)

/-- An operand with a work output: tag 0, h, ℰ(g), 0, ↕o, ↕t. -/
def encOpOk (h : List UInt8) (g : Nat) (o t : List UInt8) : List UInt8 :=
  [0] ++ (h ++ (Blob.encodeNat g ++ ([0] ++ (Blob.encodeNat o.length ++ (o ++ (Blob.encodeNat t.length ++ t))))))

/-- An operand with a work error e: tag 0, h, ℰ(g), e, ↕t. -/
def encOpErr (h : List UInt8) (g e : Nat) (t : List UInt8) : List UInt8 :=
  [0] ++ (h ++ (Blob.encodeNat g ++ ([UInt8.ofNat e] ++ (Blob.encodeNat t.length ++ t))))

/-- What both operand slots hold: the trace (capacity and length |t|, its octets at the pointer), the
    hashes at + 48 and g at + 176. -/
def RepOpBase (h : List UInt8) (g : Nat) (t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  wd bs 0 = t.length ∧ wd bs 16 = t.length ∧ μ.readN (wd bs 8) t.length = t ∧
    (bs.drop 48).take 128 = h ∧ wd bs 176 = g

/-- An operand slot with a work output o (capacity and length |o| at + 24 / + 40, octets at + 32). -/
def RepOpOk (h : List UInt8) (g : Nat) (o t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  RepOpBase h g t bs μ ∧ wd bs 24 = o.length ∧ wd bs 40 = o.length ∧ μ.readN (wd bs 32) o.length = o

/-- An operand slot with a work error e (−1 at + 24, e at + 32). -/
def RepOpErr (h : List UInt8) (g e : Nat) (t : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  RepOpBase h g t bs μ ∧ wd bs 24 = 18446744073709551615 ∧ wd bs 32 = e

/-- A word of a slot's octets is the slot's word. -/
theorem wd_slot (μ : Memory) (o k : Nat) (h : k + 8 ≤ 184) : wd (μ.readN o 184) k = rdN μ (o + k) 8 := by
  unfold wd rdN; rw [readN_drop_take μ o 184 k 8 h]

/-- 128 octets as four 32-octet pieces. -/
theorem readN128 (ν : Memory) (a : Nat) : ν.readN a 128 =
    ν.readN a 32 ++ (ν.readN (a + 32) 32 ++ (ν.readN (a + 64) 32 ++ ν.readN (a + 96) 32)) := by
  rw [← PVM.Memory.readN_split, ← PVM.Memory.readN_split, ← PVM.Memory.readN_split]

/-- **An operand with a work output is an `ItemOk` item** (`item_op_ok` and the return to 45168), for
    an output and a trace of at most 16384 octets each (the temporary bound). -/
theorem itemOk_opok {X : Type} (env : HeapHost X) (cap pb : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (h : List UInt8) (g : Nat) (o t : List UInt8) (hh : h.length = 128) (hg : g < 18446744073709551616)
    (ho : o.length ≤ 16384) (ht : t.length ≤ 16384) :
    ItemOk env cap pb p P (7 * 16384 + 7 * 16384 + 7101) (encOpOk h g o t) (RepOpOk h g o t) := by
  intro x ω μ hb s sp rd ip rlen S0 S1 H h0 h1 h7 h8 hsp hsp8 hSTk hrdsp hrdS hR0 hR8 hrl hrl32 henc hsrc
  have hL : (encOpOk h g o t).length = 1 + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat o.length).length +
      o.length + (Blob.encodeNat t.length).length + t.length) := by simp [encOpOk, hh]; omega
  -- the pieces of the encoding
  unfold encOpOk at henc
  obtain ⟨p0, r1⟩ := readN_app μ ip _ _ (by rw [← List.length_append]; exact henc)
  obtain ⟨ph, r2⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r1)
  obtain ⟨pg, r3⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r2)
  obtain ⟨pz, r4⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r3)
  obtain ⟨peo, r5⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r4)
  obtain ⟨po', r6⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r5)
  obtain ⟨pet, pt'⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r6)
  simp only [List.length_singleton, hh] at p0 ph pg pz peo po' pet pt'
  rw [hL] at hrl hsrc
  rcases item_op_ok (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s sp (sp + 88) rd ip rlen g o.length t.length
      pb S0 S1 H h1 h7 h8 ⟨hsp, hsp8⟩ hSTk ⟨by omega, hrdS⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) hR0 hR8 hg ho ht
      hrl hrl32 p0 pg pz peo pet
      (by obtain ⟨c, c1, c2, c3, c4⟩ := hsrc; exact ⟨c, c1, c2, c3, by omega⟩) with
    ⟨po, pt, s1, s2, ω', μ', va1, va2, run, H', keep, keepa, keepb, keepd, e0, e1, e5, e6, x0, x8, x16, x24, x32, x40,
      X48, X80, X112, X144, x176, od, td, R0f, R8f, fr⟩ | ⟨ω', μ', run⟩
  · have mo := va1.blk_mem
    have mt := va2.blk_mem
    have cso : ∀ c ∈ blk o.length po, c ∈ chunks s2 := fun c hc => keepb c (mo c hc).1 (mo c hc).2.1
    have cst : ∀ c ∈ blk t.length pt, c ∈ chunks s2 := fun c hc => (mt c hc).1
    refine Or.inl ⟨s2, ω', μ', (run.trans (lp_ret_op (p := p) (P := P) (R := env.rel cap) x ω' μ'
        (by rw [e0, h0]))).mono (by omega), by rw [e0, h0], e1, e5, e6, by rw [x0]; omega, H', keep, keepd,
      ⟨blk o.length po ++ blk t.length pt, fun c hc => ?_, fun μ'' hag => ?_⟩,
      by rw [R0f, hL]; all_goals (congr 1 <;> omega), by rw [R8f, hL]; all_goals (congr 1 <;> omega), fun a h0 hs h1 h2 => fr a h0 hs (by omega) h2⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨cso c hc, (mo c hc).2.1, (mo c hc).2.2⟩
      · exact ⟨(mt c hc).1, (mt c hc).2.1, fun d hd hu => (mt c hc).2.2 d (keepa d hd hu) hu⟩
    · have ro : μ''.readN po o.length = o := by
        rw [blk_read H' cso μ'' μ' (fun c hc a ha => hag c (List.mem_append_left _ hc) a ha), od, po']
      have rt : μ''.readN pt t.length = t := by
        rw [blk_read H' cst μ'' μ' (fun c hc a ha => hag c (List.mem_append_right _ hc) a ha), td, pt']
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [wd_slot _ _ _ (by omega)]; simpa using x0
      · rw [wd_slot _ _ _ (by omega)]; exact x16
      · rw [wd_slot _ _ _ (by omega), x8]; exact rt
      · rw [readN_drop_take μ' (sp + 88) 184 48 128 (by omega), readN128, ← ph, readN128,
          show sp + 88 + 48 = sp + 88 + 48 by rfl, X48.readN, show sp + 88 + 48 + 32 = sp + 88 + 80 by omega, X80.readN,
          show sp + 88 + 48 + 64 = sp + 88 + 112 by omega, X112.readN,
          show sp + 88 + 48 + 96 = sp + 88 + 144 by omega, X144.readN]
      · rw [wd_slot _ _ _ (by omega)]; exact x176
      · rw [wd_slot _ _ _ (by omega)]; exact x24
      · rw [wd_slot _ _ _ (by omega)]; exact x40
      · rw [wd_slot _ _ _ (by omega), x32]; exact ro
  · exact Or.inr ⟨ω', μ', run.mono (by omega)⟩

/-- **An operand with a work error is an `ItemOk` item** (`item_op_err` and the return to 45168), for a
    trace of at most 16384 octets (the temporary bound). -/
theorem itemOk_operr {X : Type} (env : HeapHost X) (cap pb : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (h : List UInt8) (g e : Nat) (t : List UInt8) (hh : h.length = 128) (hg : g < 18446744073709551616)
    (he : 1 ≤ e ∧ e ≤ 6) (ht : t.length ≤ 16384) :
    ItemOk env cap pb p P (7 * 16384 + 7101) (encOpErr h g e t) (RepOpErr h g e t) := by
  intro x ω μ hb s sp rd ip rlen S0 S1 H h0 h1 h7 h8 hsp hsp8 hSTk hrdsp hrdS hR0 hR8 hrl hrl32 henc hsrc
  have hL : (encOpErr h g e t).length = 1 + (128 + (Blob.encodeNat g).length + 1 +
      (Blob.encodeNat t.length).length + t.length) := by simp [encOpErr, hh]; omega
  unfold encOpErr at henc
  obtain ⟨p0, r1⟩ := readN_app μ ip _ _ (by rw [← List.length_append]; exact henc)
  obtain ⟨ph, r2⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r1)
  obtain ⟨pg, r3⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r2)
  obtain ⟨pe, r4⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r3)
  obtain ⟨pet, pt'⟩ := readN_app μ _ _ _ (by rw [← List.length_append]; exact r4)
  simp only [List.length_singleton, hh] at p0 ph pg pe pet pt'
  rw [hL] at hrl hsrc
  have pe' : rdN μ (ip + 1 + 128 + (Blob.encodeNat g).length) 1 = e := by
    unfold rdN; rw [pe]; simp [Num.decodeLE]; omega
  rcases item_op_err (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s sp (sp + 88) rd ip rlen g e t.length
      pb S0 S1 H h1 h7 h8 ⟨hsp, hsp8⟩ hSTk ⟨by omega, hrdS⟩ ⟨by omega, by omega⟩ (Or.inl (by omega)) hR0 hR8 hg he ht
      hrl hrl32 p0 pg pe' pet
      (by obtain ⟨c, c1, c2, c3, c4⟩ := hsrc; exact ⟨c, c1, c2, c3, by omega⟩) with
    ⟨pt, s2, ω', μ', va2, run, H', keep, keepd, e0, e1, e5, e6, x0, x8, x16, x24, x32,
      X48, X80, X112, X144, x176, td, R0f, R8f, fr⟩ | ⟨ω', μ', run⟩
  · have mt := va2.blk_mem
    have cst : ∀ c ∈ blk t.length pt, c ∈ chunks s2 := fun c hc => (mt c hc).1
    refine Or.inl ⟨s2, ω', μ', (run.trans (lp_ret_op (p := p) (P := P) (R := env.rel cap) x ω' μ'
        (by rw [e0, h0]))).mono (by omega), by rw [e0, h0], e1, e5, e6, by rw [x0]; omega, H', keep, keepd,
      ⟨blk t.length pt, fun c hc => mt c hc, fun μ'' hag => ?_⟩,
      by rw [R0f, hL]; all_goals (congr 1 <;> omega), by rw [R8f, hL]; all_goals (congr 1 <;> omega),
      fun a h0 hs h1 h2 => fr a h0 hs (by omega) h2⟩
    have rt : μ''.readN pt t.length = t := by
      rw [blk_read H' cst μ'' μ' hag, td, pt']
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [wd_slot _ _ _ (by omega)]; simpa using x0
    · rw [wd_slot _ _ _ (by omega)]; exact x16
    · rw [wd_slot _ _ _ (by omega), x8]; exact rt
    · rw [readN_drop_take μ' (sp + 88) 184 48 128 (by omega), readN128, ← ph, readN128,
        show sp + 88 + 48 = sp + 88 + 48 by rfl, X48.readN, show sp + 88 + 48 + 32 = sp + 88 + 80 by omega, X80.readN,
        show sp + 88 + 48 + 64 = sp + 88 + 112 by omega, X112.readN,
        show sp + 88 + 48 + 96 = sp + 88 + 144 by omega, X144.readN]
    · rw [wd_slot _ _ _ (by omega)]; exact x176
    · rw [wd_slot _ _ _ (by omega)]; exact x24
    · rw [wd_slot _ _ _ (by omega)]; exact x32
  · exact Or.inr ⟨ω', μ', run.mono (by omega)⟩

end Services.Bootstrap.Acc
