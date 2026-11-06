import Services.Bootstrap.Alloc.FreePrev
import Services.Bootstrap.Alloc.UnregisterRep

/-!
# The binary's `free`, stage by stage

The blocks of `FreeNext`/`FreePrev`/`Register` composed against the model's steps: the last
stage (`free_tail`, 42814 … 40681) is `freeFinal`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A header address of the heap at `base`: 32-aligned from it and inside the heap, which lies
    above the allocator and below 2³¹. -/
def Al (base a : Nat) : Prop := base ≤ a ∧ (a - base) % 32 = 0 ∧ a + 32 ≤ base + 1073741824

theorem binDown_small {x : Nat} (h1 : 1 ≤ x) (h2 : x ≤ 127) : binDown x = x - 1 := by
  unfold binDown toBin
  rw [maxSize_val]
  simp only [show min x 33554432 = x by omega, show x ≠ 0 by omega, ↓reduceIte, mantissaBits,
    show x < 2 ^ 7 by simp; omega]

/-- Setting one header's `prev` against memory. -/
theorem setPrev_rep {μ μ' : Memory} {t : State} {H F : Nat → Prop} {a v : Nat}
    (h : RepAt μ t H F) (haH : H a) (w1 : rdN μ' a 4 = v)
    (wf : ∀ b, b < 4294967296 → (b < a ∨ a + 4 ≤ b) → μ'.read b = μ.read b)
    (ha : 206864 ≤ a)
    (hHa : ∀ b, H b ∨ F b → 206864 ≤ b ∧ b + 16 < 4294967296 ∧ (b = a ∨ b + 16 ≤ a ∨ a + 16 ≤ b)) :
    RepAt μ' (setHdr t a (fun h => { h with prev := v })) H F := by
  have pr : ∀ b, (setHdr t a (fun h => { h with prev := v })).hdr b =
      if b = a then { t.hdr a with prev := v } else t.hdr b := by
    intro b; by_cases hb : b = a
    · subst hb; rw [setHdr_self, if_pos rfl]
    · rw [setHdr_other hb, if_neg hb]
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [show (setHdr t a _).heads = t.heads from rfl, ← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (setHdr t a _).secondary = t.secondary from rfl, ← h.sec q hq]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (setHdr t a _).primary = t.primary from rfl, ← h.pri]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (setHdr t a _).base = t.base from rfl, ← h.base]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [show (setHdr t a _).allocated = t.allocated from rfl, ← h.alloc]; unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [pr]
    by_cases hba : b = a
    · subst hba; rw [if_pos rfl, w1]
    · rw [if_neg hba]
      obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb)
      rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inl hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.size _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.next _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · obtain ⟨b1, b2, b3⟩ := hHa b (Or.inr hb)
    rw [pr]; split
    · rename_i hba; subst hba; rw [← h.prevL _ hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
    · rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)


/-- `RepAt` depends only on the octets read. -/
theorem RepAt.congr {μ μ' : Memory} {t : State} {H F : Nat → Prop} (h : RepAt μ t H F)
    (wf : ∀ b, b < 4294967296 → μ'.read b = μ.read b)
    (hHa : ∀ b, H b ∨ F b → b + 16 < 4294967296) : RepAt μ' t H F := by
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inl hb); rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inl hb); rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inr hb); rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega)
  · have := hHa b (Or.inr hb); rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega)

theorem readN_frame {μ μ' : Memory} {a n : Nat} (h : ∀ j, j < n → μ'.read (a + j) = μ.read (a + j)) :
    μ'.readN a n = μ.readN a n := readN_congr2 h


/-- **The last stage of `free`, 42814 … the return into `dealloc`** (40681): the merged chunk M of
    `total` units, with `prev` pv, is registered free and the chunk after it records `total` — the
    memory holds the model's `freeFinal`. -/
theorem free_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s2 : State) (H F : Nat → Prop) (base M pv total sp v5 v6 : Nat)
    (hrep : RepAt μ s2 H F)
    (h2 : ω[2] = UInt64.ofNat total) (h8 : ω[8] = UInt64.ofNat M) (h3 : ω[3] = UInt64.ofNat pv)
    (h7 : ω[7] = UInt64.ofNat 196792) (h4 : ω[4] = UInt64.ofNat 204984)
    (h12 : ω[12] = UInt64.ofNat (base + 1073741824)) (h1 : ω[1] = UInt64.ofNat (sp - 24))
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648)
    (ht1 : 1 ≤ total) (ht2 : total ≤ 33554432) (hAM : Al base M) (hMt : M + 32 * total ≤ base + 1073741824)
    (hpv : pv < 4294967296) (hold : s2.heads (binDown total) ≠ M)
    (hold1 : s2.heads (binDown total) ≠ 0 → Al base (s2.heads (binDown total)))
    (hHF : ∀ a, H a ∨ F a → Al base a) (hnext : M + 32 * total < base + 1073741824 → H (M + 32 * total))
    (s0 : μ.readN (sp - 8) 8 = Num.encodeLE 8 1986) (s5 : μ.readN (sp - 16) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (sp - 24) 8 = Num.encodeLE 8 v6) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hsp : 2147483700 ≤ sp) (hsp1 : sp < 4294967296)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42814 ω μ x 40681 ω' μ' x 60 ∧
      RepAt μ' (freeFinal s2 M pv total (base + 1073741824)) (fun a => H a ∨ a = M) (fun a => F a ∨ a = M) ∧
      (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = UInt64.ofNat 1986 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨hM1, hM2, hM3⟩ := hAM
  have hB : binDown total < 2432 := toBin_lt false (Nat.min_le_right _ _)
  -- the bin
  obtain ⟨ω1, r1, h91, fr1⟩ : ∃ ω1, FreeStepsH p R 42814 ω μ x 42862 ω1 μ x 15 ∧
      ω1[9] = UInt64.ofNat (binDown total + 1) ∧ ∀ j : Fin 13, j.val ∉ [9, 10, 11] → ω1[j] = ω[j] := by
    by_cases hs : total ≤ 127
    · obtain ⟨ω1, r1, h9, fr⟩ := reg_bin_small (p := p) (P := P) (R := R) x ω μ total h2 (by omega) hs
      refine ⟨ω1, r1.mono (by omega), by rw [h9, binDown_small ht1 hs]; congr 1; omega, fun j hj => ?_⟩
      exact fr j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
    · exact reg_bin_big (p := p) (P := P) (R := R) x ω μ total h2 (by omega) (by omega)
  generalize hbin : binDown total = bin at *
  generalize hO : s2.heads bin = old at *
  have hold' : rdN μ (bin * 4 + 196792) 4 = old := by
    have := hrep.heads bin (by unfold binCount; omega)
    unfold A0 at this; rw [show bin * 4 + 196792 = 196792 + 4 * bin by omega, this, hO]
  have hold2 : old < 2147483648 := by
    by_cases h0 : old = 0
    · omega
    · have := hold1 h0; unfold Al at this; omega
  have holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ M ∨ M + 16 ≤ old) := by
    intro h0; have := hold1 h0; unfold Al at this; omega
  have g : ∀ j : Nat, (hj : j < 13) → j ∉ [9, 10, 11] → ω1[j]'hj = ω[j]'hj := fun j hj h => by
    have := fr1 ⟨j, hj⟩ h; simpa only [Fin.getElem_fin] using this
  obtain ⟨ω2, μ2, r2, w1, w2, w3, w4, w5, w6, w7, w8, wf2, ww2, fr2⟩ := reg_write (p := p) (P := P) (R := R) x ω1 μ bin M pv total old h91
    (by rw [g 2 (by decide) (by decide)]; exact h2) (by rw [g 8 (by decide) (by decide)]; exact h8)
    (by rw [g 3 (by decide) (by decide)]; exact h3) (by rw [g 7 (by decide) (by decide)]; exact h7)
    (by rw [g 4 (by decide) (by decide)]; exact h4) hB (by omega) (by omega) hpv (by omega) hold' hold2
    holda hw
  have hrep2 := register_rep (μ' := μ2) (M := M) (pv := pv) (size := total) hrep (by omega)
    (by rw [hbin]; unfold binCount; omega) (by rw [hbin, hO]; exact hold) (by rw [hbin]; exact w1)
    w2 w3 (by rw [hbin, hO]; exact w4) w5 (by rw [hbin, hO]; exact w6) (by rw [hbin]; exact w7)
    (by rw [hbin]; exact w8) (by rw [hbin, hO]; exact wf2) (by omega) (by omega)
    (by rw [hbin, hO]; intro h0; exact (holda h0).1)
    (fun a ha => by
      have := hHF a ha; unfold Al at this; rw [hbin, hO]
      refine ⟨by omega, by omega, by omega, ?_⟩
      by_cases h0 : old = 0
      · exact Or.inl h0
      · have := hold1 h0; unfold Al at this; omega)
  -- the stack is untouched
  have hold3 : old = 0 ∨ old + 32 ≤ base + 1073741824 := by
    by_cases h0 : old = 0
    · exact Or.inl h0
    · have := hold1 h0; unfold Al at this; exact Or.inr (by omega)
  have stk : ∀ a, 2147483648 ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h1 h2 =>
    wf2 a h2 (by omega) (by omega) (by omega) (by omega) (by omega)
  have g2 : ∀ j : Nat, (hj : j < 13) → j ∉ [5, 6, 7, 9, 10, 11] → ω2[j]'hj = ω1[j]'hj := fun j hj h => by
    have := fr2 ⟨j, hj⟩ h; simpa only [Fin.getElem_fin] using this
  obtain ⟨ω3, μ3, r3, e1, ef, ew, e0, e1', e5, e6, -⟩ := free_epi (p := p) (P := P) (R := R) x ω2 μ2 sp M total
    (base + 1073741824) v5 v6
    (by rw [g2 1 (by decide) (by decide), g 1 (by decide) (by decide)]; exact h1)
    (by rw [g2 2 (by decide) (by decide), g 2 (by decide) (by decide)]; exact h2)
    (by rw [g2 8 (by decide) (by decide), g 8 (by decide) (by decide)]; exact h8)
    (by rw [g2 12 (by decide) (by decide), g 12 (by decide) (by decide)]; exact h12)
    hsp hsp1 (by omega) hbT (by omega)
    (by rw [← s0]; exact readN_frame fun j hj => stk _ (by omega) (by omega))
    (by rw [← s5]; exact readN_frame fun j hj => stk _ (by omega) (by omega))
    (by rw [← s6]; exact readN_frame fun j hj => stk _ (by omega) (by omega)) hv5 hv6 ww2
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), ?_, ew,
    fun a h1 h2 => (ef a h1 (by omega)).trans (stk a h2 h1), e0, e1', e5, e6⟩
  -- the model's last step
  have hsnd : (register s2 M pv total).2 = total := by rw [register_snd, if_neg (by omega)]
  unfold freeFinal
  rw [hsnd]
  split
  · rename_i hlt
    refine setPrev_rep hrep2 (Or.inl (hnext hlt)) (e1 hlt) (fun b h1 h2 => ef b h1 (Or.inr h2)) (by omega)
      (fun b hb => ?_)
    rcases hb with (hb | rfl) | (hb | rfl)
    · have := hHF b (Or.inl hb); have := hHF _ (Or.inl (hnext hlt)); unfold Al at *; omega
    · omega
    · have := hHF b (Or.inr hb); have := hHF _ (Or.inl (hnext hlt)); unfold Al at *; omega
    · omega
  · rename_i hge
    refine hrep2.congr (fun b hb => ef b hb (Or.inl (by omega))) (fun b hb => ?_)
    rcases hb with (hb | rfl) | (hb | rfl)
    · have := hHF b (Or.inl hb); unfold Al at this; omega
    · omega
    · have := hHF b (Or.inr hb); unfold Al at this; omega
    · omega


/-- 42630 … the head test, the next chunk nc free with sz units (1 … 2²⁵) and its bin's head `hd`:
    to 42675 if nc is the head, with ω₀ = sz, ω₅ = its bin, ω₆ = the head slot. -/
theorem nx_lookup_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc sz : Nat) (h5 : ω[5] = UInt64.ofNat (2 * sz)) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat nc) (hs1 : 1 ≤ sz) (hs2 : sz ≤ 33554432)
    (hhd : rdN μ (196792 + binDown sz * 4) 4 = nc) (hnc : nc < 2147483648) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42630 ω μ x 42675 ω' μ x 21 ∧ ω'[0] = UInt64.ofNat sz ∧
      ω'[5] = UInt64.ofNat (binDown sz) ∧ ω'[6] = UInt64.ofNat (196792 + binDown sz * 4) ∧
      ∀ j : Fin 13, j.val ∉ [0, 5, 6, 10] → ω'[j] = ω[j] := by
  by_cases hs : sz ≤ 127
  · rw [binDown_small hs1 hs] at hhd ⊢
    obtain ⟨ω1, r1, a0, a5, a6, a10, fr⟩ := nx_bin_small (p := p) (P := P) (R := R) x ω μ sz nc h5 h7 hs1
      (by omega) hhd hnc hr
    have b := nx_br_head_s (p := p) (P := P) (R := R) x ω1 μ nc
      (by have := fr ⟨9, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact h9) a10
    refine ⟨ω1, (r1.trans b).mono (by omega), a0, a5, a6, fun j hj => fr j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
  · obtain ⟨ω1, r1, a0, a5, fr1⟩ := nx_bin_big (p := p) (P := P) (R := R) x ω μ sz h5 (by omega) hs2
    have hB : binDown sz < 2432 := toBin_lt false (Nat.min_le_right _ _)
    obtain ⟨ω2, r2, a6, a10, fr2⟩ := nx_head_big (p := p) (P := P) (R := R) x ω1 μ (binDown sz) nc a5
      (by have := fr1 ⟨7, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact h7)
      hB hhd hnc hr
    have b := nx_br_head_b (p := p) (P := P) (R := R) x ω2 μ nc
      (by
        have e2 := fr2 ⟨9, by decide⟩ (by decide); have e1 := fr1 ⟨9, by decide⟩ (by decide)
        simp only [Fin.getElem_fin] at e1 e2; rw [e2, e1]; exact h9) a10
    refine ⟨ω2, ((r1.trans r2).trans b).mono (by omega),
      by have := fr2 ⟨0, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact a0,
      by have := fr2 ⟨5, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact a5,
      a6, fun j hj => ?_⟩
    rw [fr2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
      fr1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]

/-- 42630 … the head test, nc not its bin's head `hd`: to 42732. -/
theorem nx_lookup_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (nc sz hd : Nat) (h5 : ω[5] = UInt64.ofNat (2 * sz)) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat nc) (hs1 : 1 ≤ sz) (hs2 : sz ≤ 33554432)
    (hhd : rdN μ (196792 + binDown sz * 4) 4 = hd) (hne : hd ≠ nc) (hhd1 : hd < 2147483648)
    (hnc : nc < 2147483648) (hr : ∀ a, μ.readable a = true) :
    ∃ ω', FreeStepsH p R 42630 ω μ x 42732 ω' μ x 21 ∧ ω'[0] = UInt64.ofNat sz ∧
      ω'[5] = UInt64.ofNat (binDown sz) ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 6, 10] → ω'[j] = ω[j] := by
  by_cases hs : sz ≤ 127
  · rw [binDown_small hs1 hs] at hhd ⊢
    obtain ⟨ω1, r1, a0, a5, a6, a10, fr⟩ := nx_bin_small (p := p) (P := P) (R := R) x ω μ sz hd h5 h7 hs1
      (by omega) hhd hhd1 hr
    have b := nx_br_mid_s (p := p) (P := P) (R := R) x ω1 μ nc hd
      (by have := fr ⟨9, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact h9) a10
      hne hnc hhd1
    refine ⟨ω1, (r1.trans b).mono (by omega), a0, a5, fun j hj => fr j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
  · obtain ⟨ω1, r1, a0, a5, fr1⟩ := nx_bin_big (p := p) (P := P) (R := R) x ω μ sz h5 (by omega) hs2
    have hB : binDown sz < 2432 := toBin_lt false (Nat.min_le_right _ _)
    obtain ⟨ω2, r2, a6, a10, fr2⟩ := nx_head_big (p := p) (P := P) (R := R) x ω1 μ (binDown sz) hd a5
      (by have := fr1 ⟨7, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact h7)
      hB hhd hhd1 hr
    have b := nx_br_mid_b (p := p) (P := P) (R := R) x ω2 μ nc hd
      (by
        have e2 := fr2 ⟨9, by decide⟩ (by decide); have e1 := fr1 ⟨9, by decide⟩ (by decide)
        simp only [Fin.getElem_fin] at e1 e2; rw [e2, e1]; exact h9) a10 hne hnc hhd1
    refine ⟨ω2, ((r1.trans r2).trans b).mono (by omega),
      by have := fr2 ⟨0, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact a0,
      by have := fr2 ⟨5, by decide⟩ (by decide); simp only [Fin.getElem_fin] at this; rw [this]; exact a5,
      fun j hj => ?_⟩
    rw [fr2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
      fr1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]


theorem fget {ω' ω : Regs} {l : List Nat} (fr : ∀ j : Fin 13, j.val ∉ l → ω'[j] = ω[j]) (j : Nat) (hj : j < 13)
    (hl : j ∉ l) : ω'[j]'hj = ω[j]'hj := by
  have := fr ⟨j, hj⟩ hl; simpa only [Fin.getElem_fin] using this

/-- **42675 … 42814**: the next chunk nc, its bin's head, leaves the list — the memory holds
    `unregister s nc bin`; ω₂ = size + sz. -/
theorem nx_unreg_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (base nc bin size sz : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin = nc) (hb : bin < binCount) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h11 : ω[11] = UInt64.ofNat nc) (h6 : ω[6] = UInt64.ofNat (196792 + bin * 4))
    (h0 : ω[0] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size) (h5 : ω[5] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (h4 : ω[4] = UInt64.ofNat 204984) (hss : size + sz < 2147483648)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42675 ω μ x 42814 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ω'[2] = UInt64.ofNat (size + sz) ∧ ∀ j : Fin 13, j.val ∉ [2, 5, 6, 9, 10, 11] → ω'[j] = ω[j] := by
  have hAn := hHF nc (Or.inr hFn)
  unfold binCount at hb
  have hn : rdN μ (nc + 8) 4 = (s.hdr nc).next := hrep.next nc hFn
  unfold Al at hAn
  by_cases h0' : (s.hdr nc).next = 0
  · -- the list's last element
    obtain ⟨ω1, μ1, r1, s1, fr1, ww1, g1⟩ := nx_unlink_head0 (p := p) (P := P) (R := R) x ω μ nc
      (196792 + bin * 4) h11 h6 (by rw [hn, h0']) (by omega) (by omega) hw
    have hsec := hrep.sec (bin / 64) (by omega)
    have hpri := hrep.pri
    unfold A0 at hsec hpri
    have hw1 : rdN μ1 (204984 + bin / 64 * 8 + 1544) 8 = s.secondary (bin / 64) := by
      rw [← hsec, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega]
      exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    have hp1 : rdN μ1 206832 8 = s.primary := by
      rw [← hpri]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    obtain ⟨ω2, μ2, r2, c1, c2, cf, cw, c2', cg⟩ := nx_clear (p := p) (P := P) (R := R) x ω1 μ1 bin
      (s.secondary (bin / 64)) s.primary size sz
      (by rw [fget g1 5 (by decide) (by decide)]; exact h5) (by rw [fget g1 7 (by decide) (by decide)]; exact h7)
      (by rw [fget g1 4 (by decide) (by decide)]; exact h4) (by rw [fget g1 0 (by decide) (by decide)]; exact h0)
      (by rw [fget g1 2 (by decide) (by decide)]; exact h2) (by omega) hw1 hp1 hss ww1
    refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), ?_, cw, fun a h1 h2 => ?_, c2', fun j hj => ?_⟩
    · refine unregister_rep_last hrep hc (by unfold binCount; omega) h0' ?_ ?_ ?_ ?_ (fun a ha => ?_)
      · rw [← s1]; exact rdN_frame fun j hj => cf _ (by omega) (by omega) (by omega)
      · rw [c1, ← hsec, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega]
      · rw [c2, ← hsec, ← hpri, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega,
          show 196792 + 10040 = 206832 from rfl]
      · intro a h1 h2 h3 h4; rw [cf a h1 h3 h4, fr1 a h1 h2]
      · have := hHF a ha; unfold Al at this; omega
    · rw [cf a h1 (by omega) (by omega), fr1 a h1 (by omega)]
    · rw [cg j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
        g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]
  · -- a successor
    have hFx := hnx h0'
    have hAx := hHF _ (Or.inr hFx)
    unfold Al at hAx
    obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, e2, g1⟩ := nx_unlink_head (p := p) (P := P) (R := R) x ω μ nc
      (196792 + bin * 4) (s.hdr nc).next size sz h11 h6 h0 h2 hn (by omega) h0' (by omega) (by omega)
      (by omega) hss hw
    refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by omega), e2,
      fun j hj => g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
    refine unregister_rep_head hrep hc (by unfold binCount; omega) h0' s1 s2
      (fun a h1 h2 h3 => fr1 a h1 (by omega) h3) (by omega) (fun a ha => ?_)
    have := hHF a ha; unfold Al at this; omega

/-- **42732 … 42814**: the next chunk nc, inside its bin's list, leaves it — the memory holds
    `unregister s nc bin`; ω₂ = size + sz. -/
theorem nx_unreg_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (base nc bin size sz : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin ≠ nc) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hpv : F (s.hdr nc).prevL) (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next)
    (hpn : (s.hdr nc).next ≠ 0 → (s.hdr nc).next ≠ (s.hdr nc).prevL) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h11 : ω[11] = UInt64.ofNat nc) (h0 : ω[0] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size)
    (hss : size + sz < 2147483648) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42732 ω μ x 42814 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ω'[2] = UInt64.ofNat (size + sz) ∧ ∀ j : Fin 13, j.val ∉ [2, 9, 11] → ω'[j] = ω[j] := by
  have hAn := hHF nc (Or.inr hFn)
  have hAp := hHF _ (Or.inr hpv)
  unfold Al at hAn hAp
  have hn : rdN μ (nc + 8) 4 = (s.hdr nc).next := hrep.next nc hFn
  have hp : rdN μ (nc + 12) 4 = (s.hdr nc).prevL := hrep.prevL nc hFn
  have hnxA : (s.hdr nc).next = 0 ∨ ((s.hdr nc).next ≠ 0 ∧ Al base (s.hdr nc).next) := by
    by_cases h0 : (s.hdr nc).next = 0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, hHF _ (Or.inr (hnx h0))⟩
  have hnb : (s.hdr nc).next + 16 < 4294967296 := by
    rcases hnxA with h | ⟨_, h⟩
    · omega
    · unfold Al at h; omega
  obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, e2, g1⟩ := nx_unlink_mid (p := p) (P := P) (R := R) x ω μ nc
    (s.hdr nc).prevL (s.hdr nc).next size sz h11 h0 h2 hn hp (by omega) hnb (by omega)
    (fun h0 => by
      have := hpn h0
      rcases hnxA with h | ⟨_, h⟩
      · exact absurd h h0
      · unfold Al at h; omega) hss hw
  refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by
      rcases hnxA with h | ⟨_, h⟩
      · exact Or.inl h
      · unfold Al at h; omega), e2, g1⟩
  refine unregister_rep_mid hrep hc s1 s2 fr1 (by omega)
    (fun h0 => by rcases hnxA with h | ⟨_, h⟩; exact absurd h h0; unfold Al at h; omega)
    hpn (fun a ha => ?_)
  have := hHF a ha; unfold Al at this
  refine ⟨by omega, by omega, by omega, ?_⟩
  rcases hnxA with h | ⟨_, h⟩
  · exact Or.inl h
  · unfold Al at h; omega


/-- What `free_next` needs of a free next chunk nc (the invariant gives it): a free chunk of 1 … 2²⁵
    units, linked in its bin's list. -/
def NxFree (s : State) (F : Nat → Prop) (base nc sz1 : Nat) : Prop :=
  F nc ∧ 2 ≤ (s.hdr nc).size ∧ (s.hdr nc).size ≤ 67108864 ∧ sz1 + (s.hdr nc).size / 2 < 2147483648 ∧
    (s.heads (binDown ((s.hdr nc).size / 2)) = 0 ∨ Al base (s.heads (binDown ((s.hdr nc).size / 2)))) ∧
    ((s.hdr nc).next ≠ 0 → F (s.hdr nc).next) ∧
    (s.heads (binDown ((s.hdr nc).size / 2)) ≠ nc → F (s.hdr nc).prevL ∧
      ((s.hdr nc).next ≠ 0 → (s.hdr nc).next ≠ (s.hdr nc).prevL))

/-- **`free`'s merge with the next chunk, 42597 … 42814**: the memory holds the model's
    `mergeNext`, and ω₂ its merged size. -/
theorem free_next {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (base M sz1 : Nat) (hrep : RepAt μ s H F)
    (h5 : ω[5] = UInt64.ofNat base) (h2 : ω[2] = UInt64.ofNat sz1) (h8 : ω[8] = UInt64.ofNat M)
    (h7 : ω[7] = UInt64.ofNat 196792) (h4 : ω[4] = UInt64.ofNat 204984)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648) (hAM : Al base M)
    (hM : M + 32 * sz1 ≤ base + 1073741824) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnc : M + 32 * sz1 < base + 1073741824 → H (M + 32 * sz1))
    (hfree : M + 32 * sz1 < base + 1073741824 → (s.hdr (M + 32 * sz1)).size % 2 = 0 →
      NxFree s F base (M + 32 * sz1) sz1)
    (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42597 ω μ x 42814 ω' μ' x 70 ∧
      RepAt μ' (mergeNext s M sz1 (base + 1073741824)).1 H F ∧
      ω'[2] = UInt64.ofNat (mergeNext s M sz1 (base + 1073741824)).2 ∧
      ω'[12] = UInt64.ofNat (base + 1073741824) ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 5, 6, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  obtain ⟨hM1, hM2, hM3⟩ := hAM
  obtain ⟨ω1, r1, a12, a9, g1⟩ := nx_addr (p := p) (P := P) (R := R) x ω μ base M sz1 h5 h2 h8 hbT (by omega)
  unfold mergeNext
  by_cases hlt : M + 32 * sz1 < base + 1073741824
  · rw [if_pos hlt]
    have b1 := nx_br_in (p := p) (P := P) (R := R) x ω1 μ (M + 32 * sz1) (base + 1073741824) a9 a12 hlt
      (by omega) hbT
    have hAn := hHF _ (Or.inl (hnc hlt))
    unfold Al at hAn
    have hsz : rdN μ (M + 32 * sz1 + 4) 4 = (s.hdr (M + 32 * sz1)).size := hrep.size _ (hnc hlt)
    obtain ⟨ω2, r2, c5, c10, c11, g2⟩ := nx_hdr (p := p) (P := P) (R := R) x ω1 μ (M + 32 * sz1)
      (s.hdr (M + 32 * sz1)).size a9 (by omega) hsz hr
    generalize hW : (s.hdr (M + 32 * sz1)).size = w at *
    by_cases hu : w % 2 = 1
    · -- the next chunk allocated
      have b2 := nx_br_used (p := p) (P := P) (R := R) x ω2 μ (w % 2) c10 (by omega) (by omega)
      have hwu : (!wordUsed w) = false := by simp [wordUsed, hu]
      rw [if_neg (by simp [hwu])]
      refine ⟨ω2, μ, (((r1.trans b1).trans r2).trans b2).mono (by omega), hrep, ?_, ?_, hw,
        fun _ _ _ => rfl, fun j hj => ?_⟩
      · rw [fget g2 2 (by decide) (by decide), fget g1 2 (by decide) (by decide)]; exact h2
      · rw [fget g2 12 (by decide) (by decide)]; exact a12
      · rw [g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
          g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]
    · -- free: it leaves its bin's list and is merged in
      have hu0 : w % 2 = 0 := by omega
      obtain ⟨hFn, hw2, hw3, hss, hhd, hnx, hmid⟩ := hfree hlt hu0
      rw [hW] at hhd hmid hss hw2 hw3
      have b2 := nx_br_free (p := p) (P := P) (R := R) x ω2 μ (by rw [c10, hu0])
      have hwu : (!wordUsed w) = true := by simp [wordUsed, hu0]
      rw [if_pos hwu]
      have hws : wordSize w = w / 2 := rfl
      rw [hws]
      generalize hsz' : w / 2 = sz at *
      have hw' : w = 2 * sz := by omega
      have h5' : ω2[5] = UInt64.ofNat (2 * sz) := by rw [c5, hw']
      have hB : binDown sz < 2432 := toBin_lt false (Nat.min_le_right _ _)
      have hhd' : rdN μ (196792 + binDown sz * 4) 4 = s.heads (binDown sz) := by
        have := hrep.heads (binDown sz) (by unfold binCount; omega)
        unfold A0 at this; rw [show 196792 + binDown sz * 4 = 196792 + 4 * binDown sz by omega, this]
      have e7 : ω2[7] = UInt64.ofNat 196792 := by
        rw [fget g2 7 (by decide) (by decide), fget g1 7 (by decide) (by decide)]; exact h7
      have e9 : ω2[9] = UInt64.ofNat (M + 32 * sz1) := by rw [fget g2 9 (by decide) (by decide)]; exact a9
      by_cases hh : s.heads (binDown sz) = M + 32 * sz1
      · obtain ⟨ω3, r3, d0, d5, d6, g3⟩ := nx_lookup_head (p := p) (P := P) (R := R) x ω2 μ (M + 32 * sz1) sz
          h5' e7 e9 (by omega) (by omega) (by rw [hhd', hh]) (by omega) hr
        obtain ⟨ω4, μ4, r4, rep4, ww4, sf4, e2, g4⟩ := nx_unreg_head (p := p) (P := P) (R := R) x ω3 μ s H F
          base (M + 32 * sz1) (binDown sz) sz1 sz hrep hh (by unfold binCount; omega) hFn hHF hnx hb0 hbT
          (by rw [fget g3 11 (by decide) (by decide)]; exact c11) d6 d0
          (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide),
            fget g1 2 (by decide) (by decide)]; exact h2) d5
          (by rw [fget g3 7 (by decide) (by decide)]; exact e7)
          (by rw [fget g3 4 (by decide) (by decide), fget g2 4 (by decide) (by decide),
            fget g1 4 (by decide) (by decide)]; exact h4) hss hw
        refine ⟨ω4, μ4, ((((r1.trans b1).trans r2).trans b2).trans r3 |>.trans r4).mono (by omega), rep4, e2,
          ?_, ww4, sf4, fun j hj => ?_⟩
        · rw [fget g4 12 (by decide) (by decide), fget g3 12 (by decide) (by decide),
            fget g2 12 (by decide) (by decide)]; exact a12
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rw [g4 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
      · obtain ⟨hFp, hpn⟩ := hmid hh
        have hhd1 : s.heads (binDown sz) < 2147483648 := by
          rcases hhd with h | h
          · omega
          · unfold Al at h; omega
        obtain ⟨ω3, r3, d0, d5, g3⟩ := nx_lookup_mid (p := p) (P := P) (R := R) x ω2 μ (M + 32 * sz1) sz
          (s.heads (binDown sz)) h5' e7 e9 (by omega) (by omega) hhd' hh hhd1 (by omega) hr
        obtain ⟨ω4, μ4, r4, rep4, ww4, sf4, e2, g4⟩ := nx_unreg_mid (p := p) (P := P) (R := R) x ω3 μ s H F
          base (M + 32 * sz1) (binDown sz) sz1 sz hrep hh hFn hHF hFp hnx hpn hb0 hbT
          (by rw [fget g3 11 (by decide) (by decide)]; exact c11) d0
          (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide),
            fget g1 2 (by decide) (by decide)]; exact h2) hss hw
        refine ⟨ω4, μ4, ((((r1.trans b1).trans r2).trans b2).trans r3 |>.trans r4).mono (by omega), rep4, e2,
          ?_, ww4, sf4, fun j hj => ?_⟩
        · rw [fget g4 12 (by decide) (by decide), fget g3 12 (by decide) (by decide),
            fget g2 12 (by decide) (by decide)]; exact a12
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rw [g4 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
            g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
  · rw [if_neg hlt]
    have b1 := nx_br_end (p := p) (P := P) (R := R) x ω1 μ (M + 32 * sz1) (base + 1073741824) a9 a12
      (by omega) (by omega) hbT
    refine ⟨ω1, μ, (r1.trans b1).mono (by omega), hrep, ?_, a12, hw, fun _ _ _ => rfl, fun j hj => ?_⟩
    · rw [fget g1 2 (by decide) (by decide)]; exact h2
    · exact g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)

end Services.Bootstrap.Alloc
