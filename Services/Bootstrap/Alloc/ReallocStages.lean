import Services.Bootstrap.Alloc.ReallocShrink
import Services.Bootstrap.Alloc.ReallocReg

/-!
# The binary's `shrink_inplace`, stage by stage

The blocks of `ReallocShrink`/`ReallocReg` composed against the model's steps: the old next chunk
leaves its bin (`unregister`), the merge with it (`mergeNext`, 43080 … 43677), and the free tail
with the return (`freeFinal`, 43677 … 40805).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43563 … 43677**: the old next chunk nc, its bin's head, leaves the list — the memory holds
    `unregister s nc bin`; ω₂ = size + sz, ω₅ = n. -/
theorem rs_unreg_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base nc bin size sz n : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin = nc) (hb : bin < binCount) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat nc) (h9 : ω[9] = UInt64.ofNat (196792 + bin * 4))
    (h10 : ω[10] = UInt64.ofNat sz) (h2 : ω[2] = UInt64.ofNat size) (h3 : ω[3] = UInt64.ofNat bin)
    (h7 : ω[7] = UInt64.ofNat 196792) (h120 : rdN μ (sp + 120) 8 = 204984) (h112 : rdN μ (sp + 112) 8 = n)
    (hss : size + sz < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43563 ω μ x 43677 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ω'[2] = UInt64.ofNat (size + sz) ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 9, 11, 12] → ω'[j] = ω[j] := by
  have hAn := hHF nc (Or.inr hFn)
  unfold binCount at hb
  have hn : rdN μ (nc + 8) 4 = (s.hdr nc).next := hrep.next nc hFn
  unfold Al at hAn
  by_cases h0' : (s.hdr nc).next = 0
  · -- the list's last element
    obtain ⟨ω1, μ1, r1, s1, fr1, ww1, g1⟩ := rs_unlink_head0 (p := p) (P := P) (R := R) x ω μ nc
      (196792 + bin * 4) h6 h9 (by rw [hn, h0']) (by omega) (by omega) hw
    have hsec := hrep.sec (bin / 64) (by omega)
    have hpri := hrep.pri
    unfold A0 at hsec hpri
    have hw1 : rdN μ1 (bin / 64 * 8 + 204984 + 1544) 8 = s.secondary (bin / 64) := by
      rw [← hsec, show 196792 + 9736 + 8 * (bin / 64) = bin / 64 * 8 + 204984 + 1544 by omega]
      exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    have hp1 : rdN μ1 206832 8 = s.primary := by
      rw [← hpri]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    obtain ⟨ω2, μ2, r2, c1, c2, cf, cw, c2', c5, cg⟩ := rs_clear (p := p) (P := P) (R := R) x ω1 μ1 sp bin
      (s.secondary (bin / 64)) s.primary size sz n
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 3 (by decide) (by decide)]; exact h3)
      (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by rw [fget g1 10 (by decide) (by decide)]; exact h10)
      (by rw [fget g1 2 (by decide) (by decide)]; exact h2) (by omega) hw1 hp1
      (by rw [← h120]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega))
      (by rw [← h112]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)) hss hsp hsp1 ww1
    refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), ?_, cw, fun a h1 h2 => ?_, c2', c5, fun j hj => ?_⟩
    · refine unregister_rep_last hrep hc (by unfold binCount; omega) h0' ?_ ?_ ?_ ?_ (fun a ha => ?_)
      · rw [← s1]; exact rdN_frame fun j hj => cf _ (by omega) (by omega) (by omega)
      · rw [show 204984 + bin / 64 * 8 + 1544 = bin / 64 * 8 + 204984 + 1544 by omega, c1, ← hsec,
          show 196792 + 9736 + 8 * (bin / 64) = bin / 64 * 8 + 204984 + 1544 by omega]
      · rw [c2, show 204984 + bin / 64 * 8 + 1544 = bin / 64 * 8 + 204984 + 1544 by omega, ← hsec, ← hpri,
          show 196792 + 9736 + 8 * (bin / 64) = bin / 64 * 8 + 204984 + 1544 by omega,
          show 196792 + 10040 = 206832 from rfl]
      · intro a h1 h2 h3 h4; rw [cf a (by omega) (by omega) h4, fr1 a (by omega) h2]
      · have := hHF a ha; unfold Al at this; omega
    · rw [cf a h1 (by omega) (by omega), fr1 a h1 (by omega)]
    · rw [cg j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega),
        g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)]
  · -- a successor
    have hFx := hnx h0'
    have hAx := hHF _ (Or.inr hFx)
    unfold Al at hAx
    obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, e2, e5, g1⟩ := rs_unlink_head (p := p) (P := P) (R := R) x ω μ sp nc
      (196792 + bin * 4) (s.hdr nc).next size sz n h1 h6 h9 h10 h2 hn h112 (by omega) h0' (by omega) (by omega)
      (by omega) hss hsp hsp1 hw
    refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by omega), e2, e5,
      fun j hj => g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
    refine unregister_rep_head hrep hc (by unfold binCount; omega) h0' s1 s2
      (fun a h1 h2 h3 => fr1 a (by omega) (by omega) h3) (by omega) (fun a ha => ?_)
    have := hHF a ha; unfold Al at this; omega

/-- **43583 … 43677**: the old next chunk nc, inside its bin's list, leaves it — the memory holds
    `unregister s nc bin`; ω₂ = size + sz, ω₅ = n. -/
theorem rs_unreg_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base nc bin size sz n : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin ≠ nc) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hpv : F (s.hdr nc).prevL) (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next)
    (hpn : (s.hdr nc).next ≠ 0 → (s.hdr nc).next ≠ (s.hdr nc).prevL) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat nc) (h10 : ω[10] = UInt64.ofNat sz)
    (h2 : ω[2] = UInt64.ofNat size) (h112 : rdN μ (sp + 112) 8 = n)
    (hss : size + sz < 2147483648)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43583 ω μ x 43677 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      ω'[2] = UInt64.ofNat (size + sz) ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 11] → ω'[j] = ω[j] := by
  have hAn := hHF nc (Or.inr hFn)
  have hAp := hHF _ (Or.inr hpv)
  unfold Al at hAn hAp
  have hn : rdN μ (nc + 8) 4 = (s.hdr nc).next := hrep.next nc hFn
  have hp : rdN μ (nc + 12) 4 = (s.hdr nc).prevL := hrep.prevL nc hFn
  have hnxA : (s.hdr nc).next = 0 ∨ ((s.hdr nc).next ≠ 0 ∧ Al base (s.hdr nc).next) := by
    by_cases h0 : (s.hdr nc).next = 0
    · exact Or.inl h0
    · exact Or.inr ⟨h0, hHF _ (Or.inr (hnx h0))⟩
  have hnb : (s.hdr nc).next + 16 < 2147483648 := by
    rcases hnxA with h | ⟨_, h⟩
    · omega
    · unfold Al at h; omega
  obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, e2, e5, g1⟩ := rs_unlink_mid (p := p) (P := P) (R := R) x ω μ sp nc
    (s.hdr nc).prevL (s.hdr nc).next size sz n h1 h6 h10 h2 hn hp h112 (by omega) hnb (by omega)
    (fun h0 => by
      have := hpn h0
      rcases hnxA with h | ⟨_, h⟩
      · exact absurd h h0
      · unfold Al at h; omega) hss hsp hsp1 hw
  refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by
      rcases hnxA with h | ⟨_, h⟩
      · exact Or.inl h
      · unfold Al at h; omega), e2, e5, g1⟩
  refine unregister_rep_mid hrep hc s1 s2 (fun a h1 => fr1 a (by omega)) (by omega)
    (fun h0 => by rcases hnxA with h | ⟨_, h⟩; exact absurd h h0; unfold Al at h; omega)
    hpn (fun a ha => ?_)
  have := hHF a ha; unfold Al at this
  refine ⟨by omega, by omega, by omega, ?_⟩
  rcases hnxA with h | ⟨_, h⟩
  · exact Or.inl h
  · unfold Al at h; omega

/-- **The shrink's merge with the next chunk, 43080 … 43677**: the chunk X (ω₀) of `cur` units,
    keeping n (ω₅); the memory holds the model's `mergeNext s X cur T` for the heap's end
    T = base + 2³⁰, and ω₂ its merged size minus n. -/
theorem shrink_next {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base Xc cur n : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h0 : ω[0] = UInt64.ofNat Xc) (h4 : ω[4] = UInt64.ofNat (base + 1073741824))
    (h12 : ω[12] = UInt64.ofNat (Xc + 32 * cur)) (h2 : ω[2] = UInt64.ofNat (cur - n))
    (h5 : ω[5] = UInt64.ofNat n) (h7 : ω[7] = UInt64.ofNat 196792) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648) (hAX : Al base Xc)
    (hn : n < cur) (hX : Xc + 32 * cur ≤ base + 1073741824) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnc : Xc + 32 * cur < base + 1073741824 → H (Xc + 32 * cur))
    (hfree : Xc + 32 * cur < base + 1073741824 → (s.hdr (Xc + 32 * cur)).size % 2 = 0 →
      NxFree s F base (Xc + 32 * cur) cur)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43080 ω μ x 43677 ω' μ' x 70 ∧
      RepAt μ' (mergeNext s Xc cur (base + 1073741824)).1 H F ∧
      ω'[2] = UInt64.ofNat ((mergeNext s Xc cur (base + 1073741824)).2 - n) ∧ ω'[5] = UInt64.ofNat n ∧
      (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 112 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      ∀ j : Fin 13, j.val ∉ [2, 3, 5, 6, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hw a)
  obtain ⟨hX1, hX2, hX3⟩ := hAX
  unfold mergeNext
  by_cases hlt : Xc + 32 * cur < base + 1073741824
  · rw [if_pos hlt]
    have b1 := rs_br_in (p := p) (P := P) (R := R) x ω μ (Xc + 32 * cur) (base + 1073741824) h12 h4 hlt
      (by omega) hbT
    have hAn := hHF _ (Or.inl (hnc hlt))
    unfold Al at hAn
    have hsz : rdN μ (Xc + 32 * cur + 4) 4 = (s.hdr (Xc + 32 * cur)).size := hrep.size _ (hnc hlt)
    obtain ⟨ω2, r2, c6, c11, c9, g2⟩ := rs_nhdr (p := p) (P := P) (R := R) x ω μ (Xc + 32 * cur)
      (s.hdr (Xc + 32 * cur)).size h12 (by omega) hsz hr
    generalize hW : (s.hdr (Xc + 32 * cur)).size = w at *
    by_cases hu : w % 2 = 1
    · -- the next chunk allocated
      have b2 := rs_br_used (p := p) (P := P) (R := R) x ω2 μ (w % 2) c9 (by omega) (by omega)
      have hwu : (!wordUsed w) = false := by simp [wordUsed, hu]
      rw [if_neg (by simp [hwu])]
      refine ⟨ω2, μ, ((b1.trans r2).trans b2).mono (by omega), hrep, ?_, ?_, hw, fun _ _ _ _ => rfl, fun j hj => ?_⟩
      · rw [fget g2 2 (by decide) (by decide)]; exact h2
      · rw [fget g2 5 (by decide) (by decide)]; exact h5
      · exact g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
    · -- free: it leaves its bin's list and is merged in
      have hu0 : w % 2 = 0 := by omega
      obtain ⟨hFn, hw2, hw3, hss, hhd, hnx, hmid⟩ := hfree hlt hu0
      rw [hW] at hhd hmid hss hw2 hw3
      have b2 := rs_br_free (p := p) (P := P) (R := R) x ω2 μ (by rw [c9, hu0])
      have hwu : (!wordUsed w) = true := by simp [wordUsed, hu0]
      rw [if_pos hwu]
      have hws : wordSize w = w / 2 := rfl
      rw [hws]
      generalize hsz' : w / 2 = sz at *
      have hw' : w = 2 * sz := by omega
      have hB : binDown sz < 2432 := toBin_lt false (Nat.min_le_right _ _)
      -- the bin, into ω₃
      obtain ⟨ω3, μ3, r3, d3, d10, s112, sf3, ww3, g3⟩ : ∃ ω3 μ3, FreeStepsH p R 43101 ω2 μ x 43549 ω3 μ3 x 16 ∧
          ω3[3] = UInt64.ofNat (binDown sz) ∧ ω3[10] = UInt64.ofNat sz ∧ rdN μ3 (sp + 112) 8 = n ∧
          (∀ a, a < 4294967296 → (a < sp + 112 ∨ sp + 120 ≤ a) → μ3.read a = μ.read a) ∧
          (∀ a, μ3.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [3, 5, 9, 10, 11] → ω3[j] = ω2[j] := by
        have e1 : ω2[1] = UInt64.ofNat sp := by rw [fget g2 1 (by decide) (by decide)]; exact h1
        have e5 : ω2[5] = UInt64.ofNat n := by rw [fget g2 5 (by decide) (by decide)]; exact h5
        by_cases hs : sz ≤ 127
        · obtain ⟨ω3, μ3, r, a3, a10, a112, sf, ww, g⟩ := rs_bin_small (p := p) (P := P) (R := R) x ω2 μ sp n sz
            e1 e5 (by rw [c11, hw']) (by omega) (by omega) (by omega) hsp hsp1 hw
          refine ⟨ω3, μ3, r.mono (by omega), by rw [a3, binDown_small (by omega) hs], a10, a112, sf, ww,
            fun j hj => g j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
        · exact rs_bin_big (p := p) (P := P) (R := R) x ω2 μ sp n sz e1 e5 (by rw [c11, hw']) (by omega)
            (by omega) (by omega) hsp hsp1 hw
      have rep3 : RepAt μ3 s H F := hrep.congr_low (fun a ha => sf3 a (by omega) (Or.inl (by omega)))
        (fun a ha => by have := hHF a ha; unfold Al at this; omega)
      have hr3 : ∀ a, μ3.readable a = true := fun a => Memory.readable_of_writable (ww3 a)
      have hhd3 : rdN μ3 (196792 + binDown sz * 4) 4 = s.heads (binDown sz) := by
        have := rep3.heads (binDown sz) (by unfold binCount; omega)
        unfold A0 at this; rw [show 196792 + binDown sz * 4 = 196792 + 4 * binDown sz by omega, this]
      have hhd1 : s.heads (binDown sz) < 2147483648 := by
        rcases hhd with h | h
        · omega
        · unfold Al at h; omega
      have e7 : ω3[7] = UInt64.ofNat 196792 := by
        rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide)]; exact h7
      obtain ⟨ω4, r4, d9, d11, g4⟩ := rs_head (p := p) (P := P) (R := R) x ω3 μ3 (binDown sz)
        (s.heads (binDown sz)) d3 e7 hB hhd3 hhd1 hr3
      have e12 : ω4[12] = UInt64.ofNat (Xc + 32 * cur) := by
        rw [fget g4 12 (by decide) (by decide), fget g3 12 (by decide) (by decide),
          fget g2 12 (by decide) (by decide)]; exact h12
      have e1 : ω4[1] = UInt64.ofNat sp := by
        rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide),
          fget g2 1 (by decide) (by decide)]; exact h1
      have e6 : ω4[6] = UInt64.ofNat (Xc + 32 * cur) := by
        rw [fget g4 6 (by decide) (by decide), fget g3 6 (by decide) (by decide)]; exact c6
      have e10 : ω4[10] = UInt64.ofNat sz := by rw [fget g4 10 (by decide) (by decide)]; exact d10
      have e2 : ω4[2] = UInt64.ofNat (cur - n) := by
        rw [fget g4 2 (by decide) (by decide), fget g3 2 (by decide) (by decide),
          fget g2 2 (by decide) (by decide)]; exact h2
      have k120 : rdN μ3 (sp + 120) 8 = 204984 := by
        rw [← h120]; exact rdN_frame fun j hj => sf3 _ (by omega) (Or.inr (by omega))
      have hfr : ∀ (ω5 : Regs) (μ5 : Memory), (∀ a, a < 4294967296 → 2147483648 ≤ a → μ5.read a = μ3.read a) →
          ∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 112 ∨ sp + 120 ≤ a) → μ5.read a = μ.read a :=
        fun _ _ h a h1 h2 h3 => (h a h1 h2).trans (sf3 a h1 h3)
      by_cases hh : s.heads (binDown sz) = Xc + 32 * cur
      · have b4 := rs_br_head (p := p) (P := P) (R := R) x ω4 μ3 (Xc + 32 * cur) (by rw [d11, hh]) e12
        obtain ⟨ω5, μ5, r5, rep5, ww5, sf5, f2, f5, g5⟩ := rs_unreg_head (p := p) (P := P) (R := R) x ω4 μ3 s H F
          sp base (Xc + 32 * cur) (binDown sz) (cur - n) sz n rep3 hh (by unfold binCount; omega) hFn hHF hnx
          hb0 hbT e1 e6 d9 e10 e2 (by rw [fget g4 3 (by decide) (by decide)]; exact d3) e7 k120 s112
          (by omega) hsp hsp1 ww3
        refine ⟨ω5, μ5, (((((b1.trans r2).trans b2).trans r3).trans r4).trans (b4.trans r5)).mono (by omega),
          rep5, by rw [f2]; congr 1; omega, f5, ww5, hfr ω5 μ5 sf5, fun j hj => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rw [g5 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g4 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
      · obtain ⟨hFp, hpn⟩ := hmid hh
        have b4 := rs_br_mid (p := p) (P := P) (R := R) x ω4 μ3 (Xc + 32 * cur) (s.heads (binDown sz)) d11 e12 hh
          (by omega) hhd1
        obtain ⟨ω5, μ5, r5, rep5, ww5, sf5, f2, f5, g5⟩ := rs_unreg_mid (p := p) (P := P) (R := R) x ω4 μ3 s H F
          sp base (Xc + 32 * cur) (binDown sz) (cur - n) sz n rep3 hh hFn hHF hFp hnx hpn hb0 hbT e1 e6 e10 e2
          s112 (by omega) hsp hsp1 ww3
        refine ⟨ω5, μ5, (((((b1.trans r2).trans b2).trans r3).trans r4).trans (b4.trans r5)).mono (by omega),
          rep5, by rw [f2]; congr 1; omega, f5, ww5, hfr ω5 μ5 sf5, fun j hj => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rw [g5 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g4 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
          g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
  · rw [if_neg hlt]
    have b1 := rs_br_end (p := p) (P := P) (R := R) x ω μ (Xc + 32 * cur) (base + 1073741824) h12 h4
      (by omega) (by omega) hbT
    exact ⟨ω, μ, b1.mono (by omega), hrep, h2, h5, hw, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- **The shrink's last stage, 43677 … the return to `realloc` (40805)**: the tail M = X + 32·n of
    `size` units, with `prev` n, is registered free and the chunk after it records `size` — the
    memory holds the model's `freeFinal`; ω₇ = ptr. -/
theorem shrink_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s2 : State) (H F : Nat → Prop) (sp base Xc n size ptr v5 v6 : Nat)
    (hrep : RepAt μ s2 H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h0 : ω[0] = UInt64.ofNat Xc) (h5 : ω[5] = UInt64.ofNat n)
    (h2 : ω[2] = UInt64.ofNat size) (h4 : ω[4] = UInt64.ofNat (base + 1073741824))
    (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648)
    (hs1 : 1 ≤ size) (hs2 : size ≤ 33554432) (hn : 1 ≤ n) (hn1 : n < 33554432)
    (hAM : Al base (Xc + 32 * n)) (hMt : Xc + 32 * (n + size) ≤ base + 1073741824)
    (hold : s2.heads (binDown size) ≠ Xc + 32 * n)
    (hold1 : s2.heads (binDown size) ≠ 0 → Al base (s2.heads (binDown size)))
    (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnext : Xc + 32 * (n + size) < base + 1073741824 → H (Xc + 32 * (n + size)))
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 43677 ω μ x 40805 ω' μ' x 70 ∧
      RepAt μ' (freeFinal s2 (Xc + 32 * n) n size (base + 1073741824))
        (fun a => H a ∨ a = Xc + 32 * n) (fun a => F a ∨ a = Xc + 32 * n) ∧
      (∀ a, μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 112 ∨ sp + 120 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨hM1, hM2, hM3⟩ := hAM
  have hB : binDown size < 2432 := toBin_lt false (Nat.min_le_right _ _)
  obtain ⟨ω1, μ1, r1, a9, a3, a4, a112, sf1, ww1, g1⟩ := rs_reg_pre (p := p) (P := P) (R := R) x ω μ sp Xc n size
    (base + 1073741824) h1 h0 h5 h2 h4 hs1 (by omega) (by omega) hbT hsp hsp1 hw
  have rep1 : RepAt μ1 s2 H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega)))
    (fun a ha => by have := hHF a ha; unfold Al at this; omega)
  generalize hbin : binDown size = bin at *
  generalize hO : s2.heads bin = old at *
  have hold' : rdN μ1 (bin * 4 + 196792) 4 = old := by
    have := rep1.heads bin (by unfold binCount; omega)
    unfold A0 at this; rw [show bin * 4 + 196792 = 196792 + 4 * bin by omega, this, hO]
  have hold2 : old < 2147483648 := by
    by_cases h0 : old = 0
    · omega
    · have := hold1 h0; unfold Al at this; omega
  have holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ Xc + 32 * n ∨ Xc + 32 * n + 16 ≤ old) := by
    intro h0; have := hold1 h0; unfold Al at this; omega
  have k120 : rdN μ1 (sp + 120) 8 = 204984 := by
    rw [← h120]; exact rdN_frame fun j hj => sf1 _ (by omega) (Or.inr (by omega))
  obtain ⟨ω2, μ2, r2, w1, w2, w3, w4, w5, w6, w7, w8, wf2, ww2, e5, e4, g2⟩ := rs_reg_write (p := p) (P := P)
    (R := R) x ω1 μ1 sp bin (Xc + 32 * n) n size old (base + 1073741824)
    (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a9
    (by rw [fget g1 2 (by decide) (by decide)]; exact h2) a3 a4
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) k120 a112 hB (by omega) (by omega) (by omega)
    (by omega) hold' hold2 holda hsp hsp1 ww1
  have hrep2 := register_rep (μ' := μ2) (M := Xc + 32 * n) (pv := n) (size := size) rep1 (by omega)
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
  have hold3 : old = 0 ∨ old + 32 ≤ base + 1073741824 := by
    by_cases h0 : old = 0
    · exact Or.inl h0
    · have := hold1 h0; unfold Al at this; exact Or.inr (by omega)
  have stk : ∀ a, 2147483648 ≤ a → a < 4294967296 → μ2.read a = μ1.read a := fun a h1 h2 =>
    wf2 a h2 (by omega) (by omega) (by omega) (by omega) (by omega)
  have stk1 : ∀ a, 2147483648 ≤ a → a < 4294967296 → (a < sp + 112 ∨ sp + 120 ≤ a) → μ2.read a = μ.read a :=
    fun a h1 h2 h3 => (stk a h1 h2).trans (sf1 a h2 h3)
  have g12 : ∀ j : Nat, (hj : j < 13) → j ∉ [3, 4, 5, 6, 7, 9, 10, 11, 12] → ω2[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  obtain ⟨ω3, μ3, r3, e1, ef, ew, e7, e0, e1', e5', e6⟩ := rs_epi (p := p) (P := P) (R := R) x ω2 μ2 sp Xc n
    size (base + 1073741824) ptr v5 v6
    (by rw [g12 1 (by decide) (by decide)]; exact h1) (by rw [g12 2 (by decide) (by decide)]; exact h2)
    e5 (by rw [g12 0 (by decide) (by decide)]; exact h0) e4 (by rw [g12 8 (by decide) (by decide)]; exact h8) hp
    (by omega) hbT (by omega)
    (by rw [← s0]; exact rdN_frame fun j hj => stk1 _ (by omega) (by omega) (Or.inr (by omega)))
    (by rw [← s5]; exact rdN_frame fun j hj => stk1 _ (by omega) (by omega) (Or.inr (by omega)))
    (by rw [← s6]; exact rdN_frame fun j hj => stk1 _ (by omega) (by omega) (Or.inr (by omega))) hsp hsp1 ww2
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), ?_, ew,
    fun a h1 h2 h3 => (ef a h1 (by omega)).trans (stk1 a h2 h1 h3), e7, e0, e1', e5', e6⟩
  -- the model's last step
  have hsnd : (register s2 (Xc + 32 * n) n size).2 = size := by rw [register_snd, if_neg (by omega)]
  unfold freeFinal
  rw [hsnd, show Xc + 32 * n + 32 * size = Xc + 32 * (n + size) by omega]
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

end Services.Bootstrap.Alloc
