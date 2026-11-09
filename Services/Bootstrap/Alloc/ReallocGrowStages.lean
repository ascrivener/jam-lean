import Services.Bootstrap.Alloc.ReallocGrowUnreg
import Services.Bootstrap.Alloc.ReallocGrowReg
import Services.Bootstrap.Alloc.ReallocStages

/-!
# The binary's `grow_inplace`, stage by stage

The blocks of `ReallocGrow*` composed against the model's steps: the old next chunk leaves its
bin (`unregister`, 43504 … 44030), and the new size with the free tail and the return
(`freeFinal`, 44030 … 40805).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `RepAt` for fewer headers. -/
theorem RepAt.mono {μ : Memory} {t : State} {H F H' F' : Nat → Prop} (h : RepAt μ t H F)
    (hH : ∀ a, H' a → H a) (hF : ∀ a, F' a → F a) : RepAt μ t H' F' :=
  ⟨h.heads, h.sec, h.pri, h.base, h.alloc, fun a ha => h.prev a (hH a ha), fun a ha => h.size a (hH a ha),
    fun a ha => h.next a (hF a ha), fun a ha => h.prevL a (hF a ha)⟩

/-- The model's `grow_inplace` step on the chunk: it takes `n` units, as an allocation. -/
def growHdr (s : State) (Xc n : Nat) : State :=
  setHdr s Xc (fun h => { h with size := sizeWord n true })

/-- `register_rep` with the memory's frame only below 2³¹ (where the allocator and the heap lie):
    the grow's registration also writes the stack. -/
theorem register_rep_low {μ μ' : Memory} {s : State} {H F : Nat → Prop} {M pv size : Nat}
    (h : RepAt μ s H F) (hs : size ≠ 0) (hB : binDown size < binCount) (hMold : s.heads (binDown size) ≠ M)
    (w1 : rdN μ' (binDown size * 4 + 196792) 4 = M) (w2 : rdN μ' M 4 = pv)
    (w3 : rdN μ' (M + 4) 4 = 2 * size) (w4 : rdN μ' (M + 8) 4 = s.heads (binDown size))
    (w5 : rdN μ' (M + 12) 4 = 0)
    (w6 : s.heads (binDown size) ≠ 0 → rdN μ' (s.heads (binDown size) + 12) 4 = M)
    (w7 : rdN μ' (204984 + binDown size / 64 * 8 + 1544) 8 =
      rdN μ (204984 + binDown size / 64 * 8 + 1544) 8 ||| 2 ^ (binDown size % 64))
    (w8 : rdN μ' 206832 8 = rdN μ 206832 8 ||| 2 ^ (binDown size / 64))
    (wf : ∀ a, a < 2147483648 → (a < binDown size * 4 + 196792 ∨ binDown size * 4 + 196796 ≤ a) →
      (a < M ∨ M + 16 ≤ a) →
      (s.heads (binDown size) = 0 ∨ a < s.heads (binDown size) + 12 ∨ s.heads (binDown size) + 16 ≤ a) →
      (a < 204984 + binDown size / 64 * 8 + 1544 ∨ 204984 + binDown size / 64 * 8 + 1552 ≤ a) →
      (a < 206832 ∨ 206840 ≤ a) → μ'.read a = μ.read a)
    (hMa : 206864 ≤ M) (hM32 : M + 16 < 2147483648)
    (hold : s.heads (binDown size) ≠ 0 → 206864 ≤ s.heads (binDown size) ∧ s.heads (binDown size) + 16 < 2147483648)
    (hHa : ∀ a, H a ∨ F a → 206864 ≤ a ∧ a + 16 < 2147483648 ∧ (a = M ∨ a + 16 ≤ M ∨ M + 16 ≤ a) ∧
      (s.heads (binDown size) = 0 ∨ a = s.heads (binDown size) ∨ a + 16 ≤ s.heads (binDown size) ∨
        s.heads (binDown size) + 16 ≤ a)) :
    RepAt μ' (register s M pv size).1 (fun a => H a ∨ a = M) (fun a => F a ∨ a = M) := by
  generalize hbin : binDown size = bin at *
  generalize hO : s.heads bin = old at *
  have hb38 : bin / 64 < 38 := by unfold binCount at hB; omega
  obtain ⟨hsec, hpri⟩ := register_sec (s := s) (n := M) (prev := pv) hs
  rw [hbin] at hsec hpri
  unfold binCount at hB
  have hbs : bin * 4 + 196792 < 206864 := by omega
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · -- heads
    rw [register_heads hs, hbin]
    unfold A0 at *
    by_cases hbb : b = bin
    · subst hbb; rw [if_pos rfl, show 196792 + 4 * b = b * 4 + 196792 by omega, w1]
    · rw [if_neg hbb, ← h.heads b hb]
      unfold A0
      unfold binCount at hb
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- secondary words
    rw [hsec]
    unfold A0 at *
    by_cases hqq : q = bin / 64
    · subst hqq
      rw [upd_self, show 196792 + 9736 + 8 * (bin / 64) = 204984 + bin / 64 * 8 + 1544 by omega, w7,
        show 204984 + bin / 64 * 8 + 1544 = 196792 + 9736 + 8 * (bin / 64) by omega]
      have := h.sec _ hb38
      unfold A0 at this
      rw [this]
    · rw [upd_ne _ _ hqq, ← h.sec q hq]
      unfold A0
      exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- primary
    rw [hpri]
    have := h.pri
    unfold A0 at *
    rw [show 196792 + 10040 = 206832 from rfl] at this ⊢
    rw [w8, this]
  · -- base
    rw [register_base, ← h.base]
    unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- allocated
    rw [register_allocated, ← h.alloc]
    unfold A0
    exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- prev
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
      by_cases haM : a = M
      · subst haM
        rw [w2, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      · rw [(register_hdr_other haM).1, ← h.prev a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w2, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
  · -- size
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inl ha)
      by_cases haM : a = M
      · subst haM
        rw [w3, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
        simp [sizeWord]
      · rw [(register_hdr_other haM).2.1, ← h.size a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w3, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      simp [sizeWord]
  · -- next
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
      by_cases haM : a = M
      · subst haM
        rw [w4, register_hdr_self hs (by rw [hbin, hO]; exact hMold), hbin, hO]
      · rw [(register_hdr_other haM).2.2, ← h.next a ha]
        exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w4, register_hdr_self hs (by rw [hbin, hO]; exact hMold), hbin, hO]
  · -- prevL
    rcases ha with ha | rfl
    · obtain ⟨a1, a2, a3, a4⟩ := hHa a (Or.inr ha)
      by_cases haM : a = M
      · subst haM
        rw [w5, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]
      · rw [register_prevL hs haM, hbin, hO]
        by_cases hao : a = old ∧ a ≠ 0
        · rw [if_pos hao]
          obtain ⟨rfl, h0⟩ := hao
          exact w6 h0
        · rw [if_neg hao, ← h.prevL a ha]
          exact rdN_frame fun j hj => wf _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · rw [w5, register_hdr_self hs (by rw [hbin, hO]; exact hMold)]


/-- **43933 … 44030**: the old next chunk nc (sp + 80), its bin's head, leaves the list — the
    memory holds `unregister s nc bin`; ω₂ = N, ω₅ = n. -/
theorem rg_unreg_head {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base nc bin n N : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin = nc) (hb : bin < binCount) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h11 : ω[11] = UInt64.ofNat (196792 + bin * 4))
    (h10 : ω[10] = UInt64.ofNat bin) (h7 : ω[7] = UInt64.ofNat 196792) (h3 : ω[3] = UInt64.ofNat 204984)
    (h2 : ω[2] = UInt64.ofNat N) (h5 : ω[5] = UInt64.ofNat n)
    (h80 : rdN μ (sp + 80) 8 = nc) (h64 : rdN μ (sp + 64) 8 = N) (h112 : rdN μ (sp + 112) 8 = n)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43933 ω μ x 44030 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ω'[2] = UInt64.ofNat N ∧ ω'[5] = UInt64.ofNat n ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAn := hHF nc (Or.inr hFn)
  have hnT := hHFT nc (Or.inr hFn)
  unfold binCount at hb
  have hn : rdN μ (nc + 8) 4 = (s.hdr nc).next := hrep.next nc hFn
  unfold Al at hAn
  by_cases h0' : (s.hdr nc).next = 0
  · -- the list's last element
    obtain ⟨ω1, μ1, r1, s1, fr1, ww1, g1⟩ := rg_unlink_head0 (p := p) (P := P) (R := R) x ω μ sp nc
      (196792 + bin * 4) h1 h11 h80 (by rw [hn, h0']) (by omega) (by omega) hsp hsp1 (by omega) (by omega)
      ⟨by omega, by omega⟩ hS hw
    have hsec := hrep.sec (bin / 64) (by omega)
    have hpri := hrep.pri
    unfold A0 at hsec hpri
    have hw1 : rdN μ1 (bin / 64 * 8 + 204984 + 1544) 8 = s.secondary (bin / 64) := by
      rw [← hsec, show 196792 + 9736 + 8 * (bin / 64) = bin / 64 * 8 + 204984 + 1544 by omega]
      exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    have hp1 : rdN μ1 206832 8 = s.primary := by
      rw [← hpri]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)
    obtain ⟨ω2, μ2, r2, c1, c2, cf, cw, c2', c5, cg⟩ := rg_clear (p := p) (P := P) (R := R) x ω1 μ1 sp bin
      (s.secondary (bin / 64)) s.primary n N
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 10 (by decide) (by decide)]; exact h10)
      (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by rw [fget g1 3 (by decide) (by decide)]; exact h3)
      (by omega) hw1 hp1
      (by rw [← h64]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega))
      (by rw [← h112]; exact rdN_frame fun j hj => fr1 _ (by omega) (by omega)) hsp hsp1 (by omega) hS
      (hw.of_eq ww1)
    refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), ?_, fun a => (cw a).trans (ww1 a), fun a h1 h2 => ?_,
      HKeepG.of_low (fun a h1 h2 _ => by rw [cf a (by omega) (by omega) (by omega), fr1 a (by omega) (by omega)]),
      c2', c5,
      fun j hj => ?_⟩
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
    obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, g1⟩ := rg_unlink_head (p := p) (P := P) (R := R) x ω μ sp nc
      (196792 + bin * 4) (s.hdr nc).next h1 h11 h80 hn (by omega) h0' (by omega) (by omega) (by omega) hsp hsp1
      (by omega) ⟨by omega, by omega⟩ (by have := hHFT _ (Or.inr hFx); omega) hS hw
    refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by omega),
      HKeepG.of_low (fun a h1 h2 h3 => fr1 a (by omega) (by omega) (by have := h3 _ (Or.inr hFx); omega)),
      by rw [fget g1 2 (by decide) (by decide)]; exact h2, by rw [fget g1 5 (by decide) (by decide)]; exact h5,
      fun j hj => g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)⟩
    refine unregister_rep_head hrep hc (by unfold binCount; omega) h0' s1 s2
      (fun a h1 h2 h3 => fr1 a (by omega) (by omega) h3) (by omega) (fun a ha => ?_)
    have := hHF a ha; unfold Al at this; omega

/-- **43950 … 44030**: the old next chunk nc (sp + 80), inside its bin's list, leaves it — the
    memory holds `unregister s nc bin`. -/
theorem rg_unreg_mid {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base nc bin : Nat) (hrep : RepAt μ s H F)
    (hc : s.heads bin ≠ nc) (hFn : F nc) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hpv : F (s.hdr nc).prevL) (hnx : (s.hdr nc).next ≠ 0 → F (s.hdr nc).next)
    (hpn : (s.hdr nc).next ≠ 0 → (s.hdr nc).next ≠ (s.hdr nc).prevL) (hb0 : 206864 ≤ base)
    (hbT : base + 1073741824 < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h80 : rdN μ (sp + 80) 8 = nc)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43950 ω μ x 44030 ω' μ' x 30 ∧ RepAt μ' (unregister s nc bin) H F ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ∀ j : Fin 13, j.val ∉ [9, 10, 11] → ω'[j] = ω[j] := by
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
  obtain ⟨ω1, μ1, r1, s1, s2, fr1, ww1, g1⟩ := rg_unlink_mid (p := p) (P := P) (R := R) x ω μ sp nc
    (s.hdr nc).prevL (s.hdr nc).next h1 h80 hn hp (by omega) hnb (by omega)
    (fun h0 => by
      have := hpn h0
      rcases hnxA with h | ⟨_, h⟩
      · exact absurd h h0
      · unfold Al at h; omega) hsp hsp1
    ⟨by omega, by have := hHFT nc (Or.inr hFn); omega⟩ ⟨by omega, by have := hHFT _ (Or.inr hpv); omega⟩
    (fun h0 => by
      have a1 := hHF _ (Or.inr (hnx h0)); have a2 := hHFT _ (Or.inr (hnx h0)); unfold Al at a1; omega) hS hw
  refine ⟨ω1, μ1, r1.mono (by omega), ?_, ww1, fun a h1 h2 => fr1 a h1 (by omega) (by
      rcases hnxA with h | ⟨_, h⟩
      · exact Or.inl h
      · unfold Al at h; omega),
    HKeepG.of_low (fun a h1 h2 h3 => fr1 a (by omega) (by have := h3 _ (Or.inr hpv); omega) (by
      rcases hnxA with h | ⟨h0, _⟩
      · exact Or.inl h
      · have := h3 _ (Or.inr (hnx h0)); omega)), g1⟩
  refine unregister_rep_mid hrep hc s1 s2 (fun a h1 => fr1 a (by omega)) (by omega)
    (fun h0 => by rcases hnxA with h | ⟨_, h⟩; exact absurd h h0; unfold Al at h; omega)
    hpn (fun a ha => ?_)
  have := hHF a ha; unfold Al at this
  refine ⟨by omega, by omega, by omega, ?_⟩
  rcases hnxA with h | ⟨_, h⟩
  · exact Or.inl h
  · unfold Al at h; omega

/-- **The grow's unlink of the old next chunk, 43504 … 44030**: nc (sp + 56, sp + 80), free with
    `sz` units (sp + 40, its size word at sp + 48) and linked in its bin's list, leaves it — the
    memory holds `unregister s nc (binDown sz)`; ω₂ = N (sp + 64), ω₅ = n (sp + 112), ω₆ = avail − n
    (avail at sp + 72). -/
theorem grow_unreg {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base nc sz n N avail : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h3 : ω[3] = UInt64.ofNat 204984)
    (h40 : rdN μ (sp + 40) 8 = sz) (h48 : rdN μ (sp + 48) 8 = 2 * sz) (h112 : rdN μ (sp + 112) 8 = n)
    (h64 : rdN μ (sp + 64) 8 = N) (h72 : rdN μ (sp + 72) 8 = avail) (h56 : rdN μ (sp + 56) 8 = nc)
    (h80 : rdN μ (sp + 80) 8 = nc) (hn : n ≤ avail) (hav : avail < 2147483648)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648) (hHF : ∀ a, H a ∨ F a → Al base a)
    (hsz : (s.hdr nc).size = 2 * sz) (hfree : NxFree s F base nc 0)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43504 ω μ x 44030 ω' μ' x 70 ∧ RepAt μ' (unregister s nc (binDown sz)) H F ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → 2147483648 ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ω'[2] = UInt64.ofNat N ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat (avail - n) ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 6, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr := hw.rd
  obtain ⟨hFn, hw2, hw3, -, hhd, hnx, hmid⟩ := hfree
  rw [hsz, show 2 * sz / 2 = sz by omega] at hhd hmid
  rw [hsz] at hw2 hw3
  have hAn := hHF nc (Or.inr hFn)
  unfold Al at hAn
  have hB : binDown sz < 2432 := toBin_lt false (Nat.min_le_right _ _)
  -- the bin, into ω₁₀
  obtain ⟨ω1, r1, d10, d5, d2, g1⟩ : ∃ ω1, FreeStepsH p R 43504 ω μ x 43910 ω1 μ x 18 ∧
      ω1[10] = UInt64.ofNat (binDown sz) ∧ ω1[5] = UInt64.ofNat n ∧ ω1[2] = UInt64.ofNat N ∧
      ∀ j : Fin 13, j.val ∉ [2, 5, 9, 10, 11] → ω1[j] = ω[j] := by
    by_cases hs : sz ≤ 127
    · obtain ⟨ω1, r, a10, a5, a2, g⟩ := rg_bin_small (p := p) (P := P) (R := R) x ω μ sp sz n N h1 h40 h48 h112 h64
        (by omega) (by omega) hsp hsp1 hS hr
      exact ⟨ω1, r.mono (by omega), by rw [a10, binDown_small (by omega) hs], a5, a2, g⟩
    · exact rg_bin_big (p := p) (P := P) (R := R) x ω μ sp sz n N h1 h40 h48 h112 h64 (by omega) (by omega)
        hsp hsp1 hS hr
  have hhd' : rdN μ (196792 + binDown sz * 4) 4 = s.heads (binDown sz) := by
    have := hrep.heads (binDown sz) (by unfold binCount; omega)
    unfold A0 at this; rw [show 196792 + binDown sz * 4 = 196792 + 4 * binDown sz by omega, this]
  have hhd1 : s.heads (binDown sz) < 2147483648 := by
    rcases hhd with h | h
    · omega
    · unfold Al at h; omega
  obtain ⟨ω2, r2, e11, e12, e6, e9, g2⟩ := rg_head (p := p) (P := P) (R := R) x ω1 μ sp (binDown sz)
    (s.heads (binDown sz)) avail n nc (by rw [fget g1 1 (by decide) (by decide)]; exact h1) d10
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) d5 hB hhd' hhd1 h72 h56 hn hav hsp hsp1
    (by have := hHFT nc (Or.inr hFn); omega) hS hr
  have k : ∀ j : Nat, (hj : j < 13) → j ∉ [2, 5, 6, 9, 10, 11, 12] → ω2[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  by_cases hh : s.heads (binDown sz) = nc
  · have b := rg_br_head (p := p) (P := P) (R := R) x ω2 μ nc (by rw [e12, hh]) e9
    obtain ⟨ω3, μ3, r3, rep3, ww3, sf3, hk3, f2, f5, g3⟩ := rg_unreg_head (p := p) (P := P) (R := R) x ω2 μ s H F
      sp base nc (binDown sz) n N hrep hh (by unfold binCount; omega) hFn hHF hnx hb0 hbT
      (by rw [k 1 (by decide) (by decide)]; exact h1) e11
      (by rw [fget g2 10 (by decide) (by decide)]; exact d10) (by rw [k 7 (by decide) (by decide)]; exact h7)
      (by rw [k 3 (by decide) (by decide)]; exact h3)
      (by rw [fget g2 2 (by decide) (by decide)]; exact d2) (by rw [fget g2 5 (by decide) (by decide)]; exact d5)
      h80 h64 h112 hsp hsp1 hHFT hS hw
    refine ⟨ω3, μ3, (((r1.trans r2).trans b).trans r3).mono (by omega), rep3, ww3, sf3, hk3, f2, f5,
      by rw [fget g3 6 (by decide) (by decide)]; exact e6, fun j hj => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
      g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
      g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
  · obtain ⟨hFp, hpn⟩ := hmid hh
    have b := rg_br_mid (p := p) (P := P) (R := R) x ω2 μ nc (s.heads (binDown sz)) e12 e9 hh (by omega) hhd1
    obtain ⟨ω3, μ3, r3, rep3, ww3, sf3, hk3, g3⟩ := rg_unreg_mid (p := p) (P := P) (R := R) x ω2 μ s H F
      sp base nc (binDown sz) hrep hh hFn hHF hFp hnx hpn hb0 hbT
      (by rw [k 1 (by decide) (by decide)]; exact h1) h80 hsp hsp1 hHFT hS hw
    refine ⟨ω3, μ3, (((r1.trans r2).trans b).trans r3).mono (by omega), rep3, ww3, sf3, hk3,
      by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide)]; exact d2,
      by rw [fget g3 5 (by decide) (by decide), fget g2 5 (by decide) (by decide)]; exact d5,
      by rw [fget g3 6 (by decide) (by decide)]; exact e6, fun j hj => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [g3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
      g2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega),
      g1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]

/-- **The grow's last stage, 44030 … the return to `realloc` (40805)**: the chunk X (sp + 88,
    sp + 120) takes n units; its tail N = X + 32·n of `rem` units (ω₆) with `prev` n, if any, is
    registered free, and the chunk after (X + 32·(n + rem)) records `rem` (or n) — the memory holds
    the model's `freeFinal (growHdr s X n) N n rem T`; ω₇ = ptr. -/
theorem grow_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp base Xc n rem ptr v5 v6 : Nat)
    (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat rem)
    (h2 : ω[2] = UInt64.ofNat (Xc + 32 * n)) (h7 : ω[7] = UInt64.ofNat 196792)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat ptr) (hp : ptr < 18446744073709551616)
    (h88 : rdN μ (sp + 88) 8 = Xc) (h120 : rdN μ (sp + 120) 8 = Xc) (h112 : rdN μ (sp + 112) 8 = n)
    (h72 : rdN μ (sp + 72) 8 = n + rem) (h96 : rdN μ (sp + 96) 8 = base + 1073741824)
    (hb0 : 206864 ≤ base) (hbT : base + 1073741824 < 2147483648)
    (hAX : Al base Xc) (hXH : H Xc) (hs2 : rem ≤ 33554432) (hn : 1 ≤ n) (hn1 : n < 33554432)
    (hMt : Xc + 32 * (n + rem) ≤ base + 1073741824)
    (hold : rem ≠ 0 → (growHdr s Xc n).heads (binDown rem) ≠ Xc + 32 * n)
    (hold1 : rem ≠ 0 → (growHdr s Xc n).heads (binDown rem) ≠ 0 →
      Al base ((growHdr s Xc n).heads (binDown rem)))
    (hHF : ∀ a, H a ∨ F a → Al base a)
    (hnext : Xc + 32 * (n + rem) < base + 1073741824 → H (Xc + 32 * (n + rem)))
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483648 ≤ sp) (hsp1 : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1)
    (hNT : rem ≠ 0 → Xc + 32 * n + 32 ≤ HT)
    (hold1T : rem ≠ 0 → (growHdr s Xc n).heads (binDown rem) ≠ 0 →
      (growHdr s Xc n).heads (binDown rem) + 32 ≤ HT) :
    ∃ ω' μ', FreeStepsH p R 44030 ω μ x 40805 ω' μ' x 80 ∧
      RepAt μ' (freeFinal (growHdr s Xc n) (Xc + 32 * n) n rem (base + 1073741824))
        (fun a => H a ∨ (rem ≠ 0 ∧ a = Xc + 32 * n)) (fun a => F a ∨ (rem ≠ 0 ∧ a = Xc + 32 * n)) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => (H a ∨ F a) ∨ a = Xc + 32 * n ∨ a = (growHdr s Xc n).heads (binDown rem)) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  have hXT := hHFT Xc (Or.inl hXH)
  obtain ⟨hX1, hX2, hX3⟩ := hAX
  -- the new size
  obtain ⟨ω1, μ1, r1, w4, sf1, ww1, g1⟩ := rg_size (p := p) (P := P) (R := R) x ω μ sp Xc n h1 h5 h88
    (by omega) (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hw
  have rep1 : RepAt μ1 (growHdr s Xc n) H F := by
    have := registerAlloc_rep (μ' := μ1) (a := Xc) (pv := (s.hdr Xc).prev) (n := n) hrep hXH
      (by rw [← hrep.prev _ hXH]; exact rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega)))
      (by rw [w4]; unfold sizeWord; simp)
      (fun b h1 h2 => sf1 b (by omega) (by omega)) (by omega)
      (fun b hb => by
        have := hHF b hb; unfold Al at this
        refine ⟨by omega, by omega, by omega⟩)
    exact this
  have stk1 : ∀ a, 2147483648 ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 =>
    sf1 a h2 (Or.inr (by omega))
  have r8 : ∀ a v, rdN μ a 8 = v → sp ≤ a → a + 8 ≤ sp + 152 → rdN μ1 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => stk1 _ (by omega) (by omega)
  have e1 : ω1[1] = UInt64.ofNat sp := by rw [fget g1 1 (by decide) (by decide)]; exact h1
  by_cases hr0 : rem = 0
  · subst hr0
    obtain ⟨ω2, r2, e7, g2⟩ := rg_notail (p := p) (P := P) (R := R) x ω1 μ1 sp (n + 0) e1
      (by rw [fget g1 6 (by decide) (by decide)]; exact h6) (r8 _ _ h72 (by omega) (by omega)) hsp hsp1 hS
      (hw.of_eq ww1).rd
    obtain ⟨ω3, μ3, r3, f1, ef, ew, f7, f0, f1', f5, f6⟩ := rg_epi (p := p) (P := P) (R := R) x ω2 μ1 sp Xc
      (n + 0) n (base + 1073741824) ptr v5 v6
      (by rw [fget g2 1 (by decide) (by decide)]; exact e1) e7
      (by rw [fget g2 5 (by decide) (by decide), fget g1 5 (by decide) (by decide)]; exact h5)
      (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8) hp
      (r8 _ _ h120 (by omega) (by omega)) (r8 _ _ h96 (by omega) (by omega)) (by omega) hbT (by omega)
      (r8 _ _ s0 (by omega) (by omega)) (r8 _ _ s5 (by omega) (by omega)) (r8 _ _ s6 (by omega) (by omega))
      hsp hsp1 (fun hlt => ⟨by omega, by have := hHFT _ (Or.inl (hnext (by omega))); omega⟩) hS (hw.of_eq ww1)
    refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), ?_, fun a => (ew a).trans (ww1 a),
      fun a h1 h2 h3 => (ef a h1 (by omega)).trans (stk1 a h2 h1), ?hk, f7, f0, f1', f5, f6⟩
    case hk =>
      refine (HKeepG.of_low fun a h1 h2 h3 => sf1 a (by omega) (by have := h3 Xc (Or.inl (Or.inl hXH)); omega)).trans (HKeepG.of_low fun a h1 h2 h3 => ?_)
      by_cases hlt : Xc + 32 * (n + 0) < base + 1073741824
      · have := h3 _ (Or.inl (Or.inl (hnext hlt))); exact ef a (by omega) (Or.inr (by omega))
      · exact ef a (by omega) (Or.inl (by omega))
    refine RepAt.mono (H := H) (F := F) ?_ (fun a h => h.elim id (fun h => absurd h.2 (fun _ => h.1 rfl)))
      (fun a h => h.elim id (fun h => absurd h.2 (fun _ => h.1 rfl)))
    rw [freeFinal_zero]
    split
    · rename_i hlt
      refine setPrev_rep rep1 (hnext (by omega)) (f1 (by omega)) (fun b h1 h2 => ef b h1 (Or.inr h2)) (by omega)
        (fun b hb => ?_)
      have := hHF b hb; have := hHF _ (Or.inl (hnext (by omega))); unfold Al at *; omega
    · rename_i hge
      exact rep1.congr (fun b hb => ef b hb (Or.inl (by omega)))
        (fun b hb => by have := hHF b hb; unfold Al at this; omega)
  · -- a tail
    have hB : binDown rem < 2432 := toBin_lt false (Nat.min_le_right _ _)
    obtain ⟨ω2, r2, a10, g2⟩ := rg_reg_pre (p := p) (P := P) (R := R) x ω1 μ1 rem
      (by rw [fget g1 6 (by decide) (by decide)]; exact h6) (by omega) (by omega)
    have hold0 := hold hr0
    have hold10 := hold1 hr0
    have hold1T0 := hold1T hr0
    have hNT0 := hNT hr0
    generalize hbin : binDown rem = bin at *
    generalize hO : (growHdr s Xc n).heads bin = old at *
    have hold' : rdN μ1 (bin * 4 + 196792) 4 = old := by
      have := rep1.heads bin (by unfold binCount; omega)
      unfold A0 at this; rw [show bin * 4 + 196792 = 196792 + 4 * bin by omega, this, hO]
    have hold2 : old < 2147483648 := by
      by_cases h0 : old = 0
      · omega
      · have := hold10 h0; unfold Al at this; omega
    have holda : old ≠ 0 → 206864 ≤ old ∧ (old + 16 ≤ Xc + 32 * n ∨ Xc + 32 * n + 16 ≤ old) := by
      intro h0; have := hold10 h0; unfold Al at this; omega
    have k : ∀ j : Nat, (hj : j < 13) → j ∉ [9, 10, 11] → ω2[j]'hj = ω[j]'hj := fun j hj h => by
      rw [fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
        fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
    obtain ⟨ω3, μ3, r3, w1, w2, w3, w4', w5, w6, w7, w8, wf3, ww3, e7, e5, g3⟩ := rg_reg_write (p := p) (P := P)
      (R := R) x ω2 μ1 sp bin (Xc + 32 * n) n rem old (n + rem)
      (by rw [k 1 (by decide) (by decide)]; exact h1) a10
      (by rw [k 6 (by decide) (by decide)]; exact h6) (by rw [k 2 (by decide) (by decide)]; exact h2)
      (by rw [k 7 (by decide) (by decide)]; exact h7) (by rw [k 3 (by decide) (by decide)]; exact h3)
      (r8 _ _ h112 (by omega) (by omega)) (r8 _ _ h72 (by omega) (by omega)) hB (by omega) (by omega)
      (by omega) (by omega) hold' hold2 holda hsp hsp1 (by omega) (by omega)
      (fun h0 => by have := hold1T0 h0; omega) hS (hw.of_eq ww1)
    have hrep2 := register_rep_low (μ' := μ3) (M := Xc + 32 * n) (pv := n) (size := rem) rep1 hr0
      (by rw [hbin]; unfold binCount; omega) (by rw [hbin, hO]; exact hold0) (by rw [hbin]; exact w1)
      w2 w3 (by rw [hbin, hO]; exact w4') w5 (by rw [hbin, hO]; exact w6) (by rw [hbin]; exact w7)
      (by rw [hbin]; exact w8)
      (by rw [hbin, hO]; intro a h1 h2 h3 h4 h5 h6; exact wf3 a (by omega) h2 h3 h4 h5 h6 (Or.inl (by omega)))
      (by omega) (by omega)
      (by rw [hbin, hO]; intro h0; have := hold10 h0; unfold Al at this; omega)
      (fun a ha => by
        have := hHF a ha; unfold Al at this; rw [hbin, hO]
        refine ⟨by omega, by omega, by omega, ?_⟩
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := hold10 h0; unfold Al at this; omega)
    have hold3 : old = 0 ∨ old + 32 ≤ base + 1073741824 := by
      by_cases h0 : old = 0
      · exact Or.inl h0
      · have := hold10 h0; unfold Al at this; exact Or.inr (by omega)
    have stk3 : ∀ a, 2147483648 ≤ a → a < 4294967296 → (a < sp + 104 ∨ sp + 112 ≤ a) → μ3.read a = μ.read a :=
      fun a h1 h2 h3 => (wf3 a h2 (by omega) (by omega) (by omega) (by omega) (by omega) h3).trans (stk1 a h1 h2)
    have r8' : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ3 a 8 = v := fun a v h h1 h2 => by
      rw [← h]; exact rdN_frame fun j hj => stk3 _ (by omega) (by omega) (Or.inr (by omega))
    obtain ⟨ω4, μ4, r4, f1, ef, ew, f7, f0, f1', f5, f6⟩ := rg_epi (p := p) (P := P) (R := R) x ω3 μ3 sp Xc
      (n + rem) rem (base + 1073741824) ptr v5 v6
      (by rw [fget g3 1 (by decide) (by decide), k 1 (by decide) (by decide)]; exact h1) e7 e5
      (by rw [fget g3 8 (by decide) (by decide), k 8 (by decide) (by decide)]; exact h8) hp
      (r8' _ _ h120 (by omega) (by omega)) (by
        rw [← h96]; exact rdN_frame fun j hj => stk3 _ (by omega) (by omega) (Or.inl (by omega)))
      (by omega) hbT (by omega)
      (r8' _ _ s0 (by omega) (by omega)) (r8' _ _ s5 (by omega) (by omega)) (r8' _ _ s6 (by omega) (by omega))
      hsp hsp1 (fun hlt => ⟨by omega, by have := hHFT _ (Or.inl (hnext (by omega))); omega⟩) hS
      ((hw.of_eq ww1).of_eq ww3)
    refine ⟨ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega), ?_,
      fun a => ((ew a).trans (ww3 a)).trans (ww1 a),
      fun a h1 h2 h3 => (ef a h1 (by omega)).trans (stk3 a h2 h1 h3), ?hk, f7, f0, f1', f5, f6⟩
    case hk =>
      refine (HKeepG.of_low fun a h1 h2 h3 => sf1 a (by omega) (by have := h3 Xc (Or.inl (Or.inl hXH)); omega)).trans (HKeepG.of_low fun a h1 h2 h3 => ?_)
      have e1 : μ4.read a = μ3.read a := by
        by_cases hlt : Xc + 32 * (n + rem) < base + 1073741824
        · have := h3 _ (Or.inl (Or.inl (hnext hlt))); exact ef a (by omega) (Or.inr (by omega))
        · exact ef a (by omega) (Or.inl (by omega))
      rw [e1]
      have := h3 _ (Or.inr (Or.inl rfl))
      have ho : old = 0 ∨ a < old + 12 ∨ old + 16 ≤ a := by
        by_cases h0 : old = 0
        · exact Or.inl h0
        · have := h3 old (Or.inr (Or.inr rfl)); omega
      exact wf3 a (by omega) (by omega) (by omega) ho (by omega) (by omega) (Or.inl (by omega))
    refine RepAt.mono (H := fun a => H a ∨ a = Xc + 32 * n) (F := fun a => F a ∨ a = Xc + 32 * n) ?_
      (fun a h => h.elim Or.inl (fun h => Or.inr h.2)) (fun a h => h.elim Or.inl (fun h => Or.inr h.2))
    have hsnd : (register (growHdr s Xc n) (Xc + 32 * n) n rem).2 = rem := by
      rw [register_snd, if_neg hr0]
    unfold freeFinal
    rw [hsnd, show Xc + 32 * n + 32 * rem = Xc + 32 * (n + rem) by omega]
    split
    · rename_i hlt
      refine setPrev_rep hrep2 (Or.inl (hnext hlt)) (f1 hlt) (fun b h1 h2 => ef b h1 (Or.inr h2)) (by omega)
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
