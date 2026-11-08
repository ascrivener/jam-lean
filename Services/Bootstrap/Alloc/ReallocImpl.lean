import Services.Bootstrap.Alloc.ReallocStages

/-!
# The binary's `realloc_impl`: the shrink, whole

`realloc_impl` (42980, called by `realloc` with ω₀ = 1988) for a request below the usable size:
its inlined `shrink_inplace`, to the return into `realloc` (40805), leaves memory that holds the
model's `shrink s ptr req` — given the facts about the heap the stages need, which the invariant
provides.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The model's `shrink`'s first step: the chunk keeps `req + 1` units, as an allocation. -/
def shrinkHdr (s : State) (ptr req : Nat) : State :=
  setHdr s (ptr - 32) (fun h => { h with size := sizeWord (req + 1) true })

theorem mergeNext_snd_ge {s : State} {c sz T : Nat} : sz ≤ (mergeNext s c sz T).2 := by
  unfold mergeNext; split
  · split
    · simp only; omega
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **`shrink`, unfolded**, for the chunk of `cur` units at ptr − 32 and a new request
    `req + 1 < cur`: the merge with the next chunk, then the free tail. -/
theorem shrink_eq {s : State} {ptr req cur : Nat} (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1)
    (hr : req + 1 < cur) :
    shrink s ptr req =
      freeFinal (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1
        (ptr - 32 + 32 * (req + 1)) (req + 1)
        ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1))
        (s.base + 1073741824) := by
  have hc : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hsz]; unfold wordSize; omega
  unfold shrink
  dsimp only
  rw [hc, if_neg (by omega), maxSize_val]
  rfl

/-- **The binary's shrink refines the model's `shrink`**: `realloc_impl` (42980) for a request
    `req` of 1 … `cur − 2` units, the chunk at ptr − 32 allocated with `cur` units, reaches the
    return into `realloc` (40805) with memory holding `shrink s ptr req` and ω₇ = ptr, the caller's
    ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. The hypotheses are the facts about
    the heap the stages read (the invariant provides them). -/
theorem realloc_impl_shrink {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp ptr req cur : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hr0 : req ≠ 0) (hr : req + 1 < cur) (hc : cur ≤ 33554432)
    (hcur : ptr - 32 + 32 * cur ≤ s.base + 1073741824)
    -- the merge
    (hnc : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur))
    (hfree : ptr - 32 + 32 * cur < s.base + 1073741824 →
      ((shrinkHdr s ptr req).hdr (ptr - 32 + 32 * cur)).size % 2 = 0 →
      NxFree (shrinkHdr s ptr req) F s.base (ptr - 32 + 32 * cur) cur)
    -- the free tail
    (htot : (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 ≤ 33554432)
    (hMt : ptr - 32 + 32 * (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 ≤
      s.base + 1073741824)
    (hold : (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1.heads
      (binDown ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1))) ≠
        ptr - 32 + 32 * (req + 1))
    (hold1 : (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1.heads
      (binDown ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1))) ≠ 0 →
      Al s.base ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1.heads
        (binDown ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1)))))
    (hnext : ptr - 32 + 32 * (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 <
      s.base + 1073741824 →
      H (ptr - 32 + 32 * (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2))
    {HT S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT) (hMT : ptr - 32 + 32 * (req + 1) + 32 ≤ HT)
    (hold1T : (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1.heads
      (binDown ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1))) ≠ 0 →
      (mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).1.heads
        (binDown ((mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824)).2 - (req + 1))) + 32 ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧
      RepAt μ' (shrink s ptr req) (fun a => H a ∨ a = ptr - 32 + 32 * (req + 1))
        (fun a => F a ∨ a = ptr - 32 + 32 * (req + 1)) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hHFl : ∀ b, H b ∨ F b → b + 16 < 2147483648 := fun b hb => by
    have := hHF b hb; unfold Al at this; omega
  generalize hXd : ptr - 32 = Xc at *
  have hpX : ptr = Xc + 32 := by omega
  subst hpX
  have hXd' : Xc + 32 - 32 = Xc := by omega
  -- the prologue
  have hwX : rdN μ (Xc + 32 - 28) 4 = 2 * cur + 1 := by
    rw [show Xc + 32 - 28 = Xc + 4 by omega, hrep.size _ hXH, hsz]
  obtain ⟨ω1, μ1, r1, a1, a11, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    (Xc + 32) (2 * cur + 1) h1 h8 (by omega) (by omega) hwX (by omega) hsp hsp1
    ⟨by omega, by have := hHFT _ (Or.inl hXH); omega⟩ hS hw
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  obtain ⟨ω2, r2, b3, b5, g2⟩ := rl_go_shrink (p := p) (P := P) (R := R) x ω1 μ1 req ((2 * cur + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) hr0 (by omega) (by omega)
  have hb1 : rdN μ1 206520 8 = s.base := by
    have := rep1.base; unfold A0 at this; exact this
  obtain ⟨ω3, μ3, r3, c0, c4, c12, c2, cw4, c120, sf3, ww3, g3⟩ := rs_hdr (p := p) (P := P) (R := R) x ω2 μ1
    (sp - 152) (Xc + 32) (req + 1) cur s.base
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8) b5 b3 (by omega)
    (by
      rw [hXd', ← hsz, ← hrep.size _ hXH]
      exact rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega)))
    hr hb1 hbT (by omega) (by omega) (by omega) (by have := hHFT _ (Or.inl hXH); omega)
    ⟨by omega, by have := hHFT _ (Or.inl hXH); omega⟩ ⟨by omega, by omega⟩ (hw.of_eq ww1)
  rw [hXd'] at c0 c12 cw4 sf3
  -- the chunk's new size, against memory
  have rep3 : RepAt μ3 (shrinkHdr s (Xc + 32) req) H F := by
    have := registerAlloc_rep (μ' := μ3) (a := Xc) (pv := (s.hdr Xc).prev) (n := req + 1) rep1 hXH
      (by rw [← rep1.prev _ hXH]; exact rdN_frame fun j hj => sf3 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
      (by rw [cw4]; unfold sizeWord; simp)
      (fun b h1 h2 => sf3 b (by omega) (by omega) (Or.inl (by omega))) (by omega)
      (fun b hb => by
        have := hHF b hb; unfold Al at this
        refine ⟨by omega, by omega, by omega⟩)
    unfold shrinkHdr; rw [hXd']; exact this
  -- the merge
  have hHF' : ∀ a, H a ∨ F a → Al (shrinkHdr s (Xc + 32) req).base a := hHF
  obtain ⟨ω4, μ4, r4, rep4, d2, d5, ww4, sf4, g4⟩ := shrink_next (p := p) (P := P) (R := R) x ω3 μ3
    (shrinkHdr s (Xc + 32) req) H F (sp - 152) s.base Xc cur (req + 1) rep3
    (by rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]; exact a1) c0 c4 c12 c2
    (by rw [fget g3 5 (by decide) (by decide)]; exact b5)
    (by rw [fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide),
      fget g1 7 (by decide) (by decide)]; exact h7) c120 hb0 hbT ⟨hX1, hX2, hX3⟩ hr hcur hHF
    hnc hfree (by omega) (by omega) hHFT ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww3)
  generalize hm : mergeNext (shrinkHdr s (Xc + 32) req) Xc cur (s.base + 1073741824) = m at *
  have hm2 : cur ≤ m.2 := by rw [← hm]; exact mergeNext_snd_ge
  -- the free tail and the return
  have stk31 : ∀ a, a < 4294967296 → sp - 152 + 128 ≤ a → μ4.read a = μ1.read a := fun a h1 h2 =>
    (sf4 a h1 (by omega) (Or.inr (by omega))).trans (sf3 a h1 (Or.inr (by omega)) (Or.inr (by omega)))
  have stk3 : ∀ a, a < 4294967296 → sp ≤ a → μ4.read a = μ.read a := fun a h1 h2 =>
    (stk31 a h1 (by omega)).trans (sf1 a h1 (Or.inr h2))
  have rd8 : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → sp - 152 + 128 ≤ a →
      a + 8 ≤ sp → rdN μ4 a 8 = v := fun a v h hv h1 h2 => by
    rw [rdN_frame (μ := μ1) fun j hj => stk31 _ (by omega) (by omega)]
    exact rd_enc h hv
  obtain ⟨ω5, μ5, r5, rep5, ww5, sf5, e7, e0, e1, e5, e6⟩ := shrink_tail (p := p) (P := P) (R := R) x ω4 μ4 m.1 H F
    (sp - 152) s.base Xc (req + 1) (m.2 - (req + 1)) (Xc + 32) ω[5].toNat ω[6].toNat rep4
    (by rw [fget g4 1 (by decide) (by decide), fget g3 1 (by decide) (by decide),
      fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g4 0 (by decide) (by decide)]; exact c0) d5 d2
    (by rw [fget g4 4 (by decide) (by decide)]; exact c4)
    (by rw [fget g4 7 (by decide) (by decide), fget g3 7 (by decide) (by decide), fget g2 7 (by decide) (by decide),
      fget g1 7 (by decide) (by decide)]; exact h7)
    (by rw [fget g4 8 (by decide) (by decide), fget g3 8 (by decide) (by decide), fget g2 8 (by decide) (by decide),
      fget g1 8 (by decide) (by decide)]; exact h8) (by omega)
    (by rw [← c120]; exact rdN_frame fun j hj => sf4 _ (by omega) (by omega) (Or.inr (by omega)))
    hb0 hbT (by omega) (by omega) (by omega) (by omega)
    ⟨by omega, by omega, by omega⟩ (by rw [show req + 1 + (m.2 - (req + 1)) = m.2 by omega]; exact hMt)
    hold hold1 hHF (by rw [show req + 1 + (m.2 - (req + 1)) = m.2 by omega]; exact hnext)
    (rd8 _ _ (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact st0 |>.trans (by rw [h0]; rfl)) (by decide)
      (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact st5) (UInt64.toNat_lt _) (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact st6) (UInt64.toNat_lt _) (by omega) (by omega))
    (by omega) (by omega) hMT hold1T hHFT ⟨by omega, by omega⟩ (((hw.of_eq ww1).of_eq ww3).of_eq ww4)
  refine ⟨ω5, μ5, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), ?_,
    fun a => (ww5 a).trans ((ww4 a).trans ((ww3 a).trans (ww1 a))),
    fun a h1 h2 => (sf5 a h1 (by omega) (Or.inr (by omega))).trans (stk3 a h1 h2), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩
  rw [shrink_eq (cur := cur) (by rw [hXd']; exact hsz) hr, hXd', hm]
  exact rep5

end Services.Bootstrap.Alloc
