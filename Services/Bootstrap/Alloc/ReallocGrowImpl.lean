import Services.Bootstrap.Alloc.ReallocGrowStages
import Services.Bootstrap.Alloc.ReallocImpl

/-!
# The binary's `realloc_impl`: the growth in place, whole

`realloc_impl` (42980, called by `realloc` with ω₀ = 1988) for a request above the usable size,
when the next chunk is free and large enough and the allocated space already covers the new end:
its inlined `grow_inplace`, to the return into `realloc` (40805), leaves memory that holds the
model's `growInplace` — given the facts about the heap the stages need.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`growInplace`, unfolded**, for the chunk of `cur` units at ptr − 32, a new request
    `req + 1 > cur`, a free next chunk of `sz` units with `cur + sz ≥ req + 1`, and the allocated
    space covering the new end: the next chunk leaves its bin, the chunk takes `req + 1` units, and
    the rest becomes the free tail. -/
theorem growInplace_eq {grow : Grow} {s : State} {ptr req cur sz : Nat}
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hlt : cur < req + 1)
    (honc : ptr - 32 + 32 * cur < s.base + 1073741824) (hw : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * sz)
    (hav : req + 1 ≤ cur + sz)
    (hE : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + sz - (req + 1) = 0 then 0 else 1) ≤ s.allocated) :
    growInplace grow s ptr req = some (freeFinal (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown sz))
      (ptr - 32) (req + 1)) (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + sz - (req + 1)) (s.base + 1073741824)) := by
  have h1 : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hsz]; unfold wordSize; omega
  have h2 : wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false := by rw [hw]; unfold wordUsed; simp
  have h3 : wordSize (s.hdr (ptr - 32 + 32 * cur)).size = sz := by rw [hw]; unfold wordSize; omega
  unfold growInplace
  simp only [h1, maxSize_val, h2, h3]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by simp), if_neg (by omega)]
  simp only [Nat.reduceMul]
  rw [if_neg (by omega)]
  rfl

/-- **The binary's grow in place refines the model's `growInplace`** (no growth of the heap):
    `realloc_impl` (42980) for a request `req` above the usable size `cur − 1`, the chunk at
    X = ptr − 32 allocated with `cur` units, its next chunk free with `sz` units and
    `cur + sz ≥ req + 1`, and the allocated space covering the new end, reaches the return into
    `realloc` (40805) with memory holding the model's result and ω₇ = ptr, the caller's ω₀, ω₁,
    ω₅, ω₆ restored and the stack from sp up untouched. The hypotheses are the facts about the
    heap the stages read (the invariant provides them). -/
theorem realloc_impl_grow {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp ptr req cur sz : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hlt : cur < req + 1) (hr : req < 33554431)
    (hc1 : 1 ≤ cur)
    -- the next chunk
    (honc : ptr - 32 + 32 * cur < s.base + 1073741824) (hnc : H (ptr - 32 + 32 * cur))
    (hw : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * sz) (hfree : NxFree s F s.base (ptr - 32 + 32 * cur) 0)
    (hav : req + 1 ≤ cur + sz) (hMt : ptr - 32 + 32 * (cur + sz) ≤ s.base + 1073741824)
    (hE : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + sz - (req + 1) = 0 then 0 else 1) ≤ s.allocated)
    -- the free tail
    (hold : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ ptr - 32 + 32 * (req + 1))
    (hold1 : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ 0 →
      Al s.base ((growHdr (unregister s (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1)))))
    (hnext : ptr - 32 + 32 * (cur + sz) < s.base + 1073741824 → H (ptr - 32 + 32 * (cur + sz)))
    (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 250 ∧
      RepAt μ' (freeFinal (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1))
          (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + sz - (req + 1)) (s.base + 1073741824))
        (fun a => H a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1)))
        (fun a => F a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1))) ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hHFl : ∀ b, H b ∨ F b → b + 16 < 2147483648 := fun b hb => by
    have := hHF b hb; unfold Al at this; omega
  have hAn := hHF _ (Or.inl hnc)
  unfold Al at hAn
  have hFn : F (ptr - 32 + 32 * cur) := hfree.1
  have hszN : sz ≤ 33554432 := by have := hfree.2.2.1; rw [hw] at this; omega
  have hsz1 : 1 ≤ sz := by have := hfree.2.1; rw [hw] at this; omega
  -- the prologue
  have hwX : rdN μ (ptr - 28) 4 = 2 * cur + 1 := by
    rw [show ptr - 28 = ptr - 32 + 4 by omega, hrep.size _ hXH, hsz]
  obtain ⟨ω1, μ1, r1, a1, a11, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * cur + 1) h1 h8 (by omega) (by omega) hwX (by omega) hsp hsp1 hwr
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  have lo1 : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  obtain ⟨ω2, r2, b3, b5, g2⟩ := rl_go_grow (p := p) (P := P) (R := R) x ω1 μ1 req ((2 * cur + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by omega) (by omega)
  have hb1 : rdN μ1 206520 8 = s.base := by have := rep1.base; unfold A0 at this; exact this
  obtain ⟨ω3, μ3, r3, c0, c4, c2, c12, c5, c120, c88, c112, c96, sf3, ww3, g3⟩ := rg_pre (p := p) (P := P)
    (R := R) x ω2 μ1 (sp - 152) ptr req cur s.base
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10) b5 b3
    (by omega) (by rw [lo1 _ _ (by omega), hrep.size _ hXH, hsz]) hlt (by omega) hb1 hbT (by omega)
    (by omega) (by omega) ww1
  have rep3 : RepAt μ3 s H F := rep1.congr_low (fun a ha => sf3 a (by omega) (Or.inl (by omega))) hHFl
  have b4 := rg_br_in (p := p) (P := P) (R := R) x ω3 μ3 (ptr - 32 + 32 * cur) (s.base + 1073741824) c0 c4 honc
    (by omega) hbT
  have hwn : rdN μ3 (ptr - 32 + 32 * cur + 4) 4 = 2 * sz := by rw [rep3.size _ hnc, hw]
  obtain ⟨ω5, μ5, r5, d5, d11, d80, sf5, ww5, g5⟩ := rg_nhdr (p := p) (P := P) (R := R) x ω3 μ3 (sp - 152)
    (ptr - 32 + 32 * cur) (2 * sz) (by rw [fget g3 1 (by decide) (by decide)]; exact
      (by rw [fget g2 1 (by decide) (by decide)]; exact a1)) c0 (by omega) hwn (by omega) (by omega) ww3
  have b6 := rg_br_free (p := p) (P := P) (R := R) x ω5 μ5 (by rw [d11]; congr 1; omega)
  have k1 : ω5[1] = UInt64.ofNat (sp - 152) := by
    rw [fget g5 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]
    exact a1
  have k112 : rdN μ5 (sp - 152 + 112) 8 = req + 1 := by
    rw [← c112]; exact rdN_frame fun j hj => sf5 _ (by omega) (Or.inr (by omega))
  obtain ⟨ω6, r6, f4, f12, f11, g6⟩ := rg_avail_ok (p := p) (P := P) (R := R) x ω5 μ5 (sp - 152) cur sz (req + 1)
    k1 d5 (by rw [fget g5 12 (by decide) (by decide)]; exact c12) k112 hav (by omega) (by omega) (by omega)
    (by omega) (fun a => Memory.readable_of_writable (ww5 a))
  have hal5 : rdN μ5 206840 4 = s.allocated := by
    rw [rdN_frame (μ := μ1) fun j hj => (sf5 _ (by omega) (Or.inl (by omega))).trans (sf3 _ (by omega) (Or.inl (by omega)))]
    have := rep1.alloc; unfold A0 at this; exact this
  obtain ⟨ω7, μ7, r7, f11', f5', s40, s48, s56, s72, s64, sf7, ww7, g7⟩ := rg_end (p := p) (P := P) (R := R) x
    ω6 μ5 (sp - 152) ptr (req + 1) cur sz (ptr - 32 + 32 * cur) (2 * sz) s.base s.allocated
    (by rw [fget g6 1 (by decide) (by decide)]; exact k1)
    (by rw [fget g6 8 (by decide) (by decide), fget g5 8 (by decide) (by decide), fget g3 8 (by decide) (by decide),
      fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    f4 (by rw [fget g6 5 (by decide) (by decide)]; exact d5)
    (by rw [fget g6 0 (by decide) (by decide), fget g5 0 (by decide) (by decide)]; exact c0) f12 k112
    (by rw [fget g6 2 (by decide) (by decide), fget g5 2 (by decide) (by decide)]; exact c2)
    (by rw [fget g6 3 (by decide) (by decide), fget g5 3 (by decide) (by decide), fget g3 3 (by decide) (by decide)]
        exact b3)
    hal5 hal (by omega) (by omega) hav (by omega) (by omega) (by omega) (by omega) (by omega) ww5
  have b8 := rg_nogrow (p := p) (P := P) (R := R) x ω7 μ7 s.allocated _ f5' f11' (by omega) hal (by omega)
  -- registers kept through the checks
  have K : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 10, 11, 12] → ω7[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g7 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g6 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g5 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g3 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  have K3 : ω7[3] = UInt64.ofNat 204984 := by
    rw [fget g7 3 (by decide) (by decide), fget g6 3 (by decide) (by decide), fget g5 3 (by decide) (by decide),
      fget g3 3 (by decide) (by decide)]; exact b3
  have K1 : ω7[1] = UInt64.ofNat (sp - 152) := by
    rw [fget g7 1 (by decide) (by decide), fget g6 1 (by decide) (by decide)]; exact k1
  have rep7 : RepAt μ7 s H F := rep3.congr_low (fun a ha =>
    (sf7 a (by omega) (Or.inl (by omega))).trans (sf5 a (by omega) (Or.inl (by omega)))) hHFl
  have k112' : rdN μ7 (sp - 152 + 112) 8 = req + 1 := by
    rw [← k112]; exact rdN_frame fun j hj => sf7 _ (by omega) (Or.inr (by omega))
  have k80 : rdN μ7 (sp - 152 + 80) 8 = ptr - 32 + 32 * cur := by
    rw [← d80]; exact rdN_frame fun j hj => sf7 _ (by omega) (Or.inr (by omega))
  obtain ⟨ω8, μ8, r9, rep8, ww8, sf8, u2, u5, u6, g8⟩ := grow_unreg (p := p) (P := P) (R := R) x ω7 μ7 s H F
    (sp - 152) s.base (ptr - 32 + 32 * cur) sz (req + 1) (ptr - 32 + 32 * (req + 1)) (cur + sz) rep7 K1
    (by rw [K 7 (by decide) (by decide)]; exact h7) K3 s40 s48 k112' s64 s72 s56 k80 hav (by omega)
    hb0 hbT hHF hw hfree (by omega) (by omega) ww7
  -- the frame, read back
  have stk1 : ∀ a, a < 4294967296 → sp - 152 + 128 ≤ a → μ8.read a = μ1.read a := fun a h1 h2 =>
    (((sf8 a h1 (by omega)).trans (sf7 a h1 (Or.inr (by omega)))).trans (sf5 a h1 (Or.inr (by omega)))).trans
      (sf3 a h1 (Or.inr (by omega)))
  have stk3 : ∀ a, a < 4294967296 → sp - 152 + 88 ≤ a → μ8.read a = μ3.read a := fun a h1 h2 =>
    ((sf8 a h1 (by omega)).trans (sf7 a h1 (Or.inr (by omega)))).trans (sf5 a h1 (Or.inr (by omega)))
  have rd8 : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → sp - 152 + 128 ≤ a →
      a + 8 ≤ sp → rdN μ8 a 8 = v := fun a v h hv h1 h2 => by
    rw [rdN_frame (μ := μ1) fun j hj => stk1 _ (by omega) (by omega)]
    exact rd_enc h hv
  have rd3 : ∀ a v, rdN μ3 a 8 = v → sp - 152 + 88 ≤ a → a + 8 ≤ sp → rdN μ8 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => stk3 _ (by omega) (by omega)
  have K8 : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12] → ω8[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g8 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      K j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  obtain ⟨ω9, μ9, r10, rep9, ww9, sf9, e7, e0, e1, e5, e6⟩ := grow_tail (p := p) (P := P) (R := R) x ω8 μ8
    (unregister s (ptr - 32 + 32 * cur) (binDown sz)) H F (sp - 152) s.base (ptr - 32) (req + 1)
    (cur + sz - (req + 1)) ptr ω[5].toNat ω[6].toNat rep8
    (by rw [fget g8 1 (by decide) (by decide)]; exact K1) u5 u6 u2
    (by rw [K8 7 (by decide) (by decide)]; exact h7)
    (by rw [fget g8 3 (by decide) (by decide)]; exact K3)
    (by rw [K8 8 (by decide) (by decide)]; exact h8) (by omega)
    (rd3 _ _ c88 (by omega) (by omega)) (rd3 _ _ c120 (by omega) (by omega)) (rd3 _ _ c112 (by omega) (by omega))
    (by rw [show req + 1 + (cur + sz - (req + 1)) = cur + sz by omega]
        rw [← s72]; exact rdN_frame fun j hj => sf8 _ (by omega) (by omega))
    (rd3 _ _ c96 (by omega) (by omega)) hb0 hbT ⟨hX1, hX2, hX3⟩ hXH (by omega) (by omega) (by omega)
    (by rw [show req + 1 + (cur + sz - (req + 1)) = cur + sz by omega]; exact hMt)
    hold hold1 hHF
    (by rw [show req + 1 + (cur + sz - (req + 1)) = cur + sz by omega]; exact hnext)
    (rd8 _ _ (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact st0 |>.trans (by rw [h0]; rfl)) (by decide)
      (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact st5) (UInt64.toNat_lt _) (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact st6) (UInt64.toNat_lt _) (by omega) (by omega))
    (by omega) (by omega) ww8
  refine ⟨ω9, μ9, ((((((((((r1.trans r2).trans r3).trans b4).trans r5).trans b6).trans r6).trans r7).trans b8).trans
      r9).trans r10).mono (by omega), rep9, ww9, fun a h1 h2 => ?_, e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩
  rw [sf9 a h1 (by omega) (Or.inr (by omega)), stk1 a h1 (by omega)]
  exact sf1 a h1 (Or.inr h2)

end Services.Bootstrap.Alloc
