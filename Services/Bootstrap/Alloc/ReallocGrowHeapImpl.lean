import Services.Bootstrap.Alloc.ReallocGrowHeap
import Services.Bootstrap.Alloc.ReallocGrowPost
import Services.Bootstrap.Alloc.ReallocGrowRefines

/-!
# The binary's `realloc_impl`, growing in place with the heap grown

As `realloc_impl_grow`, when the grown chunk (and its free tail) ends past the allocated space: the
host grows the heap (`rg_heap`) and the allocated space becomes that end.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem realloc_impl_grow_heapK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory)
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
    (E : Nat) (hEd : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + sz - (req + 1) = 0 then 0 else 1) = E)
    (hgr : s.allocated < E)
    (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pagesOf (s.base + 32 * E) ≤ pb) (hcost : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) h pb - h) ≤ cap)
    -- the free tail
    (hold : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ ptr - 32 + 32 * (req + 1))
    (hold1 : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ 0 →
      Al s.base ((growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1)))))
    (hnext : ptr - 32 + 32 * (cur + sz) < s.base + 1073741824 → H (ptr - 32 + 32 * (cur + sz)))
    {S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h)
    (hold1T : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) + 32 ≤ 4096 * h)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 42980 ω μ x 40805 ω' μ' x 300 ∧
      RepAt μ' (freeFinal (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1))
          (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + sz - (req + 1)) (s.base + 1073741824))
        (fun a => H a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1)))
        (fun a => F a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1))) ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  -- kept out of `omega`'s sight until the tail needs them
  have hT : PLift (_ : Prop) := ⟨hold1T⟩
  clear hold1T
  have hwr := HeapPages.wrAt hp hhb hst
  have hp64 : ptr < 18446744073709551616 := by have := hX.2.2; omega
  have hspA : 2147483648 ≤ sp - 152 := by omega
  have hspB : sp - 152 + 152 < 4294967296 := by omega
  have hSA : S0 ≤ sp - 152 ∧ sp - 152 + 152 ≤ S1 := ⟨by omega, by omega⟩
  have hXT := hHFT _ (Or.inl hXH)
  have hnT := hHFT _ (Or.inl hnc)
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
  obtain ⟨ω1, μ1, r1, a1, a11, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := refineContractK cap env) x ω μ sp
    ptr (2 * cur + 1) h1 h8 (by omega) (by omega) hwX (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hwr
  have W1 := hwr.of_eq ww1
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  have lo1 : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  obtain ⟨ω2, r2, b3, b5, g2⟩ := rl_go_grow (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 req ((2 * cur + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by omega) (by omega)
  have hb1 : rdN μ1 206520 8 = s.base := by have := rep1.base; unfold A0 at this; exact this
  obtain ⟨ω3, μ3, r3, c0, c4, c2, c12, c5, c120, c88, c112, c96, sf3, ww3, g3⟩ := rg_pre (p := p) (P := P)
    (R := refineContractK cap env) x ω2 μ1 (sp - 152) ptr req cur s.base
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10) b5 b3
    (by omega) (by rw [lo1 _ _ (by omega), hrep.size _ hXH, hsz]) hlt (by omega) hb1 hbT (by omega)
    (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W1
  have W3 := W1.of_eq ww3
  have rep3 : RepAt μ3 s H F := rep1.congr_low (fun a ha => sf3 a (by omega) (Or.inl (by omega))) hHFl
  have b4 := rg_br_in (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (ptr - 32 + 32 * cur) (s.base + 1073741824) c0 c4 honc
    (by omega) hbT
  have hwn : rdN μ3 (ptr - 32 + 32 * cur + 4) 4 = 2 * sz := by rw [rep3.size _ hnc, hw]
  obtain ⟨ω5, μ5, r5, d5, d11, d80, sf5, ww5, g5⟩ := rg_nhdr (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 152)
    (ptr - 32 + 32 * cur) (2 * sz) (by rw [fget g3 1 (by decide) (by decide)]; exact
      (by rw [fget g2 1 (by decide) (by decide)]; exact a1)) c0 (by omega) hwn (by omega) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W3
  have W5 := W3.of_eq ww5
  have b6 := rg_br_free (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (by rw [d11]; congr 1; omega)
  have k1 : ω5[1] = UInt64.ofNat (sp - 152) := by
    rw [fget g5 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]
    exact a1
  have k112 : rdN μ5 (sp - 152 + 112) 8 = req + 1 := by
    rw [← c112]; exact rdN_frame fun j hj => sf5 _ (by omega) (Or.inr (by omega))
  obtain ⟨ω6, r6, f4, f12, f11, g6⟩ := rg_avail_ok (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 152) cur sz (req + 1)
    k1 d5 (by rw [fget g5 12 (by decide) (by decide)]; exact c12) k112 hav (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ W5.rd
  have hal5 : rdN μ5 206840 4 = s.allocated := by
    rw [rdN_frame (μ := μ1) fun j hj => (sf5 _ (by omega) (Or.inl (by omega))).trans (sf3 _ (by omega) (Or.inl (by omega)))]
    have := rep1.alloc; unfold A0 at this; exact this
  obtain ⟨ω7, μ7, r7, f11', f5', s40, s48, s56, s72, s64, sf7, ww7, g7⟩ := rg_end (p := p) (P := P) (R := refineContractK cap env) x
    ω6 μ5 (sp - 152) ptr (req + 1) cur sz (ptr - 32 + 32 * cur) (2 * sz) s.base s.allocated
    (by rw [fget g6 1 (by decide) (by decide)]; exact k1)
    (by rw [fget g6 8 (by decide) (by decide), fget g5 8 (by decide) (by decide), fget g3 8 (by decide) (by decide),
      fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    f4 (by rw [fget g6 5 (by decide) (by decide)]; exact d5)
    (by rw [fget g6 0 (by decide) (by decide), fget g5 0 (by decide) (by decide)]; exact c0) f12 k112
    (by rw [fget g6 2 (by decide) (by decide), fget g5 2 (by decide) (by decide)]; exact c2)
    (by rw [fget g6 3 (by decide) (by decide), fget g5 3 (by decide) (by decide), fget g3 3 (by decide) (by decide)]
        exact b3)
    hal5 hal (by omega) (by omega) hav (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ W5
  have W7 := W5.of_eq ww7
  -- registers kept through the checks
  have K0 : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 10, 11, 12] → ω7[j]'hj = ω[j]'hj := fun j hj h => by
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
  -- the heap grown
  have hp7 : HeapPages μ7 48 pb h :=
    HeapPages.of_eq hp fun a => (ww7 a).trans ((ww5 a).trans ((ww3 a).trans (ww1 a)))
  have hst7 : ∀ a, S0 ≤ a → a < S1 → μ7.writable a = true := fun a h1 h2 => by
    rw [ww7, ww5, ww3, ww1]; exact hst a h1 h2
  have hE32 : E ≤ 33554432 := by rw [← hEd]; split <;> omega
  obtain ⟨ω7h, μ7h, rH, gE, k7, k8, -, k3, frH, hpH, hstH, gH⟩ := rg_heapK (p := p) (P := P) env cap hcap x ω7 μ7
    (sp - 152) s.allocated E s.base pb h hbd h48 hhb hbs hR hcost K1 f5' (by rw [f11', hEd])
    (by rw [fget g7 2 (by decide) (by decide), fget g6 2 (by decide) (by decide),
      fget g5 2 (by decide) (by decide)]; exact c2) K3 hgr hE32 (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ hSb hp7 hst7
  obtain ⟨ht0, ht1, ht2⟩ := growTop_ge (h := h) hR
  have hpE := pagesOf_ge (s.base + 32 * E)
  generalize hTt : growTop (pagesOf (s.base + 32 * E)) h pb = t at *
  have htb : t ≤ pb := by omega
  clear ht2
  have W7h : WrAt μ7h (4096 * t) S0 S1 := HeapPages.wrAt hpH htb hstH
  have hHFT' : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * t := fun a ha => by have := hHFT a ha; omega
  have K : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 12] → ω7h[j]'hj = ω[j]'hj :=
    fun j hj h => by
      have : j = 7 ∨ j = 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
      rcases this with rfl | rfl
      · exact k7.trans (K0 7 (by decide) (by decide))
      · exact k8.trans (K0 8 (by decide) (by decide))
  have K1h : ω7h[1] = UInt64.ofNat (sp - 152) := by rw [fget gH 1 (by decide) (by decide)]; exact K1
  have rep7h : RepAt μ7h { s with allocated := E } H F := RepAt.setAlloc rep7 gE
    (fun a h1 h2 => frH a (by omega) (by omega) (by omega) h2)
    (fun b hb => by have := hHF b hb; unfold Al at this; omega)
  have tr : ∀ q v, rdN μ7 (sp - 152 + q) 8 = v → 40 ≤ q → q + 8 ≤ 104 ∨ 112 ≤ q → q + 8 ≤ 152 →
      rdN μ7h (sp - 152 + q) 8 = v := fun q v hv h1 h2 h3 => by
    rw [← hv]; exact rdN_frame fun j hj => frH _ (by omega) (by omega) (by omega) (by omega)
  have k112' : rdN μ7h (sp - 152 + 112) 8 = req + 1 := tr 112 _ (by
    rw [← k112]; exact rdN_frame fun j hj => sf7 _ (by omega) (Or.inr (by omega))) (by omega) (by omega) (by omega)
  have k80 : rdN μ7h (sp - 152 + 80) 8 = ptr - 32 + 32 * cur := tr 80 _ (by
    rw [← d80]; exact rdN_frame fun j hj => sf7 _ (by omega) (Or.inr (by omega))) (by omega) (by omega) (by omega)
  have s40' := tr 40 _ s40 (by omega) (by omega) (by omega)
  have s48' := tr 48 _ s48 (by omega) (by omega) (by omega)
  have s56' := tr 56 _ s56 (by omega) (by omega) (by omega)
  have s64' := tr 64 _ s64 (by omega) (by omega) (by omega)
  have s72' := tr 72 _ s72 (by omega) (by omega) (by omega)
  -- the frame, read back
  have stk1 : ∀ a, a < 4294967296 → sp - 152 + 128 ≤ a → μ7h.read a = μ1.read a := fun a h1 h2 =>
    (((frH a h1 (by omega) (by omega) (by omega)).trans
      (sf7 a h1 (Or.inr (by omega)))).trans (sf5 a h1 (Or.inr (by omega)))).trans
      (sf3 a h1 (Or.inr (by omega)))
  have rd8 : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → sp - 152 + 128 ≤ a →
      a + 8 ≤ sp → rdN μ7h a 8 = v := fun a v h hv h1 h2 => by
    rw [rdN_frame (μ := μ1) fun j hj => stk1 _ (by omega) (by omega)]
    exact rd_enc h hv
  have rd3 : ∀ a v, rdN μ3 a 8 = v → sp - 152 + 88 ≤ a → a + 8 ≤ sp →
      (a + 8 ≤ sp - 152 + 104 ∨ sp - 152 + 112 ≤ a) → rdN μ7h a 8 = v := fun a v h h1 h2 h3 => by
    rw [← h]; exact rdN_frame fun j hj => ((frH _ (by omega) (by omega) (by omega) (by omega)).trans
      (sf7 _ (by omega) (Or.inr (by omega)))).trans (sf5 _ (by omega) (Or.inr (by omega)))
  have hNT : PLift (cur + sz - (req + 1) ≠ 0 → ptr - 32 + 32 * (req + 1) + 32 ≤ 4096 * t) := ⟨fun hr0 => by
    have h' := hEd; rw [if_neg hr0] at h'
    exact tail_le (A := E) hX2 hX1 (by omega) (by omega)⟩
  have hT' : PLift (_ : Prop) := ⟨fun r0 h0 => Nat.le_trans (hT.down r0 h0) (Nat.mul_le_mul_left 4096 ht1)⟩
  clear hEd hgr hR hcost hhb hbs h48 hSb hE32 ht0 ht1 htb hpE gE hTt hT hHFT hal5 hal
  obtain ⟨ω9, μ9, rP, rep9, wwP, sfP, e7, e0, e1, e5, e6⟩ := grow_post (p := p) (P := P)
    (R := refineContractK cap env) x ω7h μ7h { s with allocated := E } H F (sp - 152) s.base (ptr - 32) cur sz
    (req + 1) ptr ω[5].toNat ω[6].toNat rep7h K1h (by rw [K 7 (by decide) (by decide)]; exact h7) k3
    (by rw [K 8 (by decide) (by decide)]; exact h8) hp64 s40' s48' k112' s64' s72' s56' k80
    (rd3 _ _ c88 (by omega) (by omega) (by omega)) (rd3 _ _ c120 (by omega) (by omega) (by omega))
    (rd3 _ _ c96 (by omega) (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact st0 |>.trans (by rw [h0]; rfl)) (by decide)
      (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact st5) (UInt64.toNat_lt _) (by omega) (by omega))
    (rd8 _ _ (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact st6) (UInt64.toNat_lt _) (by omega) (by omega))
    hav hlt (by omega) (by omega) (by omega) hb0 hbT hHF ⟨hX1, hX2, hX3⟩ hXH hw hfree hMt hold hold1 hnext
    hspA hspB hHFT' hSA W7h hNT.down hT'.down
  refine ⟨ω9, μ9, (((((((((r1.trans r2).trans r3).trans b4).trans r5).trans b6).trans r6).trans r7).trans rH).trans
      rP).mono (by omega), rep9,
    HeapPages.of_eq hpH wwP, fun a h1 h2 => by rw [wwP]; exact hstH a h1 h2,
    fun a h1 h2 => ?_, e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩
  rw [sfP a h1 (by omega) (Or.inr (by omega)), stk1 a h1 (by omega)]
  exact sf1 a h1 (Or.inr h2)

/-- `realloc_impl_grow_heapK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem realloc_impl_grow_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory)
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
    (E : Nat) (hEd : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + sz - (req + 1) = 0 then 0 else 1) = E)
    (hgr : s.allocated < E)
    (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pagesOf (s.base + 32 * E) ≤ pb) (hcost : growTop (pagesOf (s.base + 32 * E)) h pb ≤ h + 14)
    -- the free tail
    (hold : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ ptr - 32 + 32 * (req + 1))
    (hold1 : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ 0 →
      Al s.base ((growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1)))))
    (hnext : ptr - 32 + 32 * (cur + sz) < s.base + 1073741824 → H (ptr - 32 + 32 * (cur + sz)))
    {S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h)
    (hold1T : cur + sz - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1)).heads
        (binDown (cur + sz - (req + 1))) + 32 ≤ 4096 * h)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x 300 ∧
      RepAt μ' (freeFinal (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown sz)) (ptr - 32) (req + 1))
          (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + sz - (req + 1)) (s.base + 1073741824))
        (fun a => H a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1)))
        (fun a => F a ∨ (cur + sz - (req + 1) ≠ 0 ∧ a = ptr - 32 + 32 * (req + 1))) ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_impl_grow_heapK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ
    s H F sp ptr req cur sz hrep h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hal hX hptr hXH hHF hsz hlt hr
    hc1 honc hnc hw hfree hav hMt E hEd hgr pb h hbd h48 hhb hbs hR (by unfold hostCostMax; omega)
    hold hold1 hnext hHFT hold1T hS hSb hp hst

end Services.Bootstrap.Alloc
