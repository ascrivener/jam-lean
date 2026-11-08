import Services.Bootstrap.Alloc.ReallocGrowHeapImpl
import Services.Bootstrap.Alloc.ReallocFallbackPre

/-!
# The binary's `realloc_impl`: to the fallback when the host does not grow the heap

When the next chunk is free and large enough but the grown chunk (with its free tail) ends past
the allocated space, `grow_inplace` asks the host to grow the heap (`ecalli 1`, Ω_♊, GP
Appendix B). If the page it needs lies past the heap's bound, the host leaves the heap as it is
(`growTop`), `grow_inplace` gives up (43472 → 43259) and `realloc_impl` goes to the fallback with
the frame as `fallback_pre` leaves it. The model's `growInplace` returns `none` there
(`growInplace_none_grow`), so its `realloc` takes the fallback too.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43472 … 43259**: the heap's new top t below the requested page: the kept ω₇ … ω₁₀ come back
    from the frame, to the fallback. -/
theorem rgh_post_fail' {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp t Rq : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h8 : rdN μ (sp + 8) 8 = Rq)
    (hlt : t < Rq) (hRq : Rq < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat}
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43472 ω μ x 43259 ω' μ x 8 ∧ ω'[1] = ω[1] ∧
      ω'[7] = UInt64.ofNat (rdN μ (sp + 104) 8) ∧ ω'[8] = UInt64.ofNat (rdN μ (sp + 32) 8) ∧
      ω'[9] = UInt64.ofNat (rdN μ (sp + 24) 8) ∧ ω'[10] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧
      ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, Nat.mod_eq_of_lt (show t < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show Rq < 18446744073709551616 by omega), hlt, hr, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- The model's `growInplace` fails when the next chunk is free and large enough but the
    allocated space must grow to E and `grow` refuses it. -/
theorem growInplace_none_grow {grow : Grow} {s : State} {ptr req cur : Nat}
    (hsz : wordSize (s.hdr (ptr - 32)).size = cur) (hlt : cur < req + 1)
    (hin : ptr - 32 + 32 * cur < s.base + 1073741824) (hfree : wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false)
    (hav : req + 1 ≤ cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size)
    (hgr : s.allocated < (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
      (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1))
    (hno : grow s.base ((ptr - 32 + 32 * (req + 1) - s.base) / 32 +
      (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1)) = false) :
    growInplace grow s ptr req = none := by
  unfold growInplace
  simp only [hsz, maxSize_val, Nat.reduceMul]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by simp [hfree]), if_neg (by omega), if_pos hgr,
    if_neg (by simp [hno])]
  rfl

/-- **42980 … 43259, the host not growing the heap**: as `realloc_impl_grow_heap` up to the host
    call, when the page that the end E needs lies past the heap's bound pb: the host leaves the
    heap's top h, and `realloc_impl` reaches the fallback (43259) with the frame, the registers and
    the memory as `fallback_pre` gives them (the memory changed only in the frame), and the heap's
    pages as they were. -/
theorem fallback_pre_grow {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp ptr req cur sz : Nat) (hrep : RepAt μ s H F)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    (hX : Al s.base (ptr - 32)) (hptr : 32 ≤ ptr) (hXH : H (ptr - 32)) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hsz : (s.hdr (ptr - 32)).size = 2 * cur + 1) (hlt : cur < req + 1) (hr : req < 33554431)
    (hc1 : 1 ≤ cur)
    (honc : ptr - 32 + 32 * cur < s.base + 1073741824) (hnc : H (ptr - 32 + 32 * cur))
    (hw : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * sz) (hsz1 : 1 ≤ sz) (hszN : sz ≤ 33554432)
    (hav : req + 1 ≤ cur + sz) (hMt : ptr - 32 + 32 * (cur + sz) ≤ s.base + 1073741824)
    (E : Nat) (hEd : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + sz - (req + 1) = 0 then 0 else 1) = E)
    (hgr : s.allocated < E)
    (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hR : pb < pagesOf (s.base + 32 * E))
    {S0 S1 : Nat} (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 43259 ω' μ' x 120 ∧ RepAt μ' s H F ∧
      HeapPages μ' 48 pb h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (cur - 1) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req := by
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
  -- the prologue
  have hwX : rdN μ (ptr - 28) 4 = 2 * cur + 1 := by
    rw [show ptr - 28 = ptr - 32 + 4 by omega, hrep.size _ hXH, hsz]
  obtain ⟨ω1, μ1, r1, a1, a11, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := refineContract env) x ω μ sp
    ptr (2 * cur + 1) h1 h8 (by omega) (by omega) hwX (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hwr
  have W1 := hwr.of_eq ww1
  have rep1 : RepAt μ1 s H F := hrep.congr_low (fun a ha => sf1 a (by omega) (Or.inl (by omega))) hHFl
  have lo1 : ∀ a n, a + n ≤ 2147483648 → rdN μ1 a n = rdN μ a n := fun a n h =>
    rdN_frame fun j hj => sf1 _ (by omega) (Or.inl (by omega))
  obtain ⟨ω2, r2, b3, b5, g2⟩ := rl_go_grow (p := p) (P := P) (R := refineContract env) x ω1 μ1 req ((2 * cur + 1) / 2 - 1)
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10) a6
    (by rw [fget g1 7 (by decide) (by decide)]; exact h7) (by omega) (by omega)
  have hb1 : rdN μ1 206520 8 = s.base := by have := rep1.base; unfold A0 at this; exact this
  obtain ⟨ω3, μ3, r3, c0, c4, c2, c12, c5, c120, c88, c112, c96, sf3, ww3, g3⟩ := rg_pre (p := p) (P := P)
    (R := refineContract env) x ω2 μ1 (sp - 152) ptr req cur s.base
    (by rw [fget g2 1 (by decide) (by decide)]; exact a1)
    (by rw [fget g2 8 (by decide) (by decide), fget g1 8 (by decide) (by decide)]; exact h8)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10) b5 b3
    (by omega) (by rw [lo1 _ _ (by omega), hrep.size _ hXH, hsz]) hlt (by omega) hb1 hbT (by omega)
    (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W1
  have W3 := W1.of_eq ww3
  have rep3 : RepAt μ3 s H F := rep1.congr_low (fun a ha => sf3 a (by omega) (Or.inl (by omega))) hHFl
  have b4 := rg_br_in (p := p) (P := P) (R := refineContract env) x ω3 μ3 (ptr - 32 + 32 * cur) (s.base + 1073741824) c0 c4 honc
    (by omega) hbT
  have hwn : rdN μ3 (ptr - 32 + 32 * cur + 4) 4 = 2 * sz := by rw [rep3.size _ hnc, hw]
  obtain ⟨ω5, μ5, r5, d5, d11, d80, sf5, ww5, g5⟩ := rg_nhdr (p := p) (P := P) (R := refineContract env) x ω3 μ3 (sp - 152)
    (ptr - 32 + 32 * cur) (2 * sz) (by rw [fget g3 1 (by decide) (by decide)]; exact
      (by rw [fget g2 1 (by decide) (by decide)]; exact a1)) c0 (by omega) hwn (by omega) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ W3
  have W5 := W3.of_eq ww5
  have b6 := rg_br_free (p := p) (P := P) (R := refineContract env) x ω5 μ5 (by rw [d11]; congr 1; omega)
  have k1 : ω5[1] = UInt64.ofNat (sp - 152) := by
    rw [fget g5 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide)]
    exact a1
  have k112 : rdN μ5 (sp - 152 + 112) 8 = req + 1 := by
    rw [← c112]; exact rdN_frame fun j hj => sf5 _ (by omega) (Or.inr (by omega))
  obtain ⟨ω6, r6, f4, f12, f11, g6⟩ := rg_avail_ok (p := p) (P := P) (R := refineContract env) x ω5 μ5 (sp - 152) cur sz (req + 1)
    k1 d5 (by rw [fget g5 12 (by decide) (by decide)]; exact c12) k112 hav (by omega) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ W5.rd
  have hal5 : rdN μ5 206840 4 = s.allocated := by
    rw [rdN_frame (μ := μ1) fun j hj => (sf5 _ (by omega) (Or.inl (by omega))).trans (sf3 _ (by omega) (Or.inl (by omega)))]
    have := rep1.alloc; unfold A0 at this; exact this
  obtain ⟨ω7, μ7, r7, f11', f5', s40, s48, s56, s72, s64, sf7, ww7, g7⟩ := rg_end (p := p) (P := P) (R := refineContract env) x
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
  have K : ∀ j : Nat, (hj : j < 13) → j ∉ [0, 1, 2, 3, 4, 5, 6, 11, 12] → ω7[j]'hj = ω[j]'hj := fun j hj h => by
    rw [fget g7 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g6 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g5 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g3 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g2 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega),
      fget g1 j hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega)]
  have K6 : ω7[6] = UInt64.ofNat (cur - 1) := by
    rw [fget g7 6 (by decide) (by decide), fget g6 6 (by decide) (by decide), fget g5 6 (by decide) (by decide),
      fget g3 6 (by decide) (by decide), fget g2 6 (by decide) (by decide), a6]; congr 1; omega
  -- the host asked for the page of E, past the bound
  have hRq1 : pagesOf (s.base + 32 * E) < 4294967296 := by unfold pagesOf; split <;> omega
  obtain ⟨ω8, μ8, r8, a7', -, -, -, s8', s16', s24', s32', s104', fr8, ww8, g8⟩ :=
    rgh_pre (p := p) (P := P) (R := refineContract env) x ω7 μ7 (sp - 152) s.allocated E s.base K1 f5'
      (by rw [f11', hEd])
      (by rw [fget g7 2 (by decide) (by decide), fget g6 2 (by decide) (by decide),
        fget g5 2 (by decide) (by decide)]; exact c2) K3 hgr hE32 (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ W7
  generalize hRq : pagesOf (s.base + 32 * E) = Rq at *
  have hT : growTop Rq h pb = h := by unfold growTop; rw [if_pos (Or.inr (by omega))]
  have hp8 := HeapPages.of_eq hp7 ww8
  have hst8 : ∀ a, S0 ≤ a → a < S1 → μ8.writable a = true := fun a h1 h2 => by rw [ww8]; exact hst7 a h1 h2
  have r9 := rgh_call (p := p) (P := P) env x ω8 μ8 pb h Rq hbd hp8 h48 hhb hbs a7' (by omega)
    (by rw [hT]; omega)
  rw [hT] at r9
  have hp9 := HeapPages.grow hp8 (t := h) (Nat.le_refl _)
  have hst9 := stack_setPages hst8 (t := h) (by omega)
  have W9 := HeapPages.wrAt hp9 hhb hst9
  obtain ⟨ω10, r10, e1, e7, e8, e9, e10, g10⟩ := rgh_post_fail' (p := p) (P := P) (R := refineContract env) x
    (setR7 ω8 h) (μ8.setPages 48 (h - 48) (some .write)) (sp - 152) h Rq
    (by rw [setR7_other (by decide) (by decide), fget g8 1 (by decide) (by decide)]; exact K1) setR7_self
    (by unfold rdN; rw [Memory.readN_setPages]; exact s8') (by omega) hRq1 (by omega) (by omega)
    ⟨by omega, by omega⟩ W9.rd
  have dec : ∀ v : UInt64, UInt64.ofNat (Num.decodeLE (Num.encodeLE 8 v.toNat)) = v := fun v => by
    rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  have fr : ∀ a, a < 4294967296 → (a < sp - 152 ∨ sp - 24 ≤ a) →
      (μ8.setPages 48 (h - 48) (some .write)).read a = μ1.read a := fun a h1 h2 => by
    rw [Memory.read_setPages, fr8 a h1 (by omega) (by omega), sf7 a h1 (by omega), sf5 a h1 (by omega),
      sf3 a h1 (by omega)]
  have sv : ∀ a, sp - 24 ≤ a → a + 8 ≤ sp →
      (μ8.setPages 48 (h - 48) (some .write)).readN a 8 = μ1.readN a 8 := fun a h1 h2 =>
    Memory.readN_congr fun j hj => fr _ (by omega) (Or.inr (by omega))
  have rep10 : RepAt (μ8.setPages 48 (h - 48) (some .write)) s H F :=
    rep7.congr_low (fun a ha => fr8 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))) hHFl
  refine ⟨ω10, μ8.setPages 48 (h - 48) (some .write),
    ((((((((((r1.trans r2).trans r3).trans b4).trans r5).trans b6).trans r6).trans r7).trans r8).trans r9).trans
      r10).mono (by omega),
    rep10,
    hp9, hst9, fun a h1 h2 => (fr a h1 (by omega)).trans (sf1 a h1 (by omega)),
    by rw [sv _ (by omega) (by omega)]; exact st0, by rw [sv _ (by omega) (by omega)]; exact st5,
    by rw [sv _ (by omega) (by omega)]; exact st6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, setR7_other (by decide) (by decide), fget g8 1 (by decide) (by decide)]; exact K1
  · rw [fget g10 6 (by decide) (by decide), setR7_other (by decide) (by decide), fget g8 6 (by decide) (by decide)]
    exact K6
  · rw [e7]; unfold rdN; rw [Memory.readN_setPages, s104', dec, K 7 (by decide) (by decide)]; exact h7
  · rw [e8]; unfold rdN; rw [Memory.readN_setPages, s32', dec, K 8 (by decide) (by decide)]; exact h8
  · rw [e9]; unfold rdN; rw [Memory.readN_setPages, s24', dec, K 9 (by decide) (by decide)]
  · rw [e10]; unfold rdN; rw [Memory.readN_setPages, s16', dec, K 10 (by decide) (by decide)]; exact h10

end Services.Bootstrap.Alloc
