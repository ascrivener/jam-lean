import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.AllocGrow

/-!
# The binary's `alloc_impl` from the chosen chunk through its unlink, the heap grown
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem alloc_mid_growKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs)
    (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin q b C sz : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648)
    (hrq : req + 1 ≤ sz) (hsz : sz ≤ 33554432) (hCend : C + 32 * sz ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (E : Nat) (hE : (C - s.base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1) = E)
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) h pb - h) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h5 : ω[5] = UInt64.ofNat (196792 + 4 * bin)) (h2 : ω[2] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat q)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 41425 ω μ x 41726 ω' μ' x 150 ∧
      RepAt μ' (unregister { s with allocated := E } C bin) H F ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat (32 * ((C - s.base) / 32)) ∧ ω'[0] = UInt64.ofNat 0 ∧
      rdN μ' (sp + 96) 8 = s.base ∧ rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ rdN μ' (sp + 80) 8 = s.allocated ∧
      rdN μ' (sp + 72) 8 = (C - s.base) / 32 + 1 ∧ rdN μ' (sp + 104) 8 = sz - req - 1 ∧
      rdN μ' (sp + 88) 8 = 204984 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] := by
  have hAC := hHF C (Or.inr hFC)
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨-, ht1, ht2⟩ := growTop_ge (h := h) hR
  unfold Al at hAC
  have hEb : E ≤ 33554432 := by rw [← hE]; split <;> omega
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have halloc : rdN μ 206840 4 = s.allocated := by have := hrep.alloc; unfold A0 at this; exact this
  have hHFl : ∀ a, H a ∨ F a → a + 16 < 2147483648 := fun a ha => by have := hHF a ha; unfold Al at this; omega
  -- the offsets
  obtain ⟨ω1, μ1, r1, a2, a5, a6, a12, s64, s32, s40, s88, fr1, ww1, g1⟩ := al_offs1 (p := p) (P := P) (R := env.rel cap)
    x ω μ sp C s.base s.allocated h1 h10 h8 h120 hbase halloc hal (by omega) (by omega) hsp0 hsp hHTs hSTk hw
  obtain ⟨ω2, μ2, r2, b6, b8, b12, s96, fr2, ww2, g2⟩ := al_offs2 (p := p) (P := P) (R := env.rel cap)
    x ω1 μ1 sp (C - s.base) s.base (by rw [fget g1 1 (by decide) (by decide)]; exact h1) a12 a6 a5
    (by omega) (by omega) hsp0 hsp hHTs hSTk (hw.of_eq ww1)
  generalize hc : (C - s.base) / 32 = c at *
  obtain ⟨ω3, μ3, r3, c6, c3, c0, c11, c8, c5, s72, s104, s80, s56, fr3, ww3, g3⟩ := al_offs3 (p := p) (P := P)
    (R := env.rel cap) x ω2 μ2 sp (s.base / 32) c req sz s.allocated C
    (by rw [fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) b6 b8 b12
    (by rw [fget g2 9 (by decide) (by decide), fget g1 9 (by decide) (by decide)]; exact h9)
    (by rw [fget g2 11 (by decide) (by decide), fget g1 11 (by decide) (by decide)]; exact h11)
    (by rw [fget g2 2 (by decide) (by decide)]; exact a2)
    (by rw [fget g2 10 (by decide) (by decide), fget g1 10 (by decide) (by decide)]; exact h10)
    (by omega) hrq (by omega) (by omega) (by omega) hal (by omega) hsp0 hsp hHTs hSTk ((hw.of_eq ww1).of_eq ww2)
  rw [hE] at c5
  have r4a := al_grow (p := p) (P := P) (R := env.rel cap) x ω3 μ3 s.allocated E
    (by rw [fget g3 2 (by decide) (by decide), fget g2 2 (by decide) (by decide)]; exact a2) c5 hgr (by omega)
  -- the memory so far: only the frame changed
  have lo : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha =>
    ((fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      (fr2 a (by omega) (Or.inl (by omega)))).trans (fr1 a (by omega) (Or.inl (by omega)))
  have rep3 : RepAt μ3 s H F := hrep.congr_low lo hHFl
  have st : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → (a + 8 ≤ sp + 56 ∨ sp + 64 ≤ a) →
      (a + 8 ≤ sp + 72 ∨ sp + 88 ≤ a) → (a + 8 ≤ sp + 104 ∨ sp + 112 ≤ a) → (a + 8 ≤ sp + 96 ∨ sp + 104 ≤ a) →
      rdN μ3 a 8 = rdN μ1 a 8 := fun a h h' e1 e2 e3 e4 => rdN_frame fun j hj =>
    (fr3 _ (by omega) (by omega) (by omega) (by omega)).trans (fr2 _ (by omega) (by omega))
  have k64 : rdN μ3 (sp + 64) 8 = 196792 + 4 * bin := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s64, Num.decodeLE_encodeLE, h5]; simp; omega
  have k40 : rdN μ3 (sp + 40) 8 = q := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s40, Num.decodeLE_encodeLE, h6]; simp; omega
  have k32 : rdN μ3 (sp + 32) 8 = b := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s32, Num.decodeLE_encodeLE, h2]; simp; omega
  have k88 : rdN μ3 (sp + 88) 8 = 204984 := by
    rw [st _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    unfold rdN; rw [s88, Num.decodeLE_encodeLE, h3]; rfl
  have k120 : rdN μ3 (sp + 120) 8 = 204984 := by
    rw [← h120]; exact rdN_frame fun j hj => ((fr3 _ (by omega) (by omega) (by omega) (by omega)).trans
      (fr2 _ (by omega) (by omega))).trans (fr1 _ (by omega) (by omega))
  have h96' : rdN μ3 (sp + 96) 8 = s.base := by
    rw [show rdN μ3 (sp + 96) 8 = rdN μ2 (sp + 96) 8 from rdN_frame fun j hj => fr3 _ (by omega) (by omega)
      (by omega) (by omega)]
    exact rd_enc s96 (by omega)
  obtain ⟨ωg, μg, rg, gE, g7, g9, g4', g0, g3', g10, frg, hpg, hstg, gg⟩ := ag_growKG (p := p) (P := P) env cap hcap x ω3 μ3 sp E
    s.base pb h hbd h48 hhb hbs hR hcost
    (by rw [fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]
        exact h1) c5 h96' k120 hEb (by omega) hsp0 hsp hHTs hSTk hSb
        (HeapPages.of_eq hp fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)))
        (fun a h1 h2 => by rw [ww3, ww2, ww1]; exact hst a h1 h2)
  have tg : ∀ q, sp + 32 ≤ q → (q + 8 ≤ sp + 48 ∨ sp + 56 ≤ q) → q + 8 ≤ sp + 152 → rdN μg q 8 = rdN μ3 q 8 :=
    fun q h h' h'' => rdN_frame fun j hj => frg _ (by omega) (by omega) (by omega) (by omega)
  have repg : RepAt μg { s with allocated := E } H F := rep3.setAlloc gE
    (fun q hq h' => frg q (by omega) (by omega) (by omega) h') (fun q hq => by
      have := hHF q hq; unfold Al at this; omega)
  have gC : ωg[10] = UInt64.ofNat C := by
    rw [g10]; congr 1; exact rd_enc s56 (by omega)
  have ggf : ∀ j : Fin 13, j.val ∉ [6, 8, 10] → ωg[j] = ω3[j] := by
    intro j hj
    rcases j with ⟨j, hj13⟩
    simp only [Fin.getElem_fin]
    by_cases e0 : j = 0
    · subst e0; exact g0
    by_cases e3 : j = 3
    · subst e3; exact g3'
    by_cases e4 : j = 4
    · subst e4; exact g4'
    by_cases e7 : j = 7
    · subst e7; exact g7
    by_cases e9 : j = 9
    · subst e9; exact g9
    have := gg ⟨j, hj13⟩ (by simp at hj ⊢; omega)
    simpa only [Fin.getElem_fin] using this
  have hwg := HeapPages.wrAt hpg (by omega) hstg
  obtain ⟨ω4, μ4, r5, rep4, p48, e8, ww4, fr4, hk4, g4⟩ := al_unreg (p := p) (P := P) (R := env.rel cap) x ωg μg
    { s with allocated := E } H F sp C c bin q b repg hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv (by omega)
    (by rw [fget ggf 1 (by decide) (by decide), fget g3 1 (by decide) (by decide), fget g2 1 (by decide) (by decide),
          fget g1 1 (by decide) (by decide)]; exact h1)
    gC (by rw [fget ggf 3 (by decide) (by decide)]; exact c3)
    (by rw [tg _ (by omega) (by omega) (by omega)]; exact k64) (by rw [tg _ (by omega) (by omega) (by omega)]; exact k40)
    (by rw [tg _ (by omega) (by omega) (by omega)]; exact k32) (by rw [tg _ (by omega) (by omega) (by omega)]; exact k88)
    (by rw [tg _ (by omega) (by omega) (by omega)]; exact k120) hsp0 hsp (by omega) hSTk (fun a ha => by have := hHFT a ha; omega) hwg
  have t4 : ∀ a, sp + 32 ≤ a → a + 8 ≤ sp + 152 → (a + 8 ≤ sp + 48 ∨ sp + 56 ≤ a) → rdN μ4 a 8 = rdN μ3 a 8 :=
    fun a h h' e => (rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega)).trans (tg a h e h')
  refine ⟨ω4, μ4, (((((r1.trans r2).trans r3).trans r4a).trans rg).trans r5).mono (by omega), rep4,
    by rw [fget g4 1 (by decide) (by decide), fget ggf 1 (by decide) (by decide), fget g3 1 (by decide) (by decide),
      fget g2 1 (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1, e8,
    by rw [fget g4 0 (by decide) (by decide), fget ggf 0 (by decide) (by decide)]; exact c0, ?_, p48, ?_, ?_, ?_,
    by rw [t4 _ (by omega) (by omega) (by omega)]; exact k88, by rw [t4 _ (by omega) (by omega) (by omega)]; exact k120,
    HeapPages.of_eq hpg ww4, fun a h1 h2 => by rw [ww4]; exact hstg a h1 h2, fun a h1 h2 h3 => ?_,
    (HKeepG.of_low fun a h1 h2 _ => (frg a (by omega) (by omega) (by omega) (by omega)).trans (lo a h2)).trans hk4, ?_⟩
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact h96'
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s80 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s72 (by omega)
  · rw [t4 _ (by omega) (by omega) (by omega)]; exact rd_enc s104 (by omega)
  · rw [fr4 a h1 h2 (by omega), frg a h1 (by omega) (by omega) (by omega), fr3 a h1 (by omega) (by omega) (by omega),
      fr2 a h1 (by omega), fr1 a h1 (by omega)]
  · exact frame_trans g4 (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) ggf
      (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g3
        (frame_trans (l := [0, 2, 3, 5, 6, 8, 10, 11, 12]) g2 g1 (fun j hj => by simp at hj ⊢; omega)
          (fun j hj => by simp at hj ⊢; omega)) (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega))
      (fun j hj => hj) (fun j hj => by simp at hj ⊢; omega)

/-- `alloc_mid_growKG` for the refine contract (`refineHeap env`). -/
theorem alloc_mid_growK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin q b C sz : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648)
    (hrq : req + 1 ≤ sz) (hsz : sz ≤ 33554432) (hCend : C + 32 * sz ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (E : Nat) (hE : (C - s.base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1) = E)
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) h pb - h) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h5 : ω[5] = UInt64.ofNat (196792 + 4 * bin)) (h2 : ω[2] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat q)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41425 ω μ x 41726 ω' μ' x 150 ∧
      RepAt μ' (unregister { s with allocated := E } C bin) H F ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat (32 * ((C - s.base) / 32)) ∧ ω'[0] = UInt64.ofNat 0 ∧
      rdN μ' (sp + 96) 8 = s.base ∧ rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ rdN μ' (sp + 80) 8 = s.allocated ∧
      rdN μ' (sp + 72) 8 = (C - s.base) / 32 + 1 ∧ rdN μ' (sp + 104) 8 = sz - req - 1 ∧
      rdN μ' (sp + 88) 8 = 204984 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] :=
  alloc_mid_growKG (p := p) (P := P) (refineHeap env) cap hcap x ω μ s H F sp req bin q b C sz hrep hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hrq hsz hCend hal E hE hgr pb h hbd h48 hhb hbs hR hcost h1 h10 h11 h5 h2 h6 h3 h8 h9 h120 hsp0 hsp (S0 := S0) (S1 := S1) hHTs hSTk hSb hp hst hHFT

/-- `alloc_mid_growK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem alloc_mid_grow {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory)
    (s : State) (H F : Nat → Prop) (sp req bin q b C sz : Nat) (hrep : RepAt μ s H F)
    (hcb : s.heads bin = C) (hqb : q * 64 + b = bin) (hq : q < 38) (hb : b < 64)
    (hFC : F C) (hHC : H C) (hHF : ∀ a, H a ∨ F a → Al s.base a)
    (hnx : (s.hdr C).next ≠ 0 → F (s.hdr C).next) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) (hpv : (s.hdr C).prev < 2147483648)
    (hrq : req + 1 ≤ sz) (hsz : sz ≤ 33554432) (hCend : C + 32 * sz ≤ s.base + 1073741824)
    (hal : s.allocated < 2147483648)
    (E : Nat) (hE : (C - s.base) / 32 + 1 + req + (if sz - req - 1 = 0 then 0 else 1) = E)
    (hgr : s.allocated < E) (pb h : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb)
    (hbs : pb < 4294967296) (hR : pagesOf (s.base + 32 * E) ≤ pb)
    (hcost : growTop (pagesOf (s.base + 32 * E)) h pb ≤ h + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat C) (h11 : ω[11] = UInt64.ofNat sz)
    (h5 : ω[5] = UInt64.ofNat (196792 + 4 * bin)) (h2 : ω[2] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat q)
    (h3 : ω[3] = UInt64.ofNat 204984) (h8 : ω[8] = UInt64.ofNat 1) (h9 : ω[9] = UInt64.ofNat req)
    (h120 : rdN μ (sp + 120) 8 = 204984)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) (hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * h) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41425 ω μ x 41726 ω' μ' x 150 ∧
      RepAt μ' (unregister { s with allocated := E } C bin) H F ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[8] = UInt64.ofNat (32 * ((C - s.base) / 32)) ∧ ω'[0] = UInt64.ofNat 0 ∧
      rdN μ' (sp + 96) 8 = s.base ∧ rdN μ' (sp + 48) 8 = (s.hdr C).prev ∧ rdN μ' (sp + 80) 8 = s.allocated ∧
      rdN μ' (sp + 72) 8 = (C - s.base) / 32 + 1 ∧ rdN μ' (sp + 104) 8 = sz - req - 1 ∧
      rdN μ' (sp + 88) 8 = 204984 ∧ rdN μ' (sp + 120) 8 = 204984 ∧
      HeapPages μ' 48 pb (growTop (pagesOf (s.base + 32 * E)) h pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → 2147483648 ≤ a → (a < sp ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => H a ∨ F a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 2, 3, 5, 6, 8, 10, 11, 12] → ω'[j] = ω[j] :=
  alloc_mid_growK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ s H F
    sp req bin q b C sz hrep hcb hqb hq hb hFC hHC hHF hnx hb0 hbT hpv hrq hsz hCend hal E hE hgr
    pb h hbd h48 hhb hbs hR (by unfold hostCostMax; omega) h1 h10 h11 h5 h2 h6 h3 h8 h9 h120 hsp0
    hsp hHTs hSTk hSb hp hst hHFT

end Services.Bootstrap.Alloc
