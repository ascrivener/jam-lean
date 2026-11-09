import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocGrow
import Services.Bootstrap.Alloc.AllocGrow

/-!
# The binary's `grow_inplace`: growing the heap

43421 … 43503: when the grown chunk (and its free tail) ends past the allocated space, `grow_inplace`
asks the host to grow the heap (`ecalli 1`, Ω_♊) to the page that holds that end and records the new
allocated space; then it goes on (43504) as without growth. If the host leaves the heap short, it
gives up (43259).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **43421 … 43470**: the allocated space `al` below the end E: the requested page, the registers
    kept on the stack; at the `ecalli`. -/
theorem rgh_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp al E base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat al)
    (h11 : ω[11] = UInt64.ofNat E) (h2 : ω[2] = UInt64.ofNat base) (h3 : ω[3] = UInt64.ofNat 204984)
    (hlt : al < E) (hE : E ≤ 33554432) (hb : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hS : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43421 ω μ x 43470 ω' μ' x 22 ∧ ω'[7] = UInt64.ofNat (pagesOf (base + 32 * E)) ∧
      ω'[0] = UInt64.ofNat 2008 ∧ ω'[5] = UInt64.ofNat 204984 ∧
      rdN μ' sp 8 = E ∧ rdN μ' (sp + 8) 8 = pagesOf (base + 32 * E) ∧
      μ'.readN (sp + 16) 8 = Num.encodeLE 8 ω[10].toNat ∧ μ'.readN (sp + 24) 8 = Num.encodeLE 8 ω[9].toNat ∧
      μ'.readN (sp + 32) 8 = Num.encodeLE 8 ω[8].toNat ∧ μ'.readN (sp + 104) 8 = Num.encodeLE 8 ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 40 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 5, 7, 11, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h11, h2, h3, show ¬ E ≤ al by omega, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold,
    ↓loadI_fold]
  case post =>
    have e : E * 137438953472 / 4294967296 = 32 * E := by omega
    refine ⟨?_, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff, e]
      congr 1; unfold pagesOf; split <;> split <;> omega
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []; simp only [e]; unfold pagesOf; split <;> split <;> omega
    all_goals try (rd_simp []; rfl)
    · rd_simp []
    · rd_simp [hwr]

/-- **43470, `ecalli 1` (Ω_♊)**, as `ag_callG`.
    Under `refineContractK cap`, any growth whose cost 275 + 121 (t − h) fits in `cap`. -/
theorem rgh_callKG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : 275 + 121 * (growTop Rq h b - h) ≤ cap) :
    FreeStepsH p (env.rel cap) 43470 ω μ x 43472 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 := by
  have hr7 : reg ω 7 = Rq := by
    unfold reg; have : ω.get 7 = ω[7] := rfl; rw [this, h7, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hRq]
  have ht : growTop (reg ω 7) h b = growTop Rq h b := by rw [hr7]
  have hge : h ≤ growTop Rq h b := by unfold growTop; split <;> omega
  exact HeapHost.growHeapK cap hcap env _ (d_43470 (p := p) (P := P)) hb hp h48 hhb hbs ht
    (by unfold Constants.CgasGeminiconst Constants.CgasGeminilinear; omega) FreeStepsH.refl

/-- `rgh_callKG` for the refine contract (`refineHeap env`). -/
theorem rgh_callK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : 275 + 121 * (growTop Rq h b - h) ≤ cap) :
    FreeStepsH p (refineContractK cap env) 43470 ω μ x 43472 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 :=
  rgh_callKG (p := p) (P := P) (refineHeap env) cap hcap x ω μ b h Rq hb hp h48 hhb hbs h7 hRq hcost

/-- `rgh_callKG` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem rgh_callG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : growTop Rq h b ≤ h + 14) :
    FreeStepsH p (env.rel hostCostMax) 43470 ω μ x 43472 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 :=
  rgh_callKG (p := p) (P := P) env hostCostMax (by decide) x ω μ b h Rq hb hp h48 hhb hbs h7 hRq
    (by unfold hostCostMax; omega)

/-- `rgh_callG` for the refine contract (`refineHeap env`). -/
theorem rgh_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : growTop Rq h b ≤ h + 14) :
    FreeStepsH p (refineContract env) 43470 ω μ x 43472 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 :=
  rgh_callG (p := p) (P := P) (refineHeap env) x ω μ b h Rq hb hp h48 hhb hbs h7 hRq hcost

/-- **43472 … 43504**, the heap's new top `t` reaching the requested page: the allocated space
    becomes E; the kept registers come back. -/
theorem rgh_post_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp E t Rq : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h5 : ω[5] = UInt64.ofNat 204984)
    (h0 : rdN μ sp 8 = E) (h8 : rdN μ (sp + 8) 8 = Rq) (hok : Rq ≤ t) (ht : t < 4294967296)
    (hE : E < 4294967296) (hRq : Rq < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 206844 ≤ HT)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43472 ω μ x 43504 ω' μ' x 14 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = UInt64.ofNat (rdN μ (sp + 104) 8) ∧ ω'[8] = UInt64.ofNat (rdN μ (sp + 32) 8) ∧
      ω'[10] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧ ω'[3] = UInt64.ofNat 204984 ∧
      (∀ a, a < 4294967296 → (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [3, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h5, h0, h8, Nat.mod_eq_of_lt (show t < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show Rq < 18446744073709551616 by omega), show ¬ t < Rq by omega, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    · rd_simp []
    · rd_simp [hwr]

/-- 43472 … 43259: the heap's new top below the requested page: to the failure. -/
theorem rgh_post_fail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp t Rq : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h8 : rdN μ (sp + 8) 8 = Rq)
    (hlt : t < Rq) (hRq : Rq < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat}
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hr : RdAt μ HT S0 S1) :
    ∃ ω', FreeStepsH p R 43472 ω μ x 43259 ω' μ x 8 ∧ ω'[1] = ω[1] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, Nat.mod_eq_of_lt (show t < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show Rq < 18446744073709551616 by omega), hlt, hr, ↓rdN_fold, ↓loadI_fold]
  case post => reg_val

/-- **43421 … 43504, the heap grown**: the end E (in units past the base) lies past the allocated
    space `al` and within the heap's bound b (in pages); the host grows the heap from its top h to
    cover it, and the allocated space becomes E.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem rg_heapKG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs)
    (μ : Memory) (sp al E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : 275 + 121 * (growTop (pagesOf (base + 32 * E)) h b - h) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat al) (h11 : ω[11] = UInt64.ofNat E)
    (h2 : ω[2] = UInt64.ofNat base) (h3 : ω[3] = UInt64.ofNat 204984)
    (hlt : al < E) (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 206864 ≤ 4096 * h)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 43421 ω μ x 43504 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[10] = ω[10] ∧ ω'[3] = UInt64.ofNat 204984 ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 40 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] := by
  have hwr := HeapPages.wrAt hp hhb hst
  generalize hRq : pagesOf (base + 32 * E) = Rq at *
  have hRq1 : Rq < 4294967296 := by omega
  obtain ⟨g1', g2', g3'⟩ := growTop_ge (h := h) hR
  generalize hT : growTop Rq h b = t at *
  obtain ⟨ω1, μ1, r1, a7, a0, a5, s0, s8, s16, s24, s32, s104, fr1, ww1, g1⟩ :=
    rgh_pre (p := p) (P := P) (R := env.rel cap) x ω μ sp al E base h1 h5 h11 h2 h3 hlt hE hbase hsp0 hsp
      hS hwr
  rw [hRq] at a7 s8
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  have r2 := rgh_callKG (p := p) (P := P) env cap hcap x ω1 μ1 b h Rq hb hp1 h48 hhb hbs a7 (by omega) (by rw [hT]; exact hcost)
  rw [hT] at r2
  have hp2 := HeapPages.grow hp1 (t := t) (by omega)
  have hst2 := stack_setPages hst1 (t := t) (by omega)
  have hwr2 := HeapPages.wrAt hp2 (by omega) hst2
  obtain ⟨ω3, μ3, r3, e206, e7, e8, e10, e3, fr3, ww3, g3⟩ := rgh_post_ok (p := p) (P := P)
    (R := env.rel cap) x (setR7 ω1 t) (μ1.setPages 48 (t - 48) (some .write)) sp E t Rq
    (by rw [setR7_other (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) setR7_self
    (by rw [setR7_other (by decide) (by decide)]; exact a5)
    (by unfold rdN; rw [Memory.readN_setPages]; exact s0)
    (by unfold rdN; rw [Memory.readN_setPages]; exact s8)
    g1' (by omega) (by omega) hRq1 hsp0 hsp (by omega) hS hwr2
  have dec : ∀ v : UInt64, UInt64.ofNat (Num.decodeLE (Num.encodeLE 8 v.toNat)) = v := fun v => by
    rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), e206, ?_, ?_, ?_, e3,
    fun q h1 h2 h3 h4 => (fr3 q h1 h4).trans (fr1 q h1 h2 h3), HeapPages.of_eq hp2 ww3,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2, ?_⟩
  · rw [e7]; unfold rdN; rw [Memory.readN_setPages, s104]; exact dec _
  · rw [e8]; unfold rdN; rw [Memory.readN_setPages, s32]; exact dec _
  · rw [e10]; unfold rdN; rw [Memory.readN_setPages, s16]; exact dec _
  · intro j hj
    have hj7 : j.val ≠ 7 := by simp at hj; omega
    rw [g3 j (by simp at hj ⊢; omega)]
    simp only [Fin.getElem_fin]
    rw [setR7_other j.isLt hj7]
    exact g1 j (by simp at hj ⊢; omega)

/-- `rg_heapKG` for the refine contract (`refineHeap env`). -/
theorem rg_heapK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp al E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : 275 + 121 * (growTop (pagesOf (base + 32 * E)) h b - h) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat al) (h11 : ω[11] = UInt64.ofNat E)
    (h2 : ω[2] = UInt64.ofNat base) (h3 : ω[3] = UInt64.ofNat 204984)
    (hlt : al < E) (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 206864 ≤ 4096 * h)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 43421 ω μ x 43504 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[10] = ω[10] ∧ ω'[3] = UInt64.ofNat 204984 ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 40 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] :=
  rg_heapKG (p := p) (P := P) (refineHeap env) cap hcap x ω μ sp al E base b h hb h48 hhb hbs hR hcost h1 h5 h11 h2 h3 hlt hE hbase hsp0 hsp (S0 := S0) (S1 := S1) hHTs hS hSb hp hst

/-- `rg_heapKG` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem rg_heapG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X) (ω : Regs)
    (μ : Memory) (sp al E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : growTop (pagesOf (base + 32 * E)) h b ≤ h + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat al) (h11 : ω[11] = UInt64.ofNat E)
    (h2 : ω[2] = UInt64.ofNat base) (h3 : ω[3] = UInt64.ofNat 204984)
    (hlt : al < E) (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 206864 ≤ 4096 * h)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 43421 ω μ x 43504 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[10] = ω[10] ∧ ω'[3] = UInt64.ofNat 204984 ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 40 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] :=
  rg_heapKG (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ sp al E base b
    h hb h48 hhb hbs hR (by unfold hostCostMax; omega) h1 h5 h11 h2 h3 hlt hE hbase hsp0 hsp hHTs
    hS hSb hp hst

/-- `rg_heapG` for the refine contract (`refineHeap env`). -/
theorem rg_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp al E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : growTop (pagesOf (base + 32 * E)) h b ≤ h + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat al) (h11 : ω[11] = UInt64.ofNat E)
    (h2 : ω[2] = UInt64.ofNat base) (h3 : ω[3] = UInt64.ofNat 204984)
    (hlt : al < E) (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 206864 ≤ 4096 * h)
    (hS : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 43421 ω μ x 43504 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧ ω'[10] = ω[10] ∧ ω'[3] = UInt64.ofNat 204984 ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 40 ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 5, 7, 8, 9, 10, 11, 12] → ω'[j] = ω[j] :=
  rg_heapG (p := p) (P := P) (refineHeap env) x ω μ sp al E base b h hb h48 hhb hbs hR hcost h1 h5 h11 h2 h3 hlt hE hbase hsp0 hsp (S0 := S0) (S1 := S1) hHTs hS hSb hp hst

end Services.Bootstrap.Alloc
