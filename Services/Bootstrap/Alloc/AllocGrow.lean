import Services.Bootstrap.Alloc.AllocWrap

/-!
# The binary's `alloc_impl`: growing the heap

41517 … 41589: when the allocation ends past the allocated space, `alloc_impl` asks the host to grow
the heap (`ecalli 1`, Ω_♊) to the page that holds the allocation's end, and records the new
allocated space.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The pages covering the first x octets: ⌈x / 4096⌉. -/
def pagesOf (x : Nat) : Nat := x / 4096 + (if x % 4096 = 0 then 0 else 1)

theorem ag_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp E base : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E)
    (h96 : rdN μ (sp + 96) 8 = base) (hE : E ≤ 33554432) (hb : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41517 ω μ x 41556 ω' μ' x 20 ∧ ω'[7] = UInt64.ofNat (pagesOf (base + 32 * E)) ∧
      ω'[6] = UInt64.ofNat (pagesOf (base + 32 * E)) ∧
      μ'.readN sp 8 = Num.encodeLE 8 ω[3].toNat ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp + 16) 8 = Num.encodeLE 8 ω[4].toNat ∧ μ'.readN (sp + 24) 8 = Num.encodeLE 8 ω[9].toNat ∧
      μ'.readN (sp + 48) 8 = Num.encodeLE 8 ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [6, 7, 8] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h96, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    have e : E * 137438953472 / 4294967296 = 32 * E := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff, e]
      congr 1; unfold pagesOf; split <;> split <;> omega
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some', Nat.reduceEqDiff, e]
      congr 1; unfold pagesOf; split <;> split <;> omega
    all_goals try (rd_simp []; rfl)
    · rd_simp []
    · rd_simp [hwr]

/-- **41558 … 41589**, the heap's new top `t` reaching the requested page `R`: the allocated space
    becomes E; the saved registers come back. -/
theorem ag_post_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp E t Rq : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h6 : ω[6] = UInt64.ofNat Rq)
    (h5 : ω[5] = UInt64.ofNat E) (h120 : rdN μ (sp + 120) 8 = 204984) (hok : Rq ≤ t) (ht : t < 4294967296)
    (hE : E < 4294967296)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 41558 ω μ x 41589 ω' μ' x 12 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = UInt64.ofNat (rdN μ (sp + 48) 8) ∧ ω'[9] = UInt64.ofNat (rdN μ (sp + 24) 8) ∧
      ω'[4] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧ ω'[10] = UInt64.ofNat (rdN μ (sp + 56) 8) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧ ω'[3] = UInt64.ofNat (rdN μ sp 8) ∧
      (∀ a, a < 4294967296 → (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [0, 3, 4, 7, 9, 10] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h6, h5, h120, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (show Rq < 18446744073709551616 by omega),
    show ¬ t < Rq by omega, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rd_simp []; simp only [Nat.reducePow, Nat.reduceMul]; omega
    all_goals try reg_val
    · rd_simp []
    · rd_simp [hwr]

/-- **41556, `ecalli 1` (Ω_♊)**, with every page writable: the heap's top is already its bound b,
    the call returns b in ω₇ and the pages stay writable. -/
theorem ag_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (a b Rq : Nat) (hb : heapBounds env.code = (a, b)) (hab : a ≤ b) (hbs : b < 4294967296)
    (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616) (hw : ∀ a, μ.writable a = true) :
    FreeStepsH p (refineContract env) 41556 ω μ x 41558 (setR7 ω b) (μ.setPages a (b - a) (some .write)) x 1 := by
  have ht : growTop (reg ω 7) b b = b := by unfold growTop; rw [if_pos (by omega)]
  have hp : HeapPages μ a b b := fun q h1 h2 => by
    have h' : (μ.pages.get? q == some .write) = true := by
      have := hw (q * pageSize); unfold Memory.writable at this
      rwa [Nat.mul_div_cancel _ (show 0 < pageSize by unfold pageSize; decide)] at this
    rw [h']; simp [h2]
  rw [← ht]
  exact FreeStepsH.growHeap env _ (d_41556 (p := p) (P := P)) hb hp hab (Nat.le_refl b) hbs rfl
    (by rw [ht]; simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; decide) FreeStepsH.refl

theorem setR7_other {ω : Regs} {v j : Nat} (hj : j < 13) (h7 : j ≠ 7) : (setR7 ω v)[j] = ω[j] := by
  unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h7]

theorem setR7_self {ω : Regs} {v : Nat} : (setR7 ω v)[7] = UInt64.ofNat v := by
  unfold setR7; rw [Vector.getElem_set]; simp

/-- **41517 … 41589, the heap grown**: the allocation's end E (in units past the base) lies within
    the heap's bound b (in pages); the host grows the heap and the allocated space becomes E. -/
theorem ag_grow {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base a b : Nat) (hb : heapBounds env.code = (a, b)) (hab : a ≤ b) (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E)
    (h96 : rdN μ (sp + 96) 8 = base) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41517 ω μ x 41589 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[9] = ω[9] ∧ ω'[4] = ω[4] ∧ ω'[0] = ω[0] ∧ ω'[3] = ω[3] ∧
      ω'[10] = UInt64.ofNat (rdN μ (sp + 56) 8) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [0, 3, 4, 6, 7, 8, 9, 10] → ω'[j] = ω[j] := by
  obtain ⟨ω1, μ1, r1, a7, a6, s0, s8, s16, s24, s48, fr1, ww1, g1⟩ :=
    ag_pre (p := p) (P := P) (R := refineContract env) x ω μ sp E base h1 h5 h96 hE hbase hsp0 hsp hwr
  have r2 := ag_call (p := p) (P := P) env x ω1 μ1 a b _ hb hab hbs a7 (by unfold pagesOf; split <;> omega) ww1
  have ww2 : ∀ a', (μ1.setPages a (b - a) (some .write)).writable a' = true := fun a' => by
    rw [Memory.writable_setPages]; split
    · rfl
    · exact ww1 a'
  have tr1 : ∀ q, sp + 32 ≤ q → q + 8 ≤ sp + 48 ∨ sp + 56 ≤ q → q + 8 ≤ sp + 152 → rdN μ1 q 8 = rdN μ q 8 :=
    fun q h h' h'' => rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega)) (by omega)
  obtain ⟨ω3, μ3, r3, e206, e7, e9, e4, e10, e0, e3, fr3, ww3, g3⟩ := ag_post_ok (p := p) (P := P)
    (R := refineContract env) x (setR7 ω1 b) (μ1.setPages a (b - a) (some .write)) sp E b _
    (by rw [setR7_other (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) setR7_self
    (by rw [setR7_other (by decide) (by decide)]; exact a6)
    (by rw [setR7_other (by decide) (by decide), fget g1 5 (by decide) (by decide)]; exact h5)
    (by unfold rdN; rw [Memory.readN_setPages]; have := tr1 (sp + 120) (by omega) (by omega) (by omega)
        unfold rdN at this; rw [this]; exact h120)
    hR hbs (by omega) hsp0 hsp ww2
  have dec : ∀ v : UInt64, UInt64.ofNat (Num.decodeLE (Num.encodeLE 8 v.toNat)) = v := fun v => by
    rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), e206, ?_, ?_, ?_, ?_, ?_, ?_,
    fun q h1 h2 h3 h4 => (fr3 q h1 h4).trans (fr1 q h1 h2 h3), ww3, ?_⟩
  · rw [e7]; unfold rdN; rw [Memory.readN_setPages, s48]; exact dec _
  · rw [e9]; unfold rdN; rw [Memory.readN_setPages, s24]; exact dec _
  · rw [e4]; unfold rdN; rw [Memory.readN_setPages, s16]; exact dec _
  · rw [e0]; unfold rdN; rw [Memory.readN_setPages, s8]; exact dec _
  · rw [e3]; unfold rdN; rw [Memory.readN_setPages, s0]; exact dec _
  · rw [e10]; congr 1; unfold rdN; rw [Memory.readN_setPages]
    have := tr1 (sp + 56) (by omega) (by omega) (by omega); unfold rdN at this; exact this
  · intro j hj
    have hj7 : j.val ≠ 7 := by simp at hj; omega
    rw [g3 j (by simp at hj ⊢; omega)]
    simp only [Fin.getElem_fin]
    rw [setR7_other j.isLt hj7]
    exact g1 j (by simp at hj ⊢; omega)

/-- 41558 … 41401: the heap's new top below the requested page: to the failure. -/
theorem ag_post_fail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (t Rq : Nat) (h7 : ω[7] = UInt64.ofNat t) (h6 : ω[6] = UInt64.ofNat Rq) (hlt : t < Rq)
    (hRq : Rq < 18446744073709551616) : FreeStepsH p R 41558 ω μ x 41401 ω μ x 2 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7, h6, Nat.mod_eq_of_lt hRq, Nat.mod_eq_of_lt (show t < 18446744073709551616 by omega), hlt]

/-- **41517 … 41401, the heap cannot grow**: the allocation's end lies past the heap's bound; the
    host returns the bound and the code goes to the failure. -/
theorem ag_grow_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base a b : Nat) (hb : heapBounds env.code = (a, b)) (hab : a ≤ b) (hbs : b < 4294967296)
    (hR : b < pagesOf (base + 32 * E))
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E) (h96 : rdN μ (sp + 96) 8 = base)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41517 ω μ x 41401 ω' μ' x 30 ∧ ω'[1] = ω[1] ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) := by
  obtain ⟨ω1, μ1, r1, a7, a6, -, -, -, -, -, fr1, ww1, g1⟩ :=
    ag_pre (p := p) (P := P) (R := refineContract env) x ω μ sp E base h1 h5 h96 hE hbase hsp0 hsp hwr
  have r2 := ag_call (p := p) (P := P) env x ω1 μ1 a b _ hb hab hbs a7 (by unfold pagesOf; split <;> omega) ww1
  have r3 := ag_post_fail (p := p) (P := P) (R := refineContract env) x (setR7 ω1 b)
    (μ1.setPages a (b - a) (some .write)) b _ setR7_self (by rw [setR7_other (by decide) (by decide)]; exact a6) hR
    (by unfold pagesOf; split <;> omega)
  refine ⟨_, _, ((r1.trans r2).trans r3).mono (by omega),
    by rw [setR7_other (by decide) (by decide), fget g1 1 (by decide) (by decide)],
    fun q h1 h2 h3 => fr1 q h1 h2 h3, fun a' => ?_⟩
  rw [Memory.writable_setPages]; split
  · rfl
  · exact ww1 a'

/-- Memory holding t, with the allocated space written as E, holds t with that allocated space. -/
theorem RepAt.setAlloc {μ μ' : Memory} {t : State} {H F : Nat → Prop} {E : Nat} (h : RepAt μ t H F)
    (w : rdN μ' 206840 4 = E)
    (wf : ∀ a, a < 2147483648 → (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a)
    (hHa : ∀ b, H b ∨ F b → 206864 ≤ b ∧ b + 16 < 2147483648) :
    RepAt μ' { t with allocated := E } H F := by
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · unfold A0; exact w
  · have := hHa b (Or.inl hb); rw [← h.prev b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inl hb); rw [← h.size b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inr hb); rw [← h.next b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)
  · have := hHa b (Or.inr hb); rw [← h.prevL b hb]; exact rdN_frame fun j hj => wf _ (by omega) (by omega)

end Services.Bootstrap.Alloc
