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
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1)
    (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41517 ω μ x 41556 ω' μ' x 20 ∧ ω'[7] = UInt64.ofNat (pagesOf (base + 32 * E)) ∧
      ω'[6] = UInt64.ofNat (pagesOf (base + 32 * E)) ∧
      μ'.readN sp 8 = Num.encodeLE 8 ω[3].toNat ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 ω[0].toNat ∧
      μ'.readN (sp + 16) 8 = Num.encodeLE 8 ω[4].toNat ∧ μ'.readN (sp + 24) 8 = Num.encodeLE 8 ω[9].toNat ∧
      μ'.readN (sp + 48) 8 = Num.encodeLE 8 ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [6, 7, 8] → ω'[j] = ω[j] := by
  have hr := hwr.rd
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
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41558 ω μ x 41589 ω' μ' x 12 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = UInt64.ofNat (rdN μ (sp + 48) 8) ∧ ω'[9] = UInt64.ofNat (rdN μ (sp + 24) 8) ∧
      ω'[4] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧ ω'[10] = UInt64.ofNat (rdN μ (sp + 56) 8) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧ ω'[3] = UInt64.ofNat (rdN μ sp 8) ∧
      (∀ a, a < 4294967296 → (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ ∀ j : Fin 13, j.val ∉ [0, 3, 4, 7, 9, 10] → ω'[j] = ω[j] := by
  have hr := hwr.rd
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

/-- **41556, `ecalli 1` (Ω_♊)**: with the heap's writable pages exactly 48 … h of its bound b
    (`HeapPages`), the host grows the heap to the requested page Rq if it lies in h … b, and returns
    the new top `growTop Rq h b` in ω₇; pages 48 up to it are writable.
    Under `refineContractK cap`, any growth whose cost 275 + 121 (t − h) fits in `cap`. -/
theorem ag_callK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : 275 + 121 * (growTop Rq h b - h) ≤ cap) :
    FreeStepsH p (refineContractK cap env) 41556 ω μ x 41558 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 := by
  have hr7 : reg ω 7 = Rq := by
    unfold reg; have : ω.get 7 = ω[7] := rfl; rw [this, h7, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hRq]
  have ht : growTop (reg ω 7) h b = growTop Rq h b := by rw [hr7]
  have hge : h ≤ growTop Rq h b := by unfold growTop; split <;> omega
  exact FreeStepsH.growHeapK cap hcap env _ (d_41556 (p := p) (P := P)) hb hp h48 hhb hbs ht
    (by unfold Constants.CgasGeminiconst Constants.CgasGeminilinear; omega) FreeStepsH.refl

/-- `ag_callK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem ag_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : growTop Rq h b ≤ h + 14) :
    FreeStepsH p (refineContract env) 41556 ω μ x 41558 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 :=
  ag_callK (p := p) (P := P) env hostCostMax (by decide) x ω μ b h Rq hb hp h48 hhb hbs h7 hRq
    (by unfold hostCostMax; omega)

/-- The writable regions from `HeapPages`: the heap 48 … h in pages, and the stack. -/
theorem HeapPages.wrAt {μ : Memory} {b h S0 S1 : Nat} (hp : HeapPages μ 48 b h) (hhb : h ≤ b)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) : WrAt μ (4096 * h) S0 S1 := by
  intro a ha
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hp (a / 4096) (by omega) (by omega)
    unfold Memory.writable
    rw [show pageSize = 4096 from rfl, this]
    simp only [decide_eq_true_eq]; omega
  · exact hst a h1 h2

/-- Steps that keep every page's access keep `HeapPages`. -/
theorem HeapPages.of_eq {μ μ' : Memory} {a b h : Nat} (hp : HeapPages μ a b h)
    (he : ∀ i, μ'.writable i = μ.writable i) : HeapPages μ' a b h := fun q h1 h2 => by
  have := he (q * 4096)
  unfold Memory.writable at this
  rw [show pageSize = 4096 from rfl, Nat.mul_div_cancel _ (by decide)] at this
  rw [this]; exact hp q h1 h2

/-- `grow_heap` to t: the writable heap pages become 48 … t. -/
theorem HeapPages.grow {μ : Memory} {b h t : Nat} (hp : HeapPages μ 48 b h) (hht : h ≤ t) :
    HeapPages (μ.setPages 48 (t - 48) (some .write)) 48 b t := fun q h1 h2 => by
  rw [Memory.setPages_get?]
  by_cases hq : q < t
  · rw [if_pos (by omega)]; simp [hq]
  · rw [if_neg (by omega), hp q h1 h2]; simp only [decide_eq_decide]; omega

/-- `grow_heap` changes only pages of the heap, below the stack. -/
theorem stack_setPages {μ : Memory} {t S0 S1 : Nat} (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hS : 4096 * t ≤ S0) : ∀ a, S0 ≤ a → a < S1 → (μ.setPages 48 (t - 48) (some .write)).writable a = true :=
  fun a h1 h2 => by
    rw [Memory.writable_setPages, if_neg (by unfold pageSize; omega)]; exact hst a h1 h2

theorem growTop_ge {Rq h b : Nat} (hRb : Rq ≤ b) : Rq ≤ growTop Rq h b ∧ h ≤ growTop Rq h b ∧ growTop Rq h b ≤ max h b := by
  unfold growTop; split <;> omega

theorem pagesOf_ge (x : Nat) : x ≤ 4096 * pagesOf x := by unfold pagesOf; split <;> omega


theorem setR7_other {ω : Regs} {v j : Nat} (hj : j < 13) (h7 : j ≠ 7) : (setR7 ω v)[j] = ω[j] := by
  unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h7]

theorem setR7_self {ω : Regs} {v : Nat} : (setR7 ω v)[7] = UInt64.ofNat v := by
  unfold setR7; rw [Vector.getElem_set]; simp

/-- **41517 … 41589, the heap grown**: the allocation's end E (in units past the base) lies within
    the heap's bound b (in pages); the host grows the heap from its top h to cover it, and the
    allocated space becomes E.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem ag_growK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : 275 + 121 * (growTop (pagesOf (base + 32 * E)) h b - h) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E)
    (h96 : rdN μ (sp + 96) 8 = base) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41517 ω μ x 41589 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[9] = ω[9] ∧ ω'[4] = ω[4] ∧ ω'[0] = ω[0] ∧ ω'[3] = ω[3] ∧
      ω'[10] = UInt64.ofNat (rdN μ (sp + 56) 8) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 4, 6, 7, 8, 9, 10] → ω'[j] = ω[j] := by
  have hwr := HeapPages.wrAt hp hhb hst
  generalize hRq : pagesOf (base + 32 * E) = Rq at *
  have hRq1 : Rq < 18446744073709551616 := by have := pagesOf_ge (base + 32 * E); rw [hRq] at this; unfold pagesOf at hRq; split at hRq <;> omega
  obtain ⟨g1', g2', g3'⟩ := growTop_ge (h := h) hR
  generalize hT : growTop Rq h b = t at *
  obtain ⟨ω1, μ1, r1, a7, a6, s0, s8, s16, s24, s48, fr1, ww1, g1⟩ :=
    ag_pre (p := p) (P := P) (R := refineContractK cap env) x ω μ sp E base h1 h5 h96 hE hbase hsp0 hsp hSTk hwr
  rw [hRq] at a7 a6
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  have r2 := ag_callK (p := p) (P := P) env cap hcap x ω1 μ1 b h Rq hb hp1 h48 hhb hbs a7 hRq1 (by rw [hT]; exact hcost)
  rw [hT] at r2
  have hp2 := HeapPages.grow hp1 (t := t) (by omega)
  have hst2 := stack_setPages hst1 (t := t) (by omega)
  have hwr2 := HeapPages.wrAt hp2 (by omega) hst2
  have tr1 : ∀ q, sp + 32 ≤ q → q + 8 ≤ sp + 48 ∨ sp + 56 ≤ q → q + 8 ≤ sp + 152 → rdN μ1 q 8 = rdN μ q 8 :=
    fun q h h' h'' => rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega)) (by omega)
  obtain ⟨ω3, μ3, r3, e206, e7, e9, e4, e10, e0, e3, fr3, ww3, g3⟩ := ag_post_ok (p := p) (P := P)
    (R := refineContractK cap env) x (setR7 ω1 t) (μ1.setPages 48 (t - 48) (some .write)) sp E t Rq
    (by rw [setR7_other (by decide) (by decide), fget g1 1 (by decide) (by decide)]; exact h1) setR7_self
    (by rw [setR7_other (by decide) (by decide)]; exact a6)
    (by rw [setR7_other (by decide) (by decide), fget g1 5 (by decide) (by decide)]; exact h5)
    (by unfold rdN; rw [Memory.readN_setPages]; have := tr1 (sp + 120) (by omega) (by omega) (by omega)
        unfold rdN at this; rw [this]; exact h120)
    g1' (by omega) (by omega) hsp0 hsp (by omega) hSTk hwr2
  have dec : ∀ v : UInt64, UInt64.ofNat (Num.decodeLE (Num.encodeLE 8 v.toNat)) = v := fun v => by
    rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega), e206, ?_, ?_, ?_, ?_, ?_, ?_,
    fun q h1 h2 h3 h4 => (fr3 q h1 h4).trans (fr1 q h1 h2 h3), HeapPages.of_eq hp2 ww3,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2, ?_⟩
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

/-- `ag_growK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem ag_grow {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296)
    (hR : pagesOf (base + 32 * E) ≤ b) (hcost : growTop (pagesOf (base + 32 * E)) h b ≤ h + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E)
    (h96 : rdN μ (sp + 96) 8 = base) (h120 : rdN μ (sp + 120) 8 = 204984)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h)
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41517 ω μ x 41589 ω' μ' x 40 ∧ rdN μ' 206840 4 = E ∧
      ω'[7] = ω[7] ∧ ω'[9] = ω[9] ∧ ω'[4] = ω[4] ∧ ω'[0] = ω[0] ∧ ω'[3] = ω[3] ∧
      ω'[10] = UInt64.ofNat (rdN μ (sp + 56) 8) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) →
        (a < 206840 ∨ 206844 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b (growTop (pagesOf (base + 32 * E)) h b) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      ∀ j : Fin 13, j.val ∉ [0, 3, 4, 6, 7, 8, 9, 10] → ω'[j] = ω[j] :=
  ag_growK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ sp E base b h
    hb h48 hhb hbs hR (by unfold hostCostMax; omega) h1 h5 h96 h120 hE hbase hsp0 hsp hHTs hSTk hSb
    hp hst

/-- 41558 … 41401: the heap's new top below the requested page: to the failure. -/
theorem ag_post_fail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (t Rq : Nat) (h7 : ω[7] = UInt64.ofNat t) (h6 : ω[6] = UInt64.ofNat Rq) (hlt : t < Rq)
    (hRq : Rq < 18446744073709551616) : FreeStepsH p R 41558 ω μ x 41401 ω μ x 2 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7, h6, Nat.mod_eq_of_lt hRq, Nat.mod_eq_of_lt (show t < 18446744073709551616 by omega), hlt]

/-- **41517 … 41401, the heap cannot grow**: the allocation's end lies past the heap's bound; the
    host returns the heap's top unchanged and the code goes to the failure.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem ag_grow_failK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296) (hR : b < pagesOf (base + 32 * E))
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E) (h96 : rdN μ (sp + 96) 8 = base)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat}
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41517 ω μ x 41401 ω' μ' x 30 ∧ ω'[1] = ω[1] ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) := by
  have hwr := HeapPages.wrAt hp hhb hst
  generalize hRq : pagesOf (base + 32 * E) = Rq at *
  have hRq1 : Rq < 18446744073709551616 := by unfold pagesOf at hRq; split at hRq <;> omega
  have hT : growTop Rq h b = h := by unfold growTop; rw [if_pos (Or.inr hR)]
  obtain ⟨ω1, μ1, r1, a7, a6, -, -, -, -, -, fr1, ww1, g1⟩ :=
    ag_pre (p := p) (P := P) (R := refineContractK cap env) x ω μ sp E base h1 h5 h96 hE hbase hsp0 hsp hSTk hwr
  rw [hRq] at a7 a6
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  have r2 := ag_callK (p := p) (P := P) env cap hcap x ω1 μ1 b h Rq hb hp1 h48 hhb hbs a7 hRq1 (by rw [hT]; omega)
  rw [hT] at r2
  have r3 := ag_post_fail (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω1 h)
    (μ1.setPages 48 (h - 48) (some .write)) h Rq setR7_self (by rw [setR7_other (by decide) (by decide)]; exact a6)
    (by omega) hRq1
  refine ⟨_, _, ((r1.trans r2).trans r3).mono (by omega),
    by rw [setR7_other (by decide) (by decide), fget g1 1 (by decide) (by decide)],
    fun q h1 h2 h3 => fr1 q h1 h2 h3, HeapPages.grow hp1 (Nat.le_refl h), stack_setPages hst1 (by omega)⟩

/-- `ag_grow_failK` at `hostCostMax`, the cap of `refineContract`. -/
theorem ag_grow_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (sp E base b h : Nat) (hb : heapBounds env.code = (48, b)) (h48 : 48 ≤ h) (hhb : h ≤ b)
    (hbs : b < 4294967296) (hR : b < pagesOf (base + 32 * E))
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat E) (h96 : rdN μ (sp + 96) 8 = base)
    (hE : E ≤ 33554432) (hbase : base < 2147483648)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 152 < 4294967296) {S0 S1 : Nat}
    (hSTk : S0 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * b ≤ S0) (hp : HeapPages μ 48 b h)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41517 ω μ x 41401 ω' μ' x 30 ∧ ω'[1] = ω[1] ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → (a < sp + 48 ∨ sp + 56 ≤ a) → μ'.read a = μ.read a) ∧
      HeapPages μ' 48 b h ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) :=
  ag_grow_failK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) (by decide) x ω
    μ sp E base b h hb h48 hhb hbs hR h1 h5 h96 hE hbase hsp0 hsp hSTk hSb hp hst

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
