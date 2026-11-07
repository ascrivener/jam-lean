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

/-- **43470, `ecalli 1` (Ω_♊)**, as `ag_call`. -/
theorem rgh_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (b h Rq : Nat) (hb : heapBounds env.code = (48, b)) (hp : HeapPages μ 48 b h) (h48 : 48 ≤ h)
    (hhb : h ≤ b) (hbs : b < 4294967296) (h7 : ω[7] = UInt64.ofNat Rq) (hRq : Rq < 18446744073709551616)
    (hcost : growTop Rq h b ≤ h + 14) :
    FreeStepsH p (refineContract env) 43470 ω μ x 43472 (setR7 ω (growTop Rq h b))
      (μ.setPages 48 (growTop Rq h b - 48) (some .write)) x 1 := by
  have hr7 : reg ω 7 = Rq := by
    unfold reg; have : ω.get 7 = ω[7] := rfl; rw [this, h7, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hRq]
  have ht : growTop (reg ω 7) h b = growTop Rq h b := by rw [hr7]
  have hge : h ≤ growTop Rq h b := by unfold growTop; split <;> omega
  exact FreeStepsH.growHeap env _ (d_43470 (p := p) (P := P)) hb hp h48 hhb hbs ht
    (by unfold Constants.CgasGeminiconst Constants.CgasGeminilinear hostCostMax; omega) FreeStepsH.refl

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

end Services.Bootstrap.Alloc
