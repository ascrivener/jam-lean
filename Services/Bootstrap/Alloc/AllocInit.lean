import Services.Bootstrap.Alloc.AllocGrowRefines

/-!
# The binary's `initialize`

`initialize` (42165, called by `alloc_impl` at 42142 on the first use, ω₀ = 1998): the heap's base is
206880 (the allocator's end rounded up to 32); the host grows the heap over its first chunk's header
(51 pages); then the base, one unit allocated, the top bin's head, its bits, and the first chunk's
header — one free chunk of 2²⁵ units — are written.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **42165 … 42211**: the frame, the heap's base 206880 in ω₅, and the 51 pages to grow to. -/
theorem ii_pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp0 : 2147483680 ≤ sp) (hsp : sp < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42165 ω μ x 42211 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat 206880 ∧ ω'[6] = UInt64.ofNat 51 ∧
      ω'[7] = UInt64.ofNat 51 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 32) 8 = Num.encodeLE 8 ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) ∧ ∀ j : Fin 13, j.val ∉ [1, 5, 6, 7, 8] → ω'[j] = ω[j] := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, by reg_frame⟩
    · rw [show sp - 8 = sp - 32 + 24 by omega]; rd_simp []; rfl
    · rw [show sp - 16 = sp - 32 + 16 by omega]; rd_simp []; rfl
    · rw [show sp - 24 = sp - 32 + 8 by omega]; rd_simp []; rfl
    · rd_simp []; rfl
    · rd_simp []
    · rd_simp [hwr]

/-- **42211, `ecalli 1`**, every page writable: the call returns the heap's bound b. -/
theorem ii_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (a b : Nat) (hb : heapBounds env.code = (a, b)) (hab : a ≤ b) (hbs : b < 4294967296)
    (hw : ∀ a, μ.writable a = true) :
    FreeStepsH p (refineContract env) 42211 ω μ x 42213 (setR7 ω b) (μ.setPages a (b - a) (some .write)) x 1 := by
  have ht : growTop (reg ω 7) b b = b := by unfold growTop; rw [if_pos (by omega)]
  have hp : HeapPages μ a b b := fun q h1 h2 => by
    have h' : (μ.pages.get? q == some .write) = true := by
      have := hw (q * pageSize); unfold Memory.writable at this
      rwa [Nat.mul_div_cancel _ (show 0 < pageSize by unfold pageSize; decide)] at this
    rw [h']; simp [h2]
  rw [← ht]
  exact FreeStepsH.growHeap env _ (d_42211 (p := p) (P := P)) hb hp hab (Nat.le_refl b) hbs rfl
    (by rw [ht]; simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; decide) FreeStepsH.refl

/-- **42213 … 42325**, the heap reaching the 51 pages: the base, one unit allocated, the top bin
    (2431)'s head and bits, and the first chunk's header written; ω₇ = 1, the frame popped. -/
theorem ii_post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp t w pri : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat t) (h6 : ω[6] = UInt64.ofNat 51)
    (h5 : ω[5] = UInt64.ofNat 206880) (h0 : rdN μ sp 8 = 196792) (ht : 51 ≤ t) (ht1 : t < 4294967296)
    (hw : rdN μ 206824 8 = w) (hp : rdN μ 206832 8 = pri)
    (hsp0 : 2147483648 ≤ sp) (hsp : sp + 32 < 4294967296) (hwr : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42213 ω μ x 42325 ω' μ' x 30 ∧
      rdN μ' 206516 4 = 206880 ∧ rdN μ' 206520 8 = 206880 ∧ rdN μ' 206824 8 = w ||| 2 ^ 63 ∧
      rdN μ' 206832 8 = pri ||| 2 ^ 37 ∧ rdN μ' 206840 4 = 1 ∧ rdN μ' 206880 4 = 0 ∧
      rdN μ' 206884 4 = sizeWord 33554432 false ∧ rdN μ' 206888 4 = 0 ∧ rdN μ' 206892 4 = 0 ∧
      ω'[7] = UInt64.ofNat 1 ∧ ω'[0] = UInt64.ofNat (rdN μ (sp + 24) 8) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 16) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 8) 8) ∧
      ω'[1] = UInt64.ofNat (sp + 32) ∧
      (∀ a, a < 4294967296 → (a < 206516 ∨ 206528 ≤ a) → (a < 206824 ∨ 206844 ≤ a) →
        (a < 206880 ∨ 206896 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = true) := by
  have hr : ∀ a, μ.readable a = true := fun a => Memory.readable_of_writable (hwr a)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h6, h5, h0, hw, hp, Nat.mod_eq_of_lt ht1, show 51 ≤ t from ht, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    have hw64 : w < 2 ^ 64 := by rw [← hw]; exact rdN_lt64 μ _
    have hp64 : pri < 2 ^ 64 := by rw [← hp]; exact rdN_lt64 μ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
      fun a ha h1 h2 h3 => ?_, fun a => ?_⟩
    all_goals try rd_simp [hwr]
    all_goals try decide
    · rw [show (9223372036854775808 : Nat) = 2 ^ 63 % 18446744073709551616 from rfl]
      exact or_word _ _ hw64 (by decide)
    · rw [show (137438953472 : Nat) = 2 ^ 37 % 18446744073709551616 from rfl]
      exact or_word' _ _ hp64 (by decide)
    all_goals try (simp only [Num.decodeLE, Memory.readN, List.range, List.range.loop, List.map, Nat.add_zero]
                   simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,
                     List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
                     Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,
                     List.getElem!_cons_succ, UInt8.reduceOfNat]
                   decide)

end Services.Bootstrap.Alloc
