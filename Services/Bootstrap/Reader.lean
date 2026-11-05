import Services.Bootstrap.Memcpy
import PVM.Logic.Bits

/-!
# Bootstrap's argument reader, summarized

The function at 58434 reads n octets from a reader `{ptr, len}` (at ω₇ and ω₇ + 8) into a buffer
at ω₈: if len ≥ n it copies them with `memcpy` (68729), advances the reader by n and returns
ω₇ = 0. This file proves it for every n < 16, from the code facts alone.
-/

namespace Services.Bootstrap

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 4000000

variable {X : Type} {R : HostRel X}

/-- What a successful read of n octets leaves: ω₇ = 0, ω₀ ω₁ ω₂ ω₃ ω₄ ω₅ ω₆ ω₁₂ as they were, the
    reader advanced by n, the buffer holding the n octets, and memory unchanged outside the stack
    frames [sp − 88, sp), the reader and the buffer, with the same page access. -/
def ReadOk (ω ω' : Regs) (μ μ' : Memory) (sp rd buf ptr len n : Nat) : Prop :=
  ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧
    ω'[6] = ω[6] ∧ ω'[12] = ω[12] ∧ ω'[7] = UInt64.ofNat 0 ∧
    μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
    μ'.readN buf n = μ.readN ptr n ∧
    (∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < buf ∨ buf + n ≤ a) →
      μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

theorem read_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296)
    (hn : n < 16) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrf : rd + 16 ≤ sp - 88 ∨ sp ≤ rd) (hbf : buf + 16 ≤ sp - 88 ∨ sp ≤ buf)
    (hpf : ptr + 16 ≤ sp - 88 ∨ sp ≤ ptr) (hbr : buf + 16 ≤ rd ∨ rd + 16 ≤ buf)
    (hbp : buf + n ≤ ptr ∨ ptr + n ≤ buf)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (7 * n + 50) ∧ ReadOk ω ω' μ μ' sp rd buf ptr len n := by
  have hrf' : ∀ a, sp - 88 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 68729) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 15) (n₂ := 7 * n + 35) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_58434 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_58437 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58440 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58443 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58446 (p := p) (P := P))
    · pvm_simp [h9]
    apply FreeStepsH.step_decode (d_58448 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_58451 (p := p) (P := P))
    · pvm_simp [h9]
    apply FreeStepsH.step_decode (d_58454 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58455 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_58457 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58459 (p := p) (P := P))
    · pvm_simp [h1, h7, hwf]
    apply FreeStepsH.step_decode (d_58462 (p := p) (P := P))
    · pvm_simp [h8]
    apply FreeStepsH.step_decode (d_58464 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58466 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58468 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small_regs (p := p) (P := P) (R := R) x _ _ 2550 58474 (sp - 40)
      buf ptr n ?m0 ?m1 ?m7 ?m8 ?m9 hn (by decide) ?mjt ?mbt (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 14)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8, h9]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1274]
    case mbt => exact bs_58474
    case mwf =>
      intro a h1 h2
      simp only [Memory.writable_writeN]
      exact hwf a (by omega) (by omega)
    case mr =>
      intro a h1 h2
      simp only [Memory.readable_writeN]
      exact hra a (by omega) (by omega)
    case mw =>
      intro a h1 h2
      simp only [Memory.writable_writeN]
      exact hwb a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g2, g3, g4, g5, g6, g7, g12⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g2 g3 g4 g5 g6 g7 g12
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_58474 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_58477 (p := p) (P := P))
        · pvm_simp [g1, hrf', memcpyFrame]
        apply FreeStepsH.step_decode (d_58479 (p := p) (P := P))
        · pvm_simp [g5]
        apply FreeStepsH.step_decode (d_58482 (p := p) (P := P))
        · pvm_simp [g1, hrf', memcpyFrame]
        apply FreeStepsH.step_decode (d_58485 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_58487 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_58490 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_58491 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_58494 (p := p) (P := P))
        · pvm_simp [g1, hrf', memcpyFrame]
        apply FreeStepsH.step_decode (d_58497 (p := p) (P := P))
        · pvm_simp [g1, hrf', memcpyFrame]
        apply FreeStepsH.step_decode (d_58500 (p := p) (P := P))
        · pvm_simp [g1, hrf', memcpyFrame]
        apply FreeStepsH.step_decode (d_58503 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_58506 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl.mono (Nat.zero_le _)
      case post₂ =>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩ <;>
        simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, memcpyFrame,
          PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint,
          PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE,
          PVM.Memory.length_readN, List.length_cons, List.length_nil, PVM.two32, PVM.mul_one', PVM.sub_zero',
          Nat.mod_add_div, Nat.div_add_mod', Nat.mod_mod, Nat.sub_sub, Nat.reduceAdd, h0, h1, h7, g0, g1, g2,
          g3, g4, g5, g6, g12, hR0, hR8, UInt64.toNat_ofNat]
        all_goals simp only [Memory.readN]
    case hle2 => omega
  case hle => omega

end Services.Bootstrap
