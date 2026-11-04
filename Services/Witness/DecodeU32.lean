import Services.Witness.Memcpy
import PVM.Logic.Bits

/-!
# The SDK's `u32` decoder in witness, summarized

The function at 184570 decodes a `u32` from a reader `{ptr, len}` (at ω₇ and ω₇ + 8) in the
general natural encoding ℰ (GP (C)): ω₇ = 0 and ω₈ = n on success, and the reader advanced past
the encoding. This file proves it for every encoding of every n < 2^32.
-/

namespace Services.Witness

open PVM Services.Witness.Code

set_option maxHeartbeats 4000000

variable {X : Type} {R : HostRel X}

/-- What a successful decode of `n` (an encoding of `w` octets) leaves: ω₇ = 0 and ω₈ = n, the
    callee-saved ω₀, ω₁, ω₅, ω₆ as they were, the reader advanced by `w`, and memory unchanged
    outside the stack frames [sp − 104, sp) and the reader, with the same page access. -/
def DecodeOk (ω ω' : Regs) (μ μ' : Memory) (sp rd ptr len n w : Nat) : Prop :=
  ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
    ω'[8] = UInt64.ofNat n ∧ μ'.readN rd 8 = Num.encodeLE 8 (ptr + w) ∧
    μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - w) ∧
    (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- Prove `DecodeOk` of a concrete final state. -/
macro "decode_post" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩ <;>
  try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, memcpyFrame,
    PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint,
    PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE,
    PVM.Memory.length_readN, List.length_cons, List.length_nil, PVM.two32, PVM.mul_one', PVM.sub_zero', Nat.mod_add_div,
    Nat.div_add_mod', Nat.mod_mod, Nat.sub_sub, Nat.reduceAdd, $hs,*]))

theorem decodeU32_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 0 < len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : μ.readable ptr = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hb : μ.read ptr = 0) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len 0 1 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
    · pvm_simp [hrf']
    apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
    · pvm_simp [hrf']
    apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
    · pvm_simp [hrf']
    apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
    · pvm_simp [h0, hret, hjt, hbt]
    exact FreeStepsH.refl.mono (Nat.zero_le _)
  case post => decode_post [h0, h1]

theorem decodeU32_one {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 0 < len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : μ.readable ptr = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 0 < n ∧ n < 128) (hb : μ.read ptr = UInt8.ofNat n) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 1 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 29) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184612 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184616 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184665 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184667 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184670 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184672 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184675 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184781 (p := p) (P := P))
    · pvm_simp [hwf, h7]
    apply FreeStepsH.step_decode (d_184784 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184787 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184789 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184792 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184794 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184796 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 3386 184802 (sp - 56)
      (sp - 56 + 24) (ptr + 1) 0 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf (fun a h1 h2 => by omega)
      (fun a h1 h2 => by omega)) ?k ?hle2 (n₂ := 24)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1692]
    case mbt => exact bs_184802
    case mwf =>
      intro a h1 h2
      simp only [Memory.writable_writeN]
      exact hwf a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g5, g6, g7⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g5 g6 g7
      simp only [memcpyFrame, Memory.readN, List.range_zero, List.map_nil, Memory.writeN_nil,
        PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        UInt64.toNat_ofNat]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_184802 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184805 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184807 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184810 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_184813 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184816 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184819 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184821 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184824 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184827 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184830 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184833 (p := p) (P := P))
        · pvm_simp [bitwise_andInv_high (s := 7)]
        apply FreeStepsH.step_decode (d_184836 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184839 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184842 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184845 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184848 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl
      case post₂ => decode_post [h0, h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide

/-- **Decoding a 2-octet ℰ(n)**, 128 ≤ n < 16384: the prefix octet 128 + ⌊n / 2^8⌋, then
    ℰ_1(n mod 2^8). -/
theorem decodeU32_len2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 2 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 2 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 128 ≤ n ∧ n < 16384) (hn32 : n < 4294967296)
    (hb : μ.read ptr = UInt8.ofNat (128 + n / 256))
    (hrest : μ.readN (ptr + 1) 1 = Num.encodeLE 1 (n % 256)) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 2 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 32) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra0, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184612 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184616 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184665 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184667 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184677 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_184680 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184683 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184686 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184753 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184756 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184781 (p := p) (P := P))
    · pvm_simp [hwf, h7]
    apply FreeStepsH.step_decode (d_184784 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184787 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184789 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184792 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184794 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184796 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 3386 184802 (sp - 56)
      (sp - 56 + 24) (ptr + 1) 1 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 24)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1692]
    case mbt => exact bs_184802
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
      exact hwf a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g5, g6, g7⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g5 g6 g7
      simp only [memcpyFrame, PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', UInt64.toNat_ofNat]
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32, hrest]
      rw [show Num.encodeLE 1 (n % 256) = [UInt8.ofNat (n % 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_184802 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184805 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184807 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184810 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_184813 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184816 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184819 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184821 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184824 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184827 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184830 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184833 (p := p) (P := P))
        · pvm_simp [bitwise_andInv_high (s := 6)]
        apply FreeStepsH.step_decode (d_184836 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184839 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184842 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184845 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184848 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl
      case post₂ => decode_post [h0, h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide


/-- **Decoding a 3-octet ℰ(n)**, 16384 ≤ n < 2097152: the prefix octet 192 + ⌊n / 2^16⌋, then
    ℰ_2(n mod 2^16). -/
theorem decodeU32_len3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 3 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 3 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 16384 ≤ n ∧ n < 2097152) (hn32 : n < 4294967296)
    (hb : μ.read ptr = UInt8.ofNat (192 + n / 65536))
    (hrest : μ.readN (ptr + 1) 2 = Num.encodeLE 2 (n % 65536)) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 3 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 34) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra0, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184612 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184616 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184665 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184667 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184677 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_184680 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184688 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 5)]
    apply FreeStepsH.step_decode (d_184691 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184694 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184697 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184753 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184756 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184781 (p := p) (P := P))
    · pvm_simp [hwf, h7]
    apply FreeStepsH.step_decode (d_184784 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184787 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184789 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184792 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184794 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184796 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 3386 184802 (sp - 56)
      (sp - 56 + 24) (ptr + 1) 2 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 24)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1692]
    case mbt => exact bs_184802
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
      exact hwf a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g5, g6, g7⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g5 g6 g7
      simp only [memcpyFrame, PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', UInt64.toNat_ofNat]
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32, hrest]
      rw [show Num.encodeLE 2 (n % 65536) = [UInt8.ofNat (n % 65536 % 256), UInt8.ofNat (n % 65536 / 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_184802 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184805 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184807 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184810 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_184813 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184816 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184819 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184821 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184824 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184827 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184830 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184833 (p := p) (P := P))
        · pvm_simp [bitwise_andInv_high (s := 5)]
        apply FreeStepsH.step_decode (d_184836 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184839 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184842 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184845 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184848 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl
      case post₂ => decode_post [h0, h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide


/-- **Decoding a 4-octet ℰ(n)**, 2097152 ≤ n < 268435456: the prefix octet 224 + ⌊n / 2^24⌋, then
    ℰ_3(n mod 2^24). -/
theorem decodeU32_len4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 4 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 4 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 2097152 ≤ n ∧ n < 268435456) (hn32 : n < 4294967296)
    (hb : μ.read ptr = UInt8.ofNat (224 + n / 16777216))
    (hrest : μ.readN (ptr + 1) 3 = Num.encodeLE 3 (n % 16777216)) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 4 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 36) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra0, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184612 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184616 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184665 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184667 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184677 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_184680 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184688 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 5)]
    apply FreeStepsH.step_decode (d_184691 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184699 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 4)]
    apply FreeStepsH.step_decode (d_184702 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184705 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184708 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184753 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184756 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184781 (p := p) (P := P))
    · pvm_simp [hwf, h7]
    apply FreeStepsH.step_decode (d_184784 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184787 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184789 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184792 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184794 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184796 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 3386 184802 (sp - 56)
      (sp - 56 + 24) (ptr + 1) 3 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 24)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1692]
    case mbt => exact bs_184802
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
      exact hwf a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g5, g6, g7⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g5 g6 g7
      simp only [memcpyFrame, PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', UInt64.toNat_ofNat]
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32, hrest]
      rw [show Num.encodeLE 3 (n % 16777216) = [UInt8.ofNat (n % 16777216 % 256), UInt8.ofNat (n % 16777216 / 256 % 256), UInt8.ofNat (n % 16777216 / 256 / 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_184802 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184805 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184807 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184810 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_184813 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184816 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184819 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184821 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184824 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184827 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184830 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184833 (p := p) (P := P))
        · pvm_simp [bitwise_andInv_high (s := 4)]
        apply FreeStepsH.step_decode (d_184836 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184839 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184842 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184845 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184848 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl
      case post₂ => decode_post [h0, h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide


/-- **Decoding a 5-octet ℰ(n)**, 268435456 ≤ n < 34359738368: the prefix octet 240 + ⌊n / 2^32⌋, then
    ℰ_4(n mod 2^32). -/
theorem decodeU32_len5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 5 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 5 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 268435456 ≤ n ∧ n < 34359738368) (hn32 : n < 4294967296)
    (hb : μ.read ptr = UInt8.ofNat (240 + n / 4294967296))
    (hrest : μ.readN (ptr + 1) 4 = Num.encodeLE 4 (n % 4294967296)) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 5 := by
  have hrf' : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 38) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_184570 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_184573 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184576 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184579 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_184582 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_184585 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184588 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184592 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184593 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_184595 (p := p) (P := P))
    · pvm_simp [hra0, hb]
    apply FreeStepsH.step_decode (d_184597 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184600 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184603 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184605 (p := p) (P := P))
    · pvm_simp [h7, hwr]
    apply FreeStepsH.step_decode (d_184608 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184612 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184616 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184665 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184667 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184677 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_184680 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184688 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 5)]
    apply FreeStepsH.step_decode (d_184691 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184699 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 4)]
    apply FreeStepsH.step_decode (d_184702 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184710 (p := p) (P := P))
    · pvm_simp [bitwise_and_pow2 (k := 3)]
    apply FreeStepsH.step_decode (d_184713 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184716 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184719 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184753 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184756 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184781 (p := p) (P := P))
    · pvm_simp [hwf, h7]
    apply FreeStepsH.step_decode (d_184784 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184787 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184789 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184792 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_184794 (p := p) (P := P))
    · pvm_simp [hwf]
    apply FreeStepsH.step_decode (d_184796 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 3386 184802 (sp - 56)
      (sp - 56 + 24) (ptr + 1) 4 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 24)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_1692]
    case mbt => exact bs_184802
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
      exact hwf a (by omega) (by omega)
    case k =>
      intro ω₂ ⟨g0, g1, g5, g6, g7⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g5 g6 g7
      simp only [memcpyFrame, PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', UInt64.toNat_ofNat]
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32, hrest]
      rw [show Num.encodeLE 4 (n % 4294967296) = [UInt8.ofNat (n % 4294967296 % 256), UInt8.ofNat (n % 4294967296 / 256 % 256), UInt8.ofNat (n % 4294967296 / 256 / 256 % 256), UInt8.ofNat (n % 4294967296 / 256 / 256 / 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_184802 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184805 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184807 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184810 (p := p) (P := P))
        · pvm_simp [g5, g6]
        apply FreeStepsH.step_decode (d_184813 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184816 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184819 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184821 (p := p) (P := P))
        · pvm_simp [hwr]
        apply FreeStepsH.step_decode (d_184824 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184827 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184830 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184833 (p := p) (P := P))
        · pvm_simp [bitwise_andInv_high (s := 3)]
        apply FreeStepsH.step_decode (d_184836 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_184839 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184842 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184845 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184848 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184852 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184853 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_184855 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184858 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184861 (p := p) (P := P))
        · pvm_simp [g1, hrf']
        apply FreeStepsH.step_decode (d_184864 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_184867 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl
      case post₂ => decode_post [h0, h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide


theorem encodeNat_len1 (n : Nat) (h : 1 ≤ n ∧ n < 128) :
    Blob.encodeNat n = UInt8.ofNat (0 + n / 1) :: Num.encodeLE 0 (n % 1) := by
  have hn0 : n ≠ 0 := by omega
  simp only [Blob.encodeNat, hn0, ite_false, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.find?_cons]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
    Bool.true_and, Bool.false_and, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Bool.false_eq_true, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.mul_one]

theorem encodeNat_len2 (n : Nat) (h : 128 ≤ n ∧ n < 16384) :
    Blob.encodeNat n = UInt8.ofNat (128 + n / 256) :: Num.encodeLE 1 (n % 256) := by
  have hn0 : n ≠ 0 := by omega
  simp only [Blob.encodeNat, hn0, ite_false, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.find?_cons]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
    Bool.true_and, Bool.false_and, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Bool.false_eq_true, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.mul_one]

theorem encodeNat_len3 (n : Nat) (h : 16384 ≤ n ∧ n < 2097152) :
    Blob.encodeNat n = UInt8.ofNat (192 + n / 65536) :: Num.encodeLE 2 (n % 65536) := by
  have hn0 : n ≠ 0 := by omega
  simp only [Blob.encodeNat, hn0, ite_false, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.find?_cons]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
    Bool.true_and, Bool.false_and, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Bool.false_eq_true, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.mul_one]

theorem encodeNat_len4 (n : Nat) (h : 2097152 ≤ n ∧ n < 268435456) :
    Blob.encodeNat n = UInt8.ofNat (224 + n / 16777216) :: Num.encodeLE 3 (n % 16777216) := by
  have hn0 : n ≠ 0 := by omega
  simp only [Blob.encodeNat, hn0, ite_false, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.find?_cons]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
    Bool.true_and, Bool.false_and, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Bool.false_eq_true, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.mul_one]

theorem encodeNat_len5 (n : Nat) (h : 268435456 ≤ n ∧ n < 34359738368) :
    Blob.encodeNat n = UInt8.ofNat (240 + n / 4294967296) :: Num.encodeLE 4 (n % 4294967296) := by
  have hn0 : n ≠ 0 := by omega
  simp only [Blob.encodeNat, hn0, ite_false, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.find?_cons]
  simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.and_true, Bool.and_false,
    Bool.true_and, Bool.false_and, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
    Bool.false_eq_true, Nat.mul_zero, Nat.pow_zero, Nat.zero_add, Nat.mul_one]

/-- **The SDK's `u32` decoder** (184570): if the reader's octets at `ptr` are ℰ(n) for some
    n < 2^32, within `len`, the call returns ω₇ = 0 and ω₈ = n with the reader advanced past
    ℰ(n), for every encoding width (`DecodeOk`). -/
theorem decodeU32 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 3426 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hrf : rd + 16 ≤ sp - 104 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 104 ∨ sp ≤ ptr)
    (hpr : ptr + 16 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : n < 4294967296)
    (hlen : (Blob.encodeNat n).length ≤ len ∧ len < 4294967296)
    (hra : ∀ a, ptr ≤ a → a < ptr + (Blob.encodeNat n).length → μ.readable a = true)
    (hbytes : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    ∃ ω' μ', FreeStepsH p R 184570 ω μ x t ω' μ' x 300 ∧
      DecodeOk ω ω' μ μ' sp rd ptr len n (Blob.encodeNat n).length := by
  rcases Nat.eq_zero_or_pos n with h0n | h0n
  · subst h0n
    simp only [show Blob.encodeNat 0 = [0] by simp [Blob.encodeNat], List.length_cons,
      List.length_nil] at hlen hra hbytes ⊢
    have hb : μ.read ptr = 0 := by simpa [Memory.readN] using hbytes
    exact decodeU32_zero (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr ⟨by omega, hlen.2⟩ hrf hpf hpr hwf hwr (hra ptr (by omega) (by omega)) hR0 hR8 hb
  rcases Nat.lt_or_ge n 128 with h1n | h1n
  · rw [encodeNat_len1 n ⟨h0n, h1n⟩] at hlen hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE, Nat.div_one, Nat.zero_add] at hlen hra hbytes ⊢
    have hb : μ.read ptr = UInt8.ofNat n := by simpa [Memory.readN, Num.encodeLE] using hbytes
    exact decodeU32_one (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr ⟨by omega, hlen.2⟩ hrf hpf hpr hwf hwr (hra ptr (by omega) (by omega)) hR0 hR8 n
      ⟨h0n, h1n⟩ hb
  rcases Nat.lt_or_ge n 16384 with h2 | h2
  · rw [encodeNat_len2 n ⟨by omega, h2⟩] at hlen hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hlen hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeU32_len2 (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, h2⟩ hn hb hrest
  rcases Nat.lt_or_ge n 2097152 with h3 | h3
  · rw [encodeNat_len3 n ⟨by omega, h3⟩] at hlen hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hlen hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeU32_len3 (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, h3⟩ hn hb hrest
  rcases Nat.lt_or_ge n 268435456 with h4 | h4
  · rw [encodeNat_len4 n ⟨by omega, h4⟩] at hlen hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hlen hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeU32_len4 (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, h4⟩ hn hb hrest
  rcases Nat.lt_or_ge n 34359738368 with h5 | h5
  · rw [encodeNat_len5 n ⟨by omega, h5⟩] at hlen hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hlen hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeU32_len5 (p := p) (P := P) (R := R) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, h5⟩ hn hb hrest
  · omega

end Services.Witness
