import Services.Witness.DecodeU32

/-!
# Witness's inline decode of the core index, summarized

From pc 43276 (step 702 of refine), witness decodes the core index c from its argument reader
(ω₈ = the arguments' start, ω₇ = their length L) in the natural encoding ℰ (GP (C)), checks
c < 2^16, and calls the `u32` decoder at 184570 with the reader advanced past ℰ(c) at ω₁ + 16.
The decode is the SDK's, inlined: the prefix octet, then the remaining octets copied by `memcpy`
into a zeroed buffer at ω₁ + 40. This file proves it for every c < 2^16, by the width of ℰ(c).
-/

namespace Services.Witness

open PVM Services.Witness.Code

set_option maxHeartbeats 4000000

variable {X : Type} {R : HostRel X}

/-- What the decode of the core index leaves at the call to the `u32` decoder: ω₀ the return
    address 842, ω₁ as it was, ω₅ and the reader {ptr + w, L − w} at ω₇ = sp + 16 advanced by
    the width `w` of ℰ(c), and memory unchanged outside [sp − 48, sp + 48), with the same page
    access. -/
def DecodeCOk (ω ω' : Regs) (μ μ' : Memory) (sp ptr L w : Nat) : Prop :=
  ω'[0] = UInt64.ofNat 842 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (ptr + w) ∧
    ω'[7] = UInt64.ofNat (sp + 16) ∧ μ'.readN (sp + 16) 8 = Num.encodeLE 8 (ptr + w) ∧
    μ'.readN (sp + 24) 8 = Num.encodeLE 8 (L - w) ∧
    (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp + 48 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- Prove `DecodeCOk` of a concrete final state. -/
macro "decodec_post" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩ <;>
  try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, memcpyFrame,
    PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint,
    PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE,
    PVM.Memory.length_readN, List.length_cons, List.length_nil, PVM.two32, PVM.mul_one', PVM.sub_zero',
    Nat.mod_add_div, Nat.div_add_mod', Nat.mod_mod, Nat.sub_sub, Nat.reduceAdd, $hs,*]))

/-- **The core-index decode of ℰ(0) = [0]: the first octet is 0, and the decode skips the copy.** -/
theorem decodeC_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat ptr)
    (hsp : 65536 + 48 ≤ sp ∧ sp + 64 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hpf : ptr + 16 ≤ sp - 48 ∨ sp + 48 ≤ ptr)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 1 → μ.readable a = true) (hL : 1 ≤ L ∧ L < 4294967296)
    (hb : μ.read ptr = 0) :
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 184570 ω' μ' x 300 ∧ DecodeCOk ω ω' μ μ' sp ptr L 1 := by
  have hrf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    apply FreeStepsH.step_decode (d_43276 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43278 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43281 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43284 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43287 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43290 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43485 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43488 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    exact FreeStepsH.refl.mono (Nat.zero_le _)
  case post => decodec_post [h1]

/-- **The core-index decode of a 1-octet ℰ(C), 0 < C < 128: no further octets are copied.** -/
theorem decodeC_one {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat ptr)
    (hsp : 65536 + 48 ≤ sp ∧ sp + 64 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hpf : ptr + 16 ≤ sp - 48 ∨ sp + 48 ≤ ptr)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 1 → μ.readable a = true) (hL : 1 ≤ L ∧ L < 4294967296)
    (C : Nat) (hC : 0 < C ∧ C < 128) (hb : μ.read ptr = UInt8.ofNat C) :
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 184570 ω' μ' x 300 ∧ DecodeCOk ω ω' μ μ' sp ptr L 1 := by
  have hrf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 19) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_43276 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43278 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43281 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43284 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43287 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43290 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43294 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43298 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43324 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43326 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43329 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43331 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43334 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43336 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43339 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43425 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43428 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43430 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43432 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 840 43439 sp
      (sp + 40) (ptr + 1) 0 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf (fun a h1 h2 => by omega) (fun a h1 h2 => by omega)) ?k ?hle2 (n₂ := 18)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_419]
    case mbt => exact bs_43439
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
        apply FreeStepsH.step_decode (d_43439 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43441 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43444 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43447 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43450 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43453 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43456 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43459 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43462 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43465 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf, bitwise_andInv_high (s := 7)]
        apply FreeStepsH.step_decode (d_43468 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43471 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43474 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43477 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43478 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43481 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43485 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43488 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        exact FreeStepsH.refl
      case post₂ => decodec_post [h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide

/-- **The core-index decode of a 2-octet ℰ(C), 128 ≤ C < 2^14: the prefix octet 128 + ⌊C / 2^8⌋, then ℰ_1(C mod 2^8).** -/
theorem decodeC_len2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat ptr)
    (hsp : 65536 + 48 ≤ sp ∧ sp + 64 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hpf : ptr + 16 ≤ sp - 48 ∨ sp + 48 ≤ ptr)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 2 → μ.readable a = true) (hL : 2 ≤ L ∧ L < 4294967296)
    (C : Nat) (hC : 128 ≤ C ∧ C < 16384) (hb : μ.read ptr = UInt8.ofNat (128 + C / 256))
    (hrest : μ.readN (ptr + 1) 1 = Num.encodeLE 1 (C % 256)) :
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 184570 ω' μ' x 300 ∧ DecodeCOk ω ω' μ μ' sp ptr L 2 := by
  have hrf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 22) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_43276 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43278 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43281 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43284 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43287 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43290 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43294 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43298 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43324 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43326 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43329 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43331 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43341 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb, bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_43344 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43347 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43350 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43418 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43421 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43425 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43428 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43430 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43432 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 840 43439 sp
      (sp + 40) (ptr + 1) 1 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 18)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_419]
    case mbt => exact bs_43439
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
      rw [show Num.encodeLE 1 (C % 256) = [UInt8.ofNat (C % 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_43439 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43441 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43444 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43447 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43450 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43453 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43456 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43459 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43462 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43465 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf, bitwise_andInv_high (s := 6)]
        apply FreeStepsH.step_decode (d_43468 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43471 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43474 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43477 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43478 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43481 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43485 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43488 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        exact FreeStepsH.refl
      case post₂ => decodec_post [h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide

/-- **The core-index decode of a 3-octet ℰ(C), 2^14 ≤ C < 2^16: the prefix octet 192 + ⌊C / 2^16⌋ = 192, then ℰ_2(C).** -/
theorem decodeC_len3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat ptr)
    (hsp : 65536 + 48 ≤ sp ∧ sp + 64 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hpf : ptr + 16 ≤ sp - 48 ∨ sp + 48 ≤ ptr)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 3 → μ.readable a = true) (hL : 3 ≤ L ∧ L < 4294967296)
    (C : Nat) (hC : 16384 ≤ C ∧ C < 65536) (hb : μ.read ptr = UInt8.ofNat (192 + C / 65536))
    (hrest : μ.readN (ptr + 1) 2 = Num.encodeLE 2 (C % 65536)) :
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 184570 ω' μ' x 300 ∧ DecodeCOk ω ω' μ μ' sp ptr L 3 := by
  have hrf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hra0 : μ.readable ptr = true := hra ptr (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 186740) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 24) (n₂ := 250) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_43276 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43278 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43281 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43284 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43287 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43290 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43294 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43298 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43324 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43326 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43329 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43331 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43341 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb, bitwise_and_pow2 (k := 6)]
    apply FreeStepsH.step_decode (d_43344 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43352 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb, bitwise_and_pow2 (k := 5)]
    apply FreeStepsH.step_decode (d_43355 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43358 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43361 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43418 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43421 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43425 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43428 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43430 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    apply FreeStepsH.step_decode (d_43432 (p := p) (P := P))
    · pvm_simp [h1, h7, h8, hwf, hrf, hra0, hb]
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex (memcpy_small (p := p) (P := P) (R := R) x _ _ 840 43439 sp
      (sp + 40) (ptr + 1) 2 ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) (by decide) ?mjt ?mbt (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mr ?mw) ?k ?hle2 (n₂ := 18)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_419]
    case mbt => exact bs_43439
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
      rw [show Num.encodeLE 2 (C % 65536) = [UInt8.ofNat (C % 65536 % 256), UInt8.ofNat (C % 65536 / 256 % 256)] by simp [Num.encodeLE]]
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_43439 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43441 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43444 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43447 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43450 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43453 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43456 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43459 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43462 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43465 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf, bitwise_andInv_high (s := 5)]
        apply FreeStepsH.step_decode (d_43468 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43471 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43474 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43477 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43478 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43481 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43485 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        apply FreeStepsH.step_decode (d_43488 (p := p) (P := P))
        · pvm_simp [h1, g0, g1, g5, g6, g7, hwf, hrf]
        exact FreeStepsH.refl
      case post₂ => decodec_post [h1, g0, g1, g5, g6]
    case hle2 => decide
  case hle => decide

/-- **Witness's decode of the core index**, for every c < 2^16: from pc 43276 with the argument
    reader {ptr, L} in ω₈ and ω₇ and ℰ(c) at ptr, the machine reaches the call to the `u32`
    decoder with `DecodeCOk`, the reader advanced past ℰ(c). -/
theorem decodeC {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp ptr L : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat ptr)
    (hsp : 65536 + 48 ≤ sp ∧ sp + 64 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hpf : ptr + 16 ≤ sp - 48 ∨ sp + 48 ≤ ptr)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp + 48 → μ.writable a = true)
    (C : Nat) (hC : C < 65536)
    (hra : ∀ a, ptr ≤ a → a < ptr + (Blob.encodeNat C).length → μ.readable a = true)
    (hL : (Blob.encodeNat C).length ≤ L ∧ L < 4294967296)
    (hbytes : μ.readN ptr (Blob.encodeNat C).length = Blob.encodeNat C) :
    ∃ ω' μ', FreeStepsH p R 43276 ω μ x 184570 ω' μ' x 300 ∧
      DecodeCOk ω ω' μ μ' sp ptr L (Blob.encodeNat C).length := by
  rcases Nat.eq_zero_or_pos C with h0n | h0n
  · subst h0n
    simp only [show Blob.encodeNat 0 = [0] by simp [Blob.encodeNat], List.length_cons,
      List.length_nil] at hL hra hbytes ⊢
    have hb : μ.read ptr = 0 := by simpa [Memory.readN] using hbytes
    exact decodeC_zero (p := p) (P := P) (R := R) x ω μ sp ptr L h1 h7 h8 hsp hptr hpf hwf hra hL hb
  rcases Nat.lt_or_ge C 128 with h1n | h1n
  · rw [encodeNat_len1 C ⟨h0n, h1n⟩] at hL hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE, Nat.div_one, Nat.zero_add] at hL hra hbytes ⊢
    have hb : μ.read ptr = UInt8.ofNat C := by simpa [Memory.readN, Num.encodeLE] using hbytes
    exact decodeC_one (p := p) (P := P) (R := R) x ω μ sp ptr L h1 h7 h8 hsp hptr hpf hwf hra hL C
      ⟨h0n, h1n⟩ hb
  rcases Nat.lt_or_ge C 16384 with h2 | h2
  · rw [encodeNat_len2 C ⟨by omega, h2⟩] at hL hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hL hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeC_len2 (p := p) (P := P) (R := R) x ω μ sp ptr L h1 h7 h8 hsp hptr hpf hwf hra hL C
      ⟨by omega, h2⟩ hb hrest
  · rw [encodeNat_len3 C ⟨by omega, by omega⟩] at hL hra hbytes ⊢
    simp only [List.length_cons, PVM.Num.length_encodeLE] at hL hra hbytes ⊢
    rw [readN_succ] at hbytes
    obtain ⟨hb, hrest⟩ := List.cons.inj hbytes
    exact decodeC_len3 (p := p) (P := P) (R := R) x ω μ sp ptr L h1 h7 h8 hsp hptr hpf hwf hra hL C
      ⟨by omega, hC⟩ hb hrest

end Services.Witness
