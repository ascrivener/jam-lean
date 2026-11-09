import Services.Bootstrap.Acc.Inputs.FetchStep
import Services.Bootstrap.CodeAAll
import PVM.Logic.Go

/-!
# The SDK's `fetch_vec` (47417) for the accumulate inputs, in segments

`fetch_vec(kind)` at 47417 fetches a value into a fresh zeroed `Vec<u8>` in two phases: a
`fetch` with a null buffer for the length L (47490), then the block (`alloc_impl`, 41177, under the
allocator's lock), then a second `fetch` into it (47690). Kind 14 (the inputs ℰ(↕**i**), GP v0.8.0
eq. `fetch`) is in the no-argument mask 20359, so both calls pass ω₁₁ = ω₁₂ = 0.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **47417 … 47490**, kind 14: the frame of 64 octets (ω₀, ω₅, ω₆ and `out` saved), the kind and
    its two argument words copied to sp − 40 … sp − 56, and the registers of a `fetch` with a null
    buffer: ω₇ = ω₈ = ω₉ = 0, ω₁₀ = 14, ω₁₁ = ω₁₂ = 0. -/
theorem fv_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out args a1 a2 : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat args)
    (hsp : 65536 + 64 ≤ sp ∧ sp < 4294967296) (hargs : 65536 ≤ args ∧ args + 24 < 4294967296) (hdis : sp ≤ args)
    (hout : out < 18446744073709551616)
    (r0 : μ.readN args 8 = Num.encodeLE 8 14) (r1 : μ.readN (args + 8) 8 = Num.encodeLE 8 a1)
    (r2 : μ.readN (args + 16) 8 = Num.encodeLE 8 a2) (ha1 : a1 < 18446744073709551616)
    (ha2 : a2 < 18446744073709551616)
    (hra : ∀ a, args ≤ a → a < args + 24 → μ.readable a = true)
    (hwf : ∀ a, sp - 64 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47417 ω μ x 47490 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 14 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ω'[12] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 32) 8 = Num.encodeLE 8 out ∧
      μ'.readN (sp - 40) 8 = Num.encodeLE 8 14 ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, r0, r1, r2, hra, hwf, hr]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try rfl
    all_goals try simp only [show sp - 64 + 56 = sp - 8 from by omega, show sp - 64 + 48 = sp - 16 from by omega,
      show sp - 64 + 40 = sp - 24 from by omega, show sp - 64 + 32 = sp - 32 from by omega,
      show sp - 64 + 24 = sp - 40 from by omega]
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try rfl
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

end Services.Bootstrap.Acc
