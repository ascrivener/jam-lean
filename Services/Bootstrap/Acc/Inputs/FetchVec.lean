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

/-- **47490 … 47541**, kind 14: the first `fetch`, with a null buffer, returns the length
    L = |ℰ(↕**i**)| in ω₇ and writes nothing; L is neither an error code nor 0, so the code moves it
    to ω₅ and calls on to 47541 (return address 2120). -/
theorem fv_fetch1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : cap < 2 ^ 64) (h287 : 287 ≤ cap) (env : AccEnv) (x : AccCtx) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat 0) (h9 : ω[9] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat 14) (hL0 : 0 < (inputsEnc env).length)
    (hL : (inputsEnc env).length < 9223372036854775808) :
    ∃ ω', FreeStepsH p (accContractK cap env) 47490 ω μ x 47541 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 2120 ∧ ω'[5] = UInt64.ofNat (inputsEnc env).length ∧
      ω'[7] = UInt64.ofNat (inputsEnc env).length ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[6] = ω[6] ∧ ω'[8] = ω[8] ∧
      ω'[9] = ω[9] ∧ ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  have r7 : reg ω 7 = 0 := by unfold reg; rw [show ω.get 7 = ω[7] from rfl, h7]; rfl
  have r8 : reg ω 8 = 0 := by unfold reg; rw [show ω.get 8 = ω[8] from rfl, h8]; rfl
  have r9 : reg ω 9 = 0 := by unfold reg; rw [show ω.get 9 = ω[9] from rfl, h9]; rfl
  have r10 : reg ω 10 = 14 := by unfold reg; rw [show ω.get 10 = ω[10] from rfl, h10]; rfl
  have hst := fetch14_step cap hcap env ω μ x 0 0 0 r7 r8 r9 r10 (by unfold memGas; omega)
    (by simp [Memory.rangeWritable])
  have hm : μ.writeN 0 (((inputsEnc env).drop (min 0 (inputsEnc env).length)).take
      (min 0 ((inputsEnc env).length - min 0 (inputsEnc env).length))) = μ := by simp
  rw [hm] at hst
  generalize hLd : (inputsEnc env).length = L at hst hL0 hL ⊢
  have e7 : (setR7 ω L)[7] = UInt64.ofNat L := by
    unfold setR7; rw [Vector.getElem_set]; simp
  have eo : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (setR7 ω L)[j] = ω[j] := by
    intro j hj h; unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]
  rw [show setR7 ω L = regsNF (setR7 ω L) [] from rfl] at hst
  refine ⟨?ω', FreeStepsH.host_decode (d_47490 (p := p) (P := P)) hst ?run, ?post⟩
  case run =>
    pvm_go [e7, Nat.mod_eq_of_lt (show L < 18446744073709551616 by omega)]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, e7]
    all_goals try rfl
    all_goals first
      | exact eo _ (by decide) (by decide)
      | simp only [UInt64.ofNat_toNat]

end Services.Bootstrap.Acc
