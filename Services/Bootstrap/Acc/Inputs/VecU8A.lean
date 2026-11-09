import Services.Bootstrap.Acc.Inputs.ReadVecCall
import Services.Bootstrap.Acc.DecodeU32A

/-!
# Accumulate's length-prefixed `Vec<u8>` decoder (39634)

39634 decodes ↕**v** (GP v0.8.0 (C)): the length n by the `u32` decoder (39710,
`decodeU32A`), then n octets by the `Vec<u8>` reader (45643, `rv_call` / `rv_empty`), into a
`Vec<u8>` at `out`; a failed length decode writes −1 at `out`. Here n ≤ 16384, one chunk: a
**temporary** bound, lifted once the realloc impl lemmas take any return address.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **39634 … 39710**: the 24-octet frame (ω₀, ω₅, ω₆ at sp − 8, − 16, − 24), `out` kept in ω₅
    and the reader in ω₆, and the call of the `u32` decoder on the reader (return address 1958). -/
theorem vv_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 65536 + 24 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 39634 ω μ x 39710 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1958 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 24 + 16 = sp - 8 from by omega, show sp - 24 + 8 = sp - 16 from by omega,
      show sp - 24 + 0 = sp - 24 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl
      | rw [Nat.mod_eq_of_lt (by omega)]

/-- **39656 … 45643**, the length decoded (ω₇ = 0, ω₈ = n < 2³²): the call of the `Vec<u8>` reader
    with ω₇ = out, ω₈ = rd, ω₉ = n (return address 1960). -/
theorem vv_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (out rd n : Nat) (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) (hn : n < 4294967296)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 39656 ω μ x 45643 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 1960 ∧ ω'[7] = UInt64.ofNat out ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat n ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h6, h7, h8]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h5, h6, h8]
    all_goals try with_reducible rfl
    all_goals first
      | rfl
      | (congr 1; omega)
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])

/-- **45950 … 39708**: the reader's return through entry 979 (1960) to 39697, ω₀, ω₅, ω₆ restored
    from the 24-octet frame and the frame popped, at the return's `jumpInd`. -/
theorem vv_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 r5 r6 : Nat) (h0 : ω[0] = UInt64.ofNat 1960) (h1 : ω[1] = UInt64.ofNat sp)
    (m0 : rdN μ sp 8 = r6) (m8 : rdN μ (sp + 8) 8 = r5) (m16 : rdN μ (sp + 16) 8 = r0)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hr0 : r0 < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 45950 ω μ x 39708 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h1, m0, m8, m16, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals first
      | with_reducible rfl
      | rfl
      | (congr 1; omega)

end Services.Bootstrap.Acc
