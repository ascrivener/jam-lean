import Services.Bootstrap.Acc.Handlers.KeyEnc
import Services.Bootstrap.Encode.VecCore

/-!
# The results store (36170)

`on_work_item`'s results (rows 9 and 11, GP v0.8.0 B.7's storage write Ω_W) go through the function
at 36170: with the n results at rp (ω₇, 144-octet items), their count n (ω₈) and a storage key value
at kp (ω₉), it allocates 4 + 144 · n octets, writes ℰ(n) (`prefix_any`) and each result's encoding,
builds the key (33843, `KeyEnc.kb_call`), stores the value under the key (`set`, 48104), frees both
buffers and returns the `set` outcome's tag in ω₇.

`rs_pre`: the prologue, to the `alloc` call.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **36170 … 40494**: the frame of 96 octets at S = sp − 96 (ω₀, ω₅, ω₆ saved at S + 88, S + 80,
    S + 72; kp at S + 16, n at S + 24, the size 144 · n + 4 at S + 8), rp in ω₆, 144 · n in ω₅ and the
    call `alloc(144 · n + 4, 1)` with return address 1692. -/
theorem rs_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp rp n kp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rp)
    (h8 : ω[8] = UInt64.ofNat n) (h9 : ω[9] = UInt64.ofNat kp) (hsp : 65536 + 96 ≤ sp ∧ sp < 4294967296)
    (hrp : rp < 18446744073709551616) (hn : 144 * n + 4 < 4294967296) (hkp : kp < 18446744073709551616)
    (hw : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36170 ω μ x 40494 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1692 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat (144 * n) ∧
      ω'[6] = UInt64.ofNat rp ∧ ω'[7] = UInt64.ofNat (144 * n + 4) ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 80) 8 = Num.encodeLE 8 kp ∧
      μ'.readN (sp - 72) 8 = Num.encodeLE 8 n ∧ μ'.readN (sp - 88) 8 = Num.encodeLE 8 (144 * n + 4) ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h8, h9, hsp, hrp, hn, hkp, hw, bs_40494, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, ?_, by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try rw [show sp - 96 + 88 = sp - 8 by omega, show sp - 96 + 80 = sp - 16 by omega,
      show sp - 96 + 72 = sp - 24 by omega, show sp - 96 + 16 = sp - 80 by omega,
      show sp - 96 + 24 = sp - 72 by omega, show sp - 96 + 8 = sp - 88 by omega]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.ResStore
