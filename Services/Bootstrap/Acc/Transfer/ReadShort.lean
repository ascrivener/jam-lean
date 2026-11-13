import Services.Bootstrap.Fmt.ReadExact
import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `read_exact` on a slice reader that is too short (58434, len < n)

The counterpart of `Fmt.ReadExact.read_exact` (n ≤ len): with fewer than n octets left, it returns 1
(`Err(UnexpectedEof)`) and leaves the reader untouched. `on_transfer` meets it when "transfer-count"
holds fewer than 4 octets (quirk Q12: the count then reads as 0).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- 58434 … 58491, len < n: the 40-octet frame at F = sp − 40 (ω₀, ω₅, ω₆ at + 32, + 24, + 16). -/
theorem res_a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd n len : Nat) (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : len < n) (hn64 : n < 18446744073709551616)
    (rl : rdN μ (Rd + 8) 8 = len) (hRd : Rd + 16 ≤ sp - 40 ∨ sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (hrR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.readable a = true)
    (hwf : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x 58491 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat len ∧
      rdN μ' (sp - 40 + 32) 8 = ω[0].toNat ∧ rdN μ' (sp - 40 + 24) 8 = ω[5].toNat ∧
      rdN μ' (sp - 40 + 16) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 40 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hl64 : len < 18446744073709551616 := rl ▸ rdN_lt64 μ (Rd + 8)
  have hlt : len % 18446744073709551616 < n % 18446744073709551616 := by
    rw [Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hn64]; exact hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h9, rl, hlt, hwf, hr, hrR, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val; try rw [Nat.mod_eq_of_lt hn64]), (by reg_val; try rw [rl, Nat.mod_eq_of_lt hl64]),
      ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- 58491 … the return, len < n: 1 (`Err`), ω₀, ω₅, ω₆ restored from the frame at F, which closes. -/
theorem res_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F n len r0 t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat len)
    (hn : len < n) (hn64 : n < 18446744073709551616)
    (r6 : rdN μ (F + 16) 8 = v6) (r5 : rdN μ (F + 24) 8 = v5) (r0' : rdN μ (F + 32) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 58491 ω μ x t ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 40) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 1 := by
  have hl64 : len < 18446744073709551616 := by omega
  have hlt : len % 18446744073709551616 < n % 18446744073709551616 := by
    rw [Nat.mod_eq_of_lt hl64, Nat.mod_eq_of_lt hn64]; exact hn
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hlt, r6, r5, r0', hret, hjt, hbt, hr, ↓rdN_fold]
  case post => refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩; reg_val; try simp [hlt]

/-- **`read_exact` on a slice reader that is too short** (58434, len < n): it returns 1 (an error) to
    t, the address ω₀ resolves to, with ω₀, ω₁, ω₅, ω₆ as they were and the reader untouched; memory
    changes only in its frame sp − 40 … sp. -/
theorem read_exact_short {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp Rd n len r0 t : Nat) (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat Rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : len < n) (hn64 : n < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (rl : rdN μ (Rd + 8) 8 = len) (hRd : Rd + 16 ≤ sp - 40 ∨ sp ≤ Rd) (hRd1 : Rd + 16 < 4294967296)
    (hrR : ∀ a, Rd ≤ a → a < Rd + 16 → μ.readable a = true)
    (hwf : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x 28 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 1 ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a1, a5, a6, m32, m24, m16, fr1, rd1, wr1⟩ :=
    res_a (p := p) (P := P) (R := R) x ω μ sp Rd n len hsp h1 h7 h9 hn hn64 rl hRd hRd1 hrR hwf
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ :=
    res_b (p := p) (P := P) (R := R) x ω1 μ1 (sp - 40) n len r0 t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩
      a1 a5 a6 hn hn64 m16 m24 (by rw [m32, h0, UInt64.toNat_ofNat_of_lt' (show r0 < 2 ^ 64 by have := hret.2.1; omega)]) hret hjt hbt
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega)))
  exact ⟨ω2, μ1, (run1.trans run2).mono (by omega), by rw [b0, h0], by rw [b1, h1, show sp - 40 + 40 = sp by omega],
    by rw [b5, UInt64.ofNat_toNat], by rw [b6, UInt64.ofNat_toNat], b7, fr1, rd1, wr1⟩

end Services.Bootstrap.Acc
