import Services.Bootstrap.Encode.Writer

/-!
# The length prefix (30977), for fewer than 128 elements

The sequence codec (GP v0.8.0 Appendix C.1) prefixes a sequence with its length ℰ(n), the general natural
encoding. The function at 30977 encodes the 32-bit count at ω₇ onto the writer at ω₈. It opens a
56-octet frame (ω₀, ω₅, ω₆ at sp + 48, + 40, + 32), computes the powers of two it compares against by
loops of fixed length, and then:

* n = 0: appends the octet 0 (31112, `pz`);
* 0 < n < 2^7: appends the octet n (31100, `pb`), then the n mod 1 = 0 further octets (31342, `pc`).

`prefix_small` composes these with `Vec<u8>::extend_from_slice` (`Writer.extend_ok`): ℰ(n) = [n] for
n < 128.
-/

namespace Services.Bootstrap.Encode.Prefix

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 30977 … 31029, for n ≠ 0: the frame at sp = F − 56 with ω₀, ω₅, ω₆ saved, the count n read from c
    and the writer v kept in ω₂; ω₈ = 2^7 for the comparison. -/
theorem pa {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F c v ret r5 r6 n : Nat) (hF : 65536 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616) (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c)
    (hn : rdN μ c 4 = n) (hn0 : n ≠ 0)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x 31029 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[2] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[8] = UInt64.ofNat 128 ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn4 : n < 4294967296 := by rw [← hn]; exact rdN_lt μ c 4
  have hn0' : ¬ n = 0 := hn0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hF, hc, hcF, hw, hr, hrc, hn, hn0', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
      show F - 56 + 32 = F - 24 by omega]
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt (show n < 18446744073709551616 by omega)])

/-- 31029 … 31100, for 0 < n < 2^7: the octet n goes to sp + 24, the writer v to sp + 16 and the length
    of the rest, 0, to sp + 8; the function calls `Vec<u8>::extend_from_slice` for the octet (return
    address 1466 → 31106), with n in ω₅ and 1 in ω₆. -/
theorem pb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hn : 0 < n ∧ n < 128)
    (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat n)
    (h8 : ω[8] = UInt64.ofNat 128)
    (hw : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 31029 ω μ x 58508 ω' μ' x 60 ∧
      ω'[0] = UInt64.ofNat 1466 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat n] ∧ μ'.readN (sp + 16) 8 = Num.encodeLE 8 v ∧
      μ'.readN (sp + 8) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp + 8 ∨ sp + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hn' : n < 18446744073709551616 := by omega
  have hge : ¬ 128 ≤ n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h2, h6, h8, hsp, hw, hge, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h2, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hn']
    post_simp
    all_goals try assumption
    all_goals try (simp only [Num.encodeLE]; congr 2; omega)

/-- 31106 … 31342: back from the octet, the function reloads the writer from sp + 16, puts the n mod 1 = 0
    further octets at sp + 24 and calls `Vec<u8>::extend_from_slice` for their number, 0, from sp + 8
    (return address 1472 → 31348). -/
theorem pc {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v n : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat 1)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 0)
    (hw : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 31106 ω μ x 58508 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1472 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat v ∧
      ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 hv s16
  have r8 := rd8 (by decide) s8
  have hr : ∀ a, sp + 8 ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hsp, hw, hr, r16, r8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    post_simp
    all_goals try assumption

/-- 30977 … 31123, for n = 0: the frame, the octet 0 at sp + 24 and the call of
    `Vec<u8>::extend_from_slice` for it (return address 1468 → 31129). -/
theorem pz {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F c v ret r5 r6 : Nat) (hF : 65536 + 56 ≤ F ∧ F < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hret : ret < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hv : v < 18446744073709551616) (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 56 ∨ F ≤ c)
    (hn : rdN μ c 4 = 0)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (hw : ∀ a, F - 56 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x 58508 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1468 ∧ ω'[1] = UInt64.ofNat (F - 56) ∧ ω'[7] = UInt64.ofNat v ∧
      ω'[8] = UInt64.ofNat (F - 32) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (F - 32) 1 = [UInt8.ofNat 0] ∧
      μ'.readN (F - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (F - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (F - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F - 56 ≤ a → a < F → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hF, hc, hcF, hw, hr, hrc, hn, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show F - 56 + 48 = F - 8 by omega, show F - 56 + 40 = F - 16 by omega,
      show F - 56 + 32 = F - 24 by omega, show F - 56 + 24 = F - 32 by omega]
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', Nat.mod_eq_of_lt hv]; try (congr 1; omega))

/-- The function's end, from 31129 (n = 0) or 31348: ω₀, ω₅, ω₆ from the frame at sp, the frame closed,
    and the return. -/
theorem pt {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (e sp ret t r5 r6 : Nat) (he : e = 31129 ∨ e = 31348)
    (hsp : sp + 56 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (s0 : μ.readN (sp + 48) 8 = Num.encodeLE 8 ret)
    (s5 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r5) (s6 : μ.readN (sp + 32) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, sp + 32 ≤ a → a < sp + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R e ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (sp + 56) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have r0 := rd8 (by omega) s0
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  rw [show ω = regsNF ω [] from rfl]
  rcases he with rfl | rfl <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hsp, hr, r0, r5', r6', hret, hjt, hbt, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', h1]
      all_goals try (congr 1; omega)

end Services.Bootstrap.Encode.Prefix
