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
    all_goals try (congr 2; omega)

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
    · rw [rdN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32]; omega) (by simp [two32]; omega), r8]
    · exact Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32]; omega) (by simp [two32]; omega)
    · rw [Memory.readable_writeN]
    · rw [Memory.writable_writeN]

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

/-- **The length prefix of 0 < n < 2^7 elements** (30977): called with ω₁ = F, the 32-bit count n at c
    (ω₇) and the writer `{cap, ptr, len}` at v (ω₈) with room for an octet, the function appends the one
    octet n (ℰ(n) = [n], GP v0.8.0 Appendix C) and stores `len + 1`, and returns to `ret` with ω₁ = F and
    ω₅, ω₆ as they were. Memory changes only in [F − 136, F), the octet appended and the writer's
    length. -/
theorem prefix_small {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F c v cap ptr len ret t r5 r6 n : Nat) (hF : 65536 + 256 ≤ F ∧ F < 4294967296 ∧ F % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 136 ∨ F ≤ c) (hn : rdN μ c 4 = n) (hn1 : 0 < n ∧ n < 128)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len) (hroom : len + 1 ≤ cap) (hcap : cap < 18446744073709551616)
    (hv : v + 24 ≤ 4294967296) (hvF : v + 24 ≤ F - 136 ∨ F ≤ v)
    (hd : 65536 ≤ ptr + len ∧ ptr + len + 17 < 4294967296) (hdF : F ≤ ptr + len ∨ ptr + len + 17 ≤ F - 136)
    (hdv : v + 24 ≤ ptr + len ∨ ptr + len + 1 ≤ v)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true)
    (hwd : ∀ a, ptr + len ≤ a → a < ptr + len + 1 → μ.writable a = true)
    (hwF : ∀ a, F - 136 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x t ω' μ' x 900 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN (ptr + len) 1 = [UInt8.ofNat n] ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + 1) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + 1 ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hret' : ret < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, run1, a1, a2, a6, a8, a0', a5', a6', afr, ard, awr⟩ := pa (p := p) (P := P) (R := R) x ω μ
    F c v ret r5 r6 n ⟨by omega, hF1⟩ h0 h1 h5 h6 h7 h8 hret' hr5 hr6 (by omega) hc (by omega) hn (by omega)
    hrc (fun a h1 h2 => hwF a (by omega) h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bo, bv, bz, bfr, brd, bwr⟩ := pb (p := p) (P := P) (R := R) x
    ω1 μ1 (F - 56) v n (by omega) (by omega) hn1 a1 a2 a6 a8
    (fun a h1 h2 => by rw [awr]; exact hwF a (by omega) (by omega))
  -- outside the function's frame, μ2 is μ
  have k2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ2.read a = μ.read a := fun a h0 h1 => by
    rw [bfr a h0 (by omega), afr a h0 h1]
  have k2v : ∀ a, v ≤ a → a < v + 24 → μ2.read a = μ.read a := fun a h1 h2 => k2 a (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω2 μ2
    (F - 56) v (F - 56 + 24) 1 cap ptr len 1466 31106 ⟨by omega, by omega, by omega⟩ b0 b1 b7 b8 b9 hroom hcap
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vc)
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vp)
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vl)
    hv (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) hdv
    ⟨by decide, by decide, by decide⟩ jte_732 bs_31106
    (fun a h1 h2 => by rw [brd, ard]; exact hrv a h1 h2)
    (fun a h1 h2 => by rw [bwr, awr]; exact hwv a h1 h2)
    (fun a h1 h2 => by rw [brd, ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
    (fun a h1 h2 => by rw [bwr, awr]; exact hwd a h1 h2)
    (fun a h1 h2 => by rw [bwr, awr]; exact hwF a (by omega) (by omega))
  -- the function's frame [F − 56, F) is kept by the call
  have k3 : ∀ a, F - 56 ≤ a → a < F → μ3.read a = μ2.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω4, μ4, run4, d0, d1, d7, d8, d9, dfr, drd, dwr⟩ := pc (p := p) (P := P) (R := R) x ω3 μ3 (F - 56) v n
    (by omega) (by omega) (by omega) c1 (c5.trans b5) (c6.trans b6)
    (by rw [show F - 56 + 16 = F - 40 by omega, Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
      ← show F - 56 + 16 = F - 40 by omega]; exact bv)
    (by rw [show F - 56 + 8 = F - 48 by omega, Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
      ← show F - 56 + 8 = F - 48 by omega]; exact bz)
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact hwF a (by omega) (by omega))
  have k4v : ∀ a, v ≤ a → a < v + 24 → μ4.read a = μ3.read a := fun a h1 h2 => dfr a (by omega) (by omega)
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, _, el, efr, erd, ewr⟩ := extend_ok (p := p) (P := P) (R := R) x ω4 μ4
    (F - 56) v (F - 56 + 24) 0 cap ptr (len + 1) 1472 31348 ⟨by omega, by omega, by omega⟩ d0 d1 d7 d8 d9
    (by omega) hcap
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vc)
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vp)
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega))]; exact cl)
    hv (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_735 bs_31348
    (fun a h1 h2 => by rw [drd, crd, brd, ard]; exact hrv a h1 h2)
    (fun a h1 h2 => by rw [dwr, cwr, bwr, awr]; exact hwv a h1 h2)
    (fun a h1 h2 => by omega)
    (fun a h1 h2 => by omega)
    (fun a h1 h2 => by rw [dwr, cwr, bwr, awr]; exact hwF a (by omega) (by omega))
  -- the saved words, through everything
  have k5 : ∀ a, F - 24 ≤ a → a < F → μ5.read a = μ1.read a := fun a h1 h2 => by
    rw [efr a (by omega) (by omega) (by omega) (by omega), dfr a (by omega) (by omega), k3 a (by omega) h2,
      bfr a (by omega) (by omega)]
  obtain ⟨ω6, run6, f0, f1, f5, f6⟩ := pt (p := p) (P := P) (R := R) x ω5 μ5 31348 (F - 56) ret t r5 r6
    (Or.inr rfl) (by omega) e1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a6')
    hr5 hr6 hret hjt hbt
    (fun a h1 h2 => by rw [erd, drd, crd, brd, ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
  refine ⟨ω6, μ5, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    f0, by rw [f1]; congr 1; omega, f5, f6, ?_, by simpa using el, fun a h0' h1' h2' h3' => ?_,
    fun a => by rw [erd, drd, crd, brd, ard], fun a => by rw [ewr, dwr, cwr, bwr, awr]⟩
  · rw [Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)), cd, show F - 56 + 24 = F - 32 by omega]
    rw [show F - 32 = F - 56 + 24 by omega]; exact bo
  · rw [efr a h0' (by omega) (by omega) h3', dfr a h0' (by omega), cfr a h0' (by omega) h2' h3', k2 a h0' (by omega)]

end Services.Bootstrap.Encode.Prefix
