import Services.Bootstrap.Acc.Handlers.ResStoreSeg

/-!
# The results store (36170), n ≥ 1: the loop's straight-line segments

The loop 36346 … 36402 appends each 144-octet item's encoding (`ResultsAt`) to the value `Vec` at
S + 32 (S = sp − 96, the callee frame), with ω₅ = 144 · (items left) and ω₆ the item's address:
- `rl_enter` (36263 → 36346): n ≠ 0 at S + 24;
- `rl_ok` (36346 → 58508): the item's first octet is not 255 (`Ok`): extend by the octet 0 (staged at
  S + 56, return address 1696 → 36290); `rl_okenc` (36290 → 36299): the call of the `Ok` encoder with
  ω₇ = the item, ω₈ = S + 32 and return address 1698 (→ 36335);
- `rl_err` (36346 → 58508): the first octet is 255 (`Err`): extend by 1 (return address 1700 → 36373);
  `rl_errcode` (36373 → 58508): extend by the item's second octet (return address 1702 → 36394);
- `rl_next` (36335 or 36394 → 36346 or 36405): ω₅ −= 144, ω₆ += 144, and on while ω₅ ≠ 0;
- `rl_tail` (36405 → 33843): as `rs_zero` after its test: the value's `Vec` moved (capacity to S + 24,
  length to S + 8, ptr in ω₆) and the key encoder called with out S + 32, kp (S + 16), return 1704.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **36263, n ≠ 0** (at S + 24): on to the loop at 36346. -/
theorem rl_enter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S n : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296) (hn : n < 2 ^ 64) (hn0 : n ≠ 0)
    (mn : μ.readN (S + 24) 8 = Num.encodeLE 8 n) (hr : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 36263 ω μ x 36346 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rn := Handlers.DesignateAlloc.rd8 hn mn
  have hn0' : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hn]; exact hn0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, rn, hn0', hr, bs_36346, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val⟩

/-- **36346 … 36284, an `Ok` item** (its first octet t ≠ 255, at ω₆ = a): the octet 0 at S + 56 and the
    call of `extend` (58508) with ω₇ = S + 32, ω₈ = S + 56, ω₉ = 1 and return address 1696. -/
theorem rl_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S a t : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat a) (hS : S + 96 < 4294967296)
    (ha : a < 4294967296) (ht : t < 256) (ht1 : t ≠ 255) (mt : μ.readN a 1 = Num.encodeLE 1 t)
    (hra : μ.readable a = true) (hw : μ.writable (S + 56) = true) :
    ∃ ω' μ', FreeStepsH p R 36346 ω μ x 58508 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1696 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat (S + 56) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 56) 1 = [0] ∧
      (∀ b, b < 4294967296 → b ≠ S + 56 → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have rt : rdN μ a 1 = t := by show Num.decodeLE _ = _; rw [mt, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt ht]
  have ht1' : t ≠ 255 := ht1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, ha, rt, ht1', hra, hw, bs_36272, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, fun b hb hne => ?_,
      fun b => ?_, fun b => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [Memory.readN]
    all_goals try exact PVM.read_write_ne' _ _ _ _ hne (by omega) hb

/-- **36290 … 36295, after the octet 0**: the call of the `Ok` encoder (36299) with ω₇ = ω₆ (the item),
    ω₈ = S + 32 and return address 1698 (→ 36335). -/
theorem rl_okenc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296) :
    ∃ ω', FreeStepsH p R 36290 ω μ x 36299 ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat 1698 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] ∧
      ω'[8] = UInt64.ofNat (S + 32) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, bs_36299]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **36346 … 36367, an `Err` item** (its first octet 255, at ω₆ = a): the octet 1 at S + 56 and the call
    of `extend` with ω₇ = S + 32, ω₈ = S + 56, ω₉ = 1 and return address 1700 (→ 36373). -/
theorem rl_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S a : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat a) (hS : S + 96 < 4294967296)
    (ha : a < 4294967296) (mt : μ.readN a 1 = Num.encodeLE 1 255)
    (hra : μ.readable a = true) (hw : μ.writable (S + 56) = true) :
    ∃ ω' μ', FreeStepsH p R 36346 ω μ x 58508 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1700 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat (S + 56) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 56) 1 = [1] ∧
      (∀ b, b < 4294967296 → b ≠ S + 56 → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have rt : rdN μ a 1 = 255 := by show Num.decodeLE _ = _; rw [mt, Num.decodeLE_encodeLE]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, ha, rt, hra, hw, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, fun b hb hne => ?_,
      fun b => ?_, fun b => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [Memory.readN]
    all_goals try exact PVM.read_write_ne' _ _ _ _ hne (by omega) hb

/-- **36373 … 36388, the error code**: the item's second octet e (at a + 1, ω₆ = a) staged at S + 56 and
    the call of `extend` with ω₇ = S + 32, ω₈ = S + 56, ω₉ = 1 and return address 1702 (→ 36394). -/
theorem rl_errcode {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S a e : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat a) (hS : S + 96 < 4294967296)
    (ha : a + 1 < 4294967296) (he : e < 256) (me : μ.readN (a + 1) 1 = Num.encodeLE 1 e)
    (hra : μ.readable (a + 1) = true) (hw : μ.writable (S + 56) = true) :
    ∃ ω' μ', FreeStepsH p R 36373 ω μ x 58508 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1702 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat (S + 56) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 56) 1 = Num.encodeLE 1 e ∧
      (∀ b, b < 4294967296 → b ≠ S + 56 → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have re : rdN μ (a + 1) 1 = e := by
    show Num.decodeLE _ = _; rw [me, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt he]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, ha, re, hra, hw, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, by reg_val, ?_, fun b hb hne => ?_,
      fun b => ?_, fun b => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try exact PVM.encodeLE_mod 1 e
    all_goals try simp [Memory.readN, Num.encodeLE]
    all_goals try exact PVM.read_write_ne' _ _ _ _ hne (by omega) hb
    all_goals try rw [Nat.mod_eq_of_lt he]

/-- **36335 / 36394, the next item**: ω₅ = 144 · (k + 1) becomes 144 · k and ω₆ = a becomes a + 144; on to
    36346 if k ≠ 0, else to 36405. -/
theorem rl_next {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (i k a : Nat) (hi : i = 36335 ∨ i = 36394) (h5 : ω[5] = UInt64.ofNat (144 * (k + 1)))
    (h6 : ω[6] = UInt64.ofNat a) (hk : 144 * (k + 1) < 18446744073709551616) (ha : a + 144 < 18446744073709551616) :
    ∃ ω', FreeStepsH p R i ω μ x (if k = 0 then 36405 else 36346) ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (144 * k) ∧ ω'[6] = UInt64.ofNat (a + 144) ∧ ω'[0] = ω[0] := by
  have e5 : (144 * (k + 1) % 18446744073709551616 + 18446744073709551472) % 18446744073709551616 = 144 * k := by
    rw [Nat.mod_eq_of_lt hk]; omega
  have e6 : (a % 18446744073709551616 + 144) % 18446744073709551616 = a + 144 := by
    rw [Nat.mod_eq_of_lt (show a < 18446744073709551616 by omega), Nat.mod_eq_of_lt ha]
  rw [show ω = regsNF ω [] from rfl]
  by_cases hk0 : k = 0
  · subst hk0
    rw [if_pos rfl]
    rcases hi with rfl | rfl
    all_goals
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h5, h6, e5, e6, bs_36405]
      · refine ⟨by reg_val, ?_, ?_, by reg_val⟩
        all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5, h6, e5, e6]
  · have hk' : 144 * k % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [if_neg hk0]
    rcases hi with rfl | rfl
    all_goals
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h5, h6, e5, e6, hk', bs_36346]
      · refine ⟨by reg_val, ?_, ?_, by reg_val⟩
        all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5, h6, e5, e6]

/-- **36405 … 36426, after the loop**: the value's capacity v (S + 32) moved to S + 24, its length ℓ
    (S + 48) to S + 8, its ptr (S + 40) in ω₆, and the call of the key encoder (33843) with out S + 32,
    the key value kp (S + 16) and return address 1704. -/
theorem rl_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S v ptr len kp : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296)
    (hv : v < 2 ^ 64) (hptr : ptr < 2 ^ 64) (hlen : len < 2 ^ 64) (hkp : kp < 2 ^ 64)
    (mv : μ.readN (S + 32) 8 = Num.encodeLE 8 v)
    (mp : μ.readN (S + 40) 8 = Num.encodeLE 8 ptr) (ml : μ.readN (S + 48) 8 = Num.encodeLE 8 len)
    (mk : μ.readN (S + 16) 8 = Num.encodeLE 8 kp)
    (hr : ∀ a, S + 16 ≤ a → a < S + 56 → μ.readable a = true)
    (hw : ∀ a, S + 8 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36405 ω μ x 33843 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1704 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat ptr ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat kp ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 v ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 16 ≤ a) → (a < S + 24 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  have rk := Handlers.DesignateAlloc.rd8 hkp mk
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, rv, rp, rl, rk, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1' h2' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.ResStore
