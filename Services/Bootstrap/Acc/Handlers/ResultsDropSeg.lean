import Services.Bootstrap.Acc.Handlers.ResStoreSeg

/-!
# The results' drop (28864): the straight-line segments

`drop_in_place::<[Result]>` for the results `Vec` at v (ω₇; ptr at v + 8, len at v + 16) in the frame
F = S − 56 (ω₀, ω₅, ω₆ saved at F + 48, F + 40, F + 32; len at F, ptr at F + 8, the item's address at
F + 16, the inner array's end at F + 24). Per item at a = ptr + 144·k (k in ω₆, len in ω₅), by its tag
octet t at a:
- t = 255 or t < 5: nothing (`dr_err`, `dr_small`);
- t = 5 (`data`): `dr_isdata`, then `dr_data0` (cap at a + 8 is 0) or `dr_data1` (dealloc of the buffer
  at a + 16, return address 1350 → 28922);
- t ≥ 6 (`dataVec`): `dr_isvec`, then `dv_pre0` (len at a + 24 is 0) or `dv_pre1` (the inner loop over
  the 24-octet `Vec`s from ptr′ (at a + 16): `dv_in0` / `dv_in1` (dealloc, return address 1352 → 29032),
  `dv_back`, `dv_step0` / `dv_step1`), then `dv_out0` (outer cap 0) or `dv_out1` (dealloc of the outer
  buffer, 24·cap octets, return address 1350 → 28922);
- `dr_next0` / `dr_next1` (28922): k + 1, on while k + 1 ≠ len;
- `dr_pre0` / `dr_pre1` (28864: len = 0 or not) and `dr_end` (29072: the return).
-/

namespace Services.Bootstrap.Acc.Handlers.ResultsDrop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem rdN_lt8 (μ : Memory) (b : Nat) : rdN μ b 8 < 2 ^ 64 := by
  have := Services.Bootstrap.Acc.Handlers.KeyEnc.decodeLE_readN_lt μ b 8
  unfold rdN; simpa using this

/-- **28864 … 28879, len = 0**: the frame F = S − 56, ω₀, ω₅, ω₆ saved; on to the return at 29072. -/
theorem dr_pre0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S v : Nat) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat v) (hS : 65536 + 56 ≤ S ∧ S < 4294967296)
    (hv : v + 24 < 4294967296) (hd : v + 24 ≤ S - 56 ∨ S ≤ v) (ml : rdN μ (v + 16) 8 = 0)
    (hr : ∀ a, v + 16 ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, S - 56 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 28864 ω μ x 29072 ω' μ' x 6 ∧ ω'[1] = UInt64.ofNat (S - 56) ∧
      μ'.readN (S - 56 + 48) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (S - 56 + 40) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (S - 56 + 32) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < S - 56 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hv, ml, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)

/-- **28864 … 28894, len ≠ 0**: the frame F = S − 56, ω₀, ω₅, ω₆ saved, len at F, ptr at F + 8; on to
    the loop head 28929 with ω₅ = len, ω₆ = 0. -/
theorem dr_pre1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S v ptr len : Nat) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat v)
    (hS : 65536 + 56 ≤ S ∧ S < 4294967296) (hv : v + 24 < 4294967296) (hd : v + 24 ≤ S - 56 ∨ S ≤ v)
    (mp : rdN μ (v + 8) 8 = ptr) (ml : rdN μ (v + 16) 8 = len) (hl0 : len ≠ 0)
    (hr : ∀ a, v + 8 ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, S - 56 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 28864 ω μ x 28929 ω' μ' x 12 ∧ ω'[1] = UInt64.ofNat (S - 56) ∧
      ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat 0 ∧
      μ'.readN (S - 56 + 48) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (S - 56 + 40) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (S - 56 + 32) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (S - 56) 8 = Num.encodeLE 8 len ∧
      μ'.readN (S - 56 + 8) 8 = Num.encodeLE 8 ptr ∧
      (∀ a, a < 4294967296 → (a < S - 56 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hl : len < 2 ^ 64 := ml ▸ rdN_lt8 μ (v + 16)
  have hp : ptr < 2 ^ 64 := mp ▸ rdN_lt8 μ (v + 8)
  have hl0' : len % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hl]; exact hl0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hv, mp, ml, hl0', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)
    all_goals try simp [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hp]

/-- The common hypotheses of the loop head: ω₁ = F, ω₆ = k, ptr at F + 8, the item at
    a = ptr + 144·k with tag octet t. -/
structure HeadHyp (ω : Regs) (μ : Memory) (F ptr k t : Nat) : Prop where
  h1 : ω[1] = UInt64.ofNat F
  h6 : ω[6] = UInt64.ofNat k
  hF : 65536 ≤ F ∧ F + 56 < 4294967296
  ha : ptr + 144 * k + 1 < 4294967296
  hd : ptr + 144 * k + 1 ≤ F ∨ F + 24 ≤ ptr + 144 * k
  mp : rdN μ (F + 8) 8 = ptr
  mt : rdN μ (ptr + 144 * k) 1 = t
  hr : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true
  hra : μ.readable (ptr + 144 * k) = true
  hw : ∀ a, F + 16 ≤ a → a < F + 24 → μ.writable a = true

/-- What the loop head leaves: a = ptr + 144·k at F + 16, ω₁, ω₅, ω₆ kept, memory kept off F + 16. -/
def HeadPost (ω : Regs) (μ : Memory) (F ptr k : Nat) (ω' : Regs) (μ' : Memory) : Prop :=
  ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 16) 8 = Num.encodeLE 8 (ptr + 144 * k) ∧
    (∀ a, a < 4294967296 → (a < F + 16 ∨ F + 24 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **28929 … 28954, t = 255** (`Err`): nothing to drop; on to 28922. -/
theorem dr_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F ptr k : Nat) (H : HeadHyp ω μ F ptr k 255) :
    ∃ ω' μ', FreeStepsH p R 28929 ω μ x 28922 ω' μ' x 10 ∧ HeadPost ω μ F ptr k ω' μ' := by
  obtain ⟨h1, h6, hF, ha, hd, mp, mt, hr, hra, hw⟩ := H
  have ea : k * 16 + k * 128 + ptr = ptr + 144 * k := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF, ha, ea, mp, mt, hr, hra, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **28929 … 28960, t < 5** (`Ok` of a fixed-size payload): nothing to drop; on to 28922. -/
theorem dr_small {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F ptr k t : Nat) (H : HeadHyp ω μ F ptr k t) (ht : t < 5) :
    ∃ ω' μ', FreeStepsH p R 28929 ω μ x 28922 ω' μ' x 12 ∧ HeadPost ω μ F ptr k ω' μ' := by
  obtain ⟨h1, h6, hF, ha, hd, mp, mt, hr, hra, hw⟩ := H
  have ea : k * 16 + k * 128 + ptr = ptr + 144 * k := by omega
  have ht' : t ≠ 255 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF, ha, ea, mp, mt, ht, ht', hr, hra, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **28929 … 28963, t = 5** (`data`): on to 28896. -/
theorem dr_isdata {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F ptr k : Nat) (H : HeadHyp ω μ F ptr k 5) :
    ∃ ω' μ', FreeStepsH p R 28929 ω μ x 28896 ω' μ' x 13 ∧ HeadPost ω μ F ptr k ω' μ' := by
  obtain ⟨h1, h6, hF, ha, hd, mp, mt, hr, hra, hw⟩ := H
  have ea : k * 16 + k * 128 + ptr = ptr + 144 * k := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF, ha, ea, mp, mt, hr, hra, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **28929 … 28963, 6 ≤ t < 255** (`dataVec`): on to 28967. -/
theorem dr_isvec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F ptr k t : Nat) (H : HeadHyp ω μ F ptr k t) (ht : 6 ≤ t ∧ t < 255) :
    ∃ ω' μ', FreeStepsH p R 28929 ω μ x 28967 ω' μ' x 13 ∧ HeadPost ω μ F ptr k ω' μ' := by
  obtain ⟨h1, h6, hF, ha, hd, mp, mt, hr, hra, hw⟩ := H
  have ea : k * 16 + k * 128 + ptr = ptr + 144 * k := by omega
  have ht1 : t ≠ 255 := by omega
  have ht2 : ¬ t < 5 := by omega
  have ht3 : t ≠ 5 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hF, ha, ea, mp, mt, ht1, ht2, ht3, hr, hra, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **28896 … 28903, a `data` item with cap 0** (at a + 8; a at F + 16): on to 28922. -/
theorem dr_data0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 16 < 4294967296)
    (mA : rdN μ (F + 16) 8 = a) (mc : rdN μ (a + 8) 8 = 0)
    (hr : ∀ b, F + 16 ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 8 ≤ b → b < a + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28896 ω μ x 28922 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, ha, mA, mc, hr, hra, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **28896 … 28916, a `data` item with cap ≠ 0**: the call of `dealloc` (40613) with ω₇ = the buffer
    (at a + 16), ω₉ = 1 and return address 1350 (→ 28922). -/
theorem dr_data1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a c q : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 24 < 4294967296)
    (mA : rdN μ (F + 16) 8 = a) (mc : rdN μ (a + 8) 8 = c) (hc : c ≠ 0) (mq : rdN μ (a + 16) 8 = q)
    (hr : ∀ b, F + 16 ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 8 ≤ b → b < a + 24 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28896 ω μ x 40613 ω' μ x 9 ∧ ω'[0] = UInt64.ofNat 1350 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (a + 8)
  have hq : q < 2 ^ 64 := mq ▸ rdN_lt8 μ (a + 16)
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, ha, mA, mc, hc0, mq, hr, hra, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hq]

/-- **28922 … 28925, k + 1 = len** (ω₆ = k, ω₅ = len): on to the return at 29072. -/
theorem dr_next0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (k len : Nat) (h5 : ω[5] = UInt64.ofNat len) (h6 : ω[6] = UInt64.ofNat k) (hl : len < 2 ^ 64)
    (hk : k + 1 = len) :
    ∃ ω', FreeStepsH p R 28922 ω μ x 29072 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat (k + 1) := by
  rw [show ω = regsNF ω [] from rfl]
  have e : (k % 18446744073709551616 + 1) % 18446744073709551616 = len % 18446744073709551616 := by omega
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, e]
  · refine ⟨by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, h6]
    subst hk
    rw [UInt64.ofNat_add]; rfl

/-- **28922 … 28925, k + 1 ≠ len**: on to the loop head 28929 with ω₆ = k + 1. -/
theorem dr_next1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (k len : Nat) (h5 : ω[5] = UInt64.ofNat len) (h6 : ω[6] = UInt64.ofNat k) (hl : len < 2 ^ 64)
    (hk : k + 1 < len) :
    ∃ ω', FreeStepsH p R 28922 ω μ x 28929 ω' μ x 2 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat (k + 1) := by
  rw [show ω = regsNF ω [] from rfl]
  have e : (k % 18446744073709551616 + 1) % 18446744073709551616 ≠ len % 18446744073709551616 := by omega
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6, e]
  · refine ⟨by reg_val, by reg_val, ?_⟩
    have e6 : (k % 18446744073709551616 + 1) % 18446744073709551616 = k + 1 := by omega
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h6, e6]
    all_goals try (congr 1; omega)

/-- **29072 … 29085, the return**: ω₀, ω₅, ω₆ restored from F + 48, F + 40, F + 32, ω₁ := F + 56, and the
    return through ω₀ = ret to t. -/
theorem dr_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F ret v5 v6 t : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (m0 : rdN μ (F + 48) 8 = ret) (m5 : rdN μ (F + 40) 8 = v5) (m6 : rdN μ (F + 32) 8 = v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, F + 32 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29072 ω μ x t ω' μ x 6 ∧ ω'[1] = UInt64.ofNat (F + 56) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  have h5 : v5 < 2 ^ 64 := m5 ▸ rdN_lt8 μ (F + 40)
  have h6 : v6 < 2 ^ 64 := m6 ▸ rdN_lt8 μ (F + 32)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, m0, m5, m6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6]
    all_goals try (congr 1; omega)

/-- **28967 … 28974, a `dataVec` item with len 0** (at a + 24): on to 29034. -/
theorem dv_pre0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 32 < 4294967296)
    (mA : rdN μ (F + 16) 8 = a) (ml : rdN μ (a + 24) 8 = 0)
    (hr : ∀ b, F + 16 ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 24 ≤ b → b < a + 32 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28967 ω μ x 29034 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, ha, mA, ml, hr, hra, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val⟩

/-- **28967 … 29002, a `dataVec` item with len ≠ 0**: ω₅ := q + 8 (q the inner array at a + 16), its end
    q + 8 + 24·len at F + 24; on to the inner loop at 29014. -/
theorem dv_pre1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a q len : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 32 < 4294967296)
    (hq : q + 8 + 24 * len < 2 ^ 64) (hd : a + 32 ≤ F + 24 ∨ F + 32 ≤ a)
    (mA : rdN μ (F + 16) 8 = a) (mq : rdN μ (a + 16) 8 = q) (ml : rdN μ (a + 24) 8 = len) (hl0 : len ≠ 0)
    (hr : ∀ b, F + 16 ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 16 ≤ b → b < a + 32 → μ.readable b = true)
    (hw : ∀ b, F + 24 ≤ b → b < F + 32 → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 28967 ω μ x 29014 ω' μ' x 14 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (q + 8) ∧
      ω'[6] = ω[6] ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 (q + 8 + 24 * len) ∧
      (∀ b, b < 4294967296 → (b < F + 24 ∨ F + 32 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hl : len < 2 ^ 64 := ml ▸ rdN_lt8 μ (a + 24)
  have hl0' : len % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hl]; exact hl0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hF, ha, mA, mq, ml, hl0', hr, hra, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, ?_, fun b hb h1' => ?_, fun b => ?_, fun b => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    all_goals try (congr 1; omega)

/-- The wrapped read at q − 8 (the offset −8 as a 64-bit immediate) and its readability, for an opaque q
    (kept opaque so that no literal is folded into q). -/
theorem back8 (μ : Memory) (q : Nat) (hq : 8 ≤ q ∧ q + 8 < 4294967296) :
    rdN μ (q + 18446744073709551608) 8 = rdN μ (q - 8) 8 ∧
    ∀ j, (q + 18446744073709551608 + j) % 4294967296 = q - 8 + (j % 4294967296) ∨ 4294967296 ≤ q - 8 + j := by
  refine ⟨?_, fun j => ?_⟩
  · have h : ∀ k, μ.read (q + 18446744073709551608 + k) = μ.read (q - 8 + k) := fun k => by
      unfold Memory.read
      rw [show (q + 18446744073709551608 + k) % two32 = (q - 8 + k) % two32 by unfold two32; omega]
    unfold rdN Memory.readN
    simp only [h]
  · omega

/-- **29014 … 29018, an inner `Vec` with cap 0** (at ω₅ − 8, ω₅ = q): on to 29004. -/
theorem dv_in0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (q : Nat) (h5 : ω[5] = UInt64.ofNat q) (hq : 8 ≤ q ∧ q + 8 < 4294967296) (mc : rdN μ (q - 8) 8 = 0)
    (hra : ∀ b, q - 8 ≤ b → b < q → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29014 ω μ x 29004 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hq' : q % 18446744073709551616 = q := Nat.mod_eq_of_lt (by omega)
  obtain ⟨e8, -⟩ := back8 μ q hq
  have mc' : rdN μ (q + 18446744073709551608) 8 = 0 := by rw [e8]; exact mc
  have rr : ∀ j, j < 8 → μ.readable ((q + 18446744073709551608 + j) % 4294967296) = true := fun j hj => by
    rw [show (q + 18446744073709551608 + j) % 4294967296 = q - 8 + j by omega]; exact hra _ (by omega) (by omega)
  have r0 := rr 0 (by omega)
  have r1 := rr 1 (by omega)
  have r2 := rr 2 (by omega)
  have r3 := rr 3 (by omega)
  have r4 := rr 4 (by omega)
  have r5 := rr 5 (by omega)
  have r6 := rr 6 (by omega)
  have r7 := rr 7 (by omega)
  simp only [Nat.add_zero] at r0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, hq', mc', r0, r1, r2, r3, r4, r5, r6, r7, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val, by reg_val⟩

/-- **29014 … 29026, an inner `Vec` with cap c ≠ 0** (at q − 8, ω₅ = q): the call of `dealloc` with
    ω₇ = its buffer w (at q), ω₉ = 1 and return address 1352 (→ 29032). -/
theorem dv_in1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (q c w : Nat) (h5 : ω[5] = UInt64.ofNat q) (hq : 8 ≤ q ∧ q + 8 < 4294967296) (mc : rdN μ (q - 8) 8 = c)
    (hc : c ≠ 0) (mw : rdN μ q 8 = w) (hra : ∀ b, q - 8 ≤ b → b < q + 8 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29014 ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat 1352 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat w := by
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (q - 8)
  have hw : w < 2 ^ 64 := mw ▸ rdN_lt8 μ q
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  have hq' : q % 18446744073709551616 = q := Nat.mod_eq_of_lt (by omega)
  obtain ⟨e8, -⟩ := back8 μ q hq
  have mc' : rdN μ (q + 18446744073709551608) 8 = c := by rw [e8]; exact mc
  have rr : ∀ j, j < 8 → μ.readable ((q + 18446744073709551608 + j) % 4294967296) = true := fun j hj => by
    rw [show (q + 18446744073709551608 + j) % 4294967296 = q - 8 + j by omega]; exact hra _ (by omega) (by omega)
  have r0 := rr 0 (by omega)
  have r1 := rr 1 (by omega)
  have r2 := rr 2 (by omega)
  have r3 := rr 3 (by omega)
  have r4 := rr 4 (by omega)
  have r5 := rr 5 (by omega)
  have r6 := rr 6 (by omega)
  have r7 := rr 7 (by omega)
  simp only [Nat.add_zero] at r0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, hq', mc', r0, r1, r2, r3, r4, r5, r6, r7, hc0, mw, hra, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hw]

/-- **29032**: on to 29004. -/
theorem dv_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory) :
    FreeStepsH p R 29032 ω μ x 29004 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go []

/-- **29004 … 29011, the inner loop's end** (ω₅ + 24 = the end at F + 24): on to 29034. -/
theorem dv_step0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F r e : Nat) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r) (hF : F + 56 < 4294967296)
    (hr : r + 24 < 2 ^ 64) (me : rdN μ (F + 24) 8 = e) (he : r + 24 = e)
    (hre : ∀ b, F + 24 ≤ b → b < F + 32 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29004 ω μ x 29034 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  have e' : (r % 18446744073709551616 + 24) % 18446744073709551616 = e := by omega
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hF, me, e', hre, ↓rdN_fold]
  · exact ⟨by reg_val, by reg_val⟩

/-- **29004 … 29011, on in the inner loop** (ω₅ + 24 ≠ the end): ω₅ += 24; on to 29014. -/
theorem dv_step1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F r e : Nat) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r) (hF : F + 56 < 4294967296)
    (hr : r + 24 < 2 ^ 64) (me : rdN μ (F + 24) 8 = e) (he : r + 24 ≠ e)
    (hre : ∀ b, F + 24 ≤ b → b < F + 32 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29004 ω μ x 29014 ω' μ x 4 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (r + 24) ∧
      ω'[6] = ω[6] := by
  have hle : e < 2 ^ 64 := me ▸ rdN_lt8 μ (F + 24)
  rw [show ω = regsNF ω [] from rfl]
  have e' : (r % 18446744073709551616 + 24) % 18446744073709551616 ≠ e := by omega
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hF, me, e', hre, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val⟩
    have e5 : (r % 18446744073709551616 + 24) % 18446744073709551616 = r + 24 := by omega
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5, e5]
    all_goals try (congr 1; omega)

/-- **29034 … 29043, a `dataVec` item with outer cap 0** (at a + 8): ω₅ := len (from F); on to 28922. -/
theorem dv_out0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a len : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 16 < 4294967296)
    (mA : rdN μ (F + 16) 8 = a) (mc : rdN μ (a + 8) 8 = 0) (ml : rdN μ F 8 = len)
    (hr : ∀ b, F ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 8 ≤ b → b < a + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29034 ω μ x 28922 ω' μ x 5 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[6] = ω[6] := by
  have hl : len < 2 ^ 64 := ml ▸ rdN_lt8 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, ha, mA, mc, ml, hr, hra, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hl]

/-- **29034 … 29069, a `dataVec` item with outer cap c ≠ 0**: ω₅ := len (from F), and the call of
    `dealloc` with ω₇ = the outer buffer q (at a + 16), ω₈ = 24·c, ω₉ = 8 and return address 1350
    (→ 28922). -/
theorem dv_out1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (F a len c q : Nat) (h1 : ω[1] = UInt64.ofNat F) (hF : F + 56 < 4294967296) (ha : a + 24 < 4294967296)
    (mA : rdN μ (F + 16) 8 = a) (mc : rdN μ (a + 8) 8 = c) (hc : c ≠ 0) (mq : rdN μ (a + 16) 8 = q)
    (ml : rdN μ F 8 = len) (hr : ∀ b, F ≤ b → b < F + 24 → μ.readable b = true)
    (hra : ∀ b, a + 8 ≤ b → b < a + 24 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 29034 ω μ x 40613 ω' μ x 14 ∧ ω'[0] = UInt64.ofNat 1350 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat len ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  have hl : len < 2 ^ 64 := ml ▸ rdN_lt8 μ F
  have hc' : c < 2 ^ 64 := mc ▸ rdN_lt8 μ (a + 8)
  have hq : q < 2 ^ 64 := mq ▸ rdN_lt8 μ (a + 16)
  have hc0 : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc']; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, ha, mA, mc, hc0, mq, ml, hr, hra, ↓rdN_fold]
  · refine ⟨by reg_val, by reg_val, ?_, by reg_val, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hq]

end Services.Bootstrap.Acc.Handlers.ResultsDrop
