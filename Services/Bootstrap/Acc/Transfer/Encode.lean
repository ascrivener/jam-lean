import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The encoding of a transfer's record (34071 … 34176), for "transfer{n}"

`on_transfer` lays out (amount: u64, source: u32, memo: [u8; 128]) at st = sp + 1568 (amount at
st, source at st + 8, the memo at st + 12) and calls this helper with out = sp + 744: after
`alloc(140, 1)` (returning to 34071) it builds `Vec { 140, ptr, 0 }` at s + 8 (s = sp − 64) and
extends it with ℰ₄(source), ℰ₈(amount) and the memo (`extend_from_slice`, 58508), then copies the
`Vec` to out. So the value is ℰ₄(source) ++ ℰ₈(amount) ++ memo (Spec `onTransfer`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- A u32 sign-extended to a word and cut back to 32 bits. -/
theorem enc_sxw (v : Nat) (hv : v < 4294967296) : sxw 4 v % 18446744073709551616 % 4294967296 = v := by
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  have := sxw_mod 4 v (Or.inr rfl) (by simpa using hv)
  simp only [Nat.reducePow] at this
  rw [this, Nat.mod_eq_of_lt hv]

/-- **34071 … 34178**, `alloc` returned null: the allocation-failure trap. -/
theorem enc_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) : FreeStepsH p R 34071 ω μ x 34178 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7]

/-- **34071 … 58508**, a block ptr ≠ 0: `Vec { 140, ptr, 0 }` at s + 8, the memo's address st + 12
    at s, the source (the u32 at st + 8) at s + 32, and `extend_from_slice` of those 4 octets (return
    address 1578). -/
theorem enc_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s st ptr src : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat st)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hst : 65536 ≤ st ∧ st + 140 < 4294967296)
    (hwf : ∀ a, s ≤ a → a < s + 64 → μ.writable a = true)
    (hrs : ∀ a, st + 8 ≤ a → a < st + 12 → μ.readable a = true)
    (dj : st + 12 ≤ s ∨ s + 64 ≤ st + 8) (m8 : rdN μ (st + 8) 4 = src) :
    ∃ ω' μ', FreeStepsH p R 34071 ω μ x 58508 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1578 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 8) ∧
      ω'[8] = UInt64.ofNat (s + 32) ∧ ω'[9] = UInt64.ofNat 4 ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat st ∧
      μ'.readN (s + 8) 8 = Num.encodeLE 8 140 ∧ μ'.readN (s + 16) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (s + 24) 8 = Num.encodeLE 8 0 ∧ rdN μ' s 8 = st + 12 ∧ rdN μ' (s + 32) 4 = src ∧
      (∀ a, a < 4294967296 → (a < s ∨ s + 36 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, hp0', hwf, hr, hrs, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val, (by reg_val <;> rfl),
      (by reg_val <;> exact h6), ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip
    have hv : Num.decodeLE (μ.readN (st + 8) 4) < 4294967296 := rdN_lt μ (st + 8) 4
    rw [enc_sxw _ hv, Nat.mod_eq_of_lt hv]; exact m8

/-- **34112 … 58508**: the amount (the word at st) at s + 32 and `extend_from_slice` of those 8
    octets (return address 1580). -/
theorem enc_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s st am : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat st)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hst : 65536 ≤ st ∧ st + 140 < 4294967296)
    (hwf : ∀ a, s ≤ a → a < s + 64 → μ.writable a = true)
    (hrs : ∀ a, st ≤ a → a < st + 8 → μ.readable a = true) (m0 : rdN μ st 8 = am) :
    ∃ ω' μ', FreeStepsH p R 34112 ω μ x 58508 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1580 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 8) ∧
      ω'[8] = UInt64.ofNat (s + 32) ∧ ω'[9] = UInt64.ofNat 8 ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (s + 32) 8 = am ∧
      (∀ a, a < 4294967296 → (a < s + 32 ∨ s + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, hwf, hr, hrs, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val, (by reg_val <;> rfl),
      (by reg_val <;> rfl), ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | (rw [← m0]; unfold rdN; rw [Nat.mod_eq_of_lt (show Num.decodeLE (μ.readN st 8) < 18446744073709551616 from rdN_lt64 μ st)]; exact Nat.mod_eq_of_lt (rdN_lt64 μ st)) | skip

/-- **34132 … 58508**: `extend_from_slice` of the memo's 128 octets (its address at s; return
    address 1582). -/
theorem enc_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s mp : Nat) (h1 : ω[1] = UInt64.ofNat s) (hs : 65536 ≤ s ∧ s + 64 < 4294967296)
    (hrf : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true) (m0 : rdN μ s 8 = mp) :
    ∃ ω', FreeStepsH p R 34132 ω μ x 58508 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 1582 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 8) ∧
      ω'[8] = UInt64.ofNat mp ∧ ω'[9] = UInt64.ofNat 128 ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, m0, ↓rdN_fold]
  case post => exact ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val,
    (by reg_val <;> rfl), (by reg_val <;> rfl)⟩

/-- **34147 … 34176**: the `Vec` at s + 8 copied to out (ω₅); ω₀, ω₅, ω₆ restored from s + 56, + 48,
    + 40 and the frame popped, at the return's `jumpInd`. -/
theorem enc_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s out cap ptr len r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat out)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (ho : 65536 ≤ out ∧ out + 24 < 4294967296)
    (dj : out + 24 ≤ s ∨ s + 64 ≤ out)
    (hrf : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (m8 : rdN μ (s + 8) 8 = cap) (m16 : rdN μ (s + 16) 8 = ptr) (m24 : rdN μ (s + 24) 8 = len)
    (m56 : rdN μ (s + 56) 8 = r0) (m48 : rdN μ (s + 48) 8 = r5) (m40 : rdN μ (s + 40) 8 = r6) :
    ∃ ω' μ', FreeStepsH p R 34147 ω μ x 34176 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      ω'[1] = UInt64.ofNat (s + 64) ∧
      rdN μ' out 8 = cap ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = len ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have l8 := m8 ▸ rdN_lt64 μ (s + 8)
  have l16 := m16 ▸ rdN_lt64 μ (s + 16)
  have l24 := m24 ▸ rdN_lt64 μ (s + 24)
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hrf, hwo, hro, m8, m16, m24, m56, m48, m40, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | exact Nat.mod_eq_of_lt (by omega) | skip

/-- The helper's return (34176) to 7888 (ω₀ = 272). -/
theorem enc_j {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 272) : FreeStepsH p R 34176 ω μ x 7888 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Acc
