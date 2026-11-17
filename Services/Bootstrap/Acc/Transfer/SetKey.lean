import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `set` of a copied 14-octet key (3896 … 4000), for "transfer-count"

`on_transfer` writes "transfer-count" (14 octets of read-only data at 65956) through a helper that
copies the key into a fresh `Vec<u8>` and then calls the SDK's `set` (48104):
- 7350 … 7382 (inline at the call site): the frame s = sp − 64 (ω₀ = 250, ω₅, ω₆ at s + 56, + 48,
  + 40), the value's address and length (4) at s and s + 8, then `alloc(14, 1)` (40494) returning to
  3896;
- 3896: a null block traps (4002, `sk_null`); else `Vec { 14, ptr, 0 }` at s + 16 and
  `extend_from_slice` (58508) of the key (`sk_vec`);
- 3922: `set(out = s + 16, key, value)` (`sk_set`); 3947: the copy freed (`sk_free`); 3972: the
  result word back (`sk_back`); 3976: the return (`sk_ret`), ω₇ = 2⁶⁴ − 1 for `Ok`, the error code
  for `Err`.
-/
namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **3896 … 4002**, `alloc` returned null: the allocation-failure trap. -/
theorem sk_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) : FreeStepsH p R 3896 ω μ x 4002 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7]

/-- **3896 … 58508**, a block ptr ≠ 0: the key's `Vec { 14, ptr, 0 }` at s + 16, and the call of
    `extend_from_slice` of the 14 octets at ω₅ (return address 112). -/
theorem sk_vec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s ptr : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat 14)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hwf : ∀ a, s ≤ a → a < s + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3896 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 112 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 16) ∧ ω'[8] = ω[5] ∧
      ω'[9] = UInt64.ofNat 14 ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat 14 ∧
      μ'.readN (s + 16) 8 = Num.encodeLE 8 14 ∧ μ'.readN (s + 24) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (s + 32) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < s + 16 ∨ s + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, hp0', hwf, hr]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_val,
      (by reg_val <;> simp [UInt64.ofNat_toNat]), (by reg_val <;> exact h6), ?_, ?_, ?_, fun a ha h1 => ?_,
      fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try (simp only [UInt64.toNat_ofNat_of_lt' (show ptr < 2 ^ 64 by omega)])
    all_goals try rfl
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **3922 … 48104**: the call of `set` with out = s + 16, the key's `Vec` (cap, ptr, len at s + 16 …
    + 32: ω₇ = s + 16, ω₈ = ptr, ω₉ = len), the value at ω₁₀ = the word at s (ω₁₁ = the word at s + 8);
    ω₅ = cap and ω₆ = ptr kept for the free, return address 114. -/
theorem sk_set {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s cap ptr len vO vZ : Nat) (h1 : ω[1] = UInt64.ofNat s)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hrf : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true)
    (m0 : rdN μ s 8 = vO) (m8 : rdN μ (s + 8) 8 = vZ) (m16 : rdN μ (s + 16) 8 = cap)
    (m24 : rdN μ (s + 24) 8 = ptr) (m32 : rdN μ (s + 32) 8 = len) :
    ∃ ω', FreeStepsH p R 3922 ω μ x 48104 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 114 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 16) ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat len ∧ ω'[10] = UInt64.ofNat vO ∧
      ω'[11] = UInt64.ofNat vZ ∧ ω'[5] = UInt64.ofNat cap ∧ ω'[6] = UInt64.ofNat ptr := by
  have l0 := m0 ▸ rdN_lt64 μ s
  have l8 := m8 ▸ rdN_lt64 μ (s + 8)
  have l16 := m16 ▸ rdN_lt64 μ (s + 16)
  have l24 := m24 ▸ rdN_lt64 μ (s + 24)
  have l32 := m32 ▸ rdN_lt64 μ (s + 32)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, m16, m24, m32, hrf, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (reg_val; try simp only [Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l8, Nat.mod_eq_of_lt l16,
        Nat.mod_eq_of_lt l24, Nat.mod_eq_of_lt l32])

/-- **3972 … 3976**: the result word back in ω₇ (from s + 8). -/
theorem sk_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s : Nat) (h1 : ω[1] = UInt64.ofNat s) (hs : 65536 ≤ s ∧ s + 64 < 4294967296)
    (hrf : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3972 ω μ x 3976 ω' μ x 2 ∧ ω'[7] = UInt64.ofNat (rdN μ (s + 8) 8) ∧
      ω'[1] = UInt64.ofNat s ∧ ω'[5] = ω[5] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, ↓rdN_fold]
  case post => exact ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val <;> rfl)⟩

/-- **3947 … 40613**, the key's capacity cap ≠ 0: the result word w at s + 16 saved at s + 8, ω₅ = the
    octet at s + 24, and the call of `dealloc` on ptr (ω₈ = cap, ω₉ = 1), return address 116. -/
theorem sk_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s cap ptr : Nat) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat cap)
    (h6 : ω[6] = UInt64.ofNat ptr) (hc : cap ≠ 0) (hc64 : cap < 18446744073709551616)
    (hp64 : ptr < 18446744073709551616)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hwf : ∀ a, s ≤ a → a < s + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3947 ω μ x 40613 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 116 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[8] = UInt64.ofNat cap ∧ ω'[9] = UInt64.ofNat 1 ∧
      ω'[5] = UInt64.ofNat (rdN μ (s + 24) 1) ∧ rdN μ' (s + 8) 8 = rdN μ (s + 16) 8 ∧
      (∀ a, a < 4294967296 → (a < s + 8 ∨ s + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc64]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hc', hwf, hr, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val; try rw [Nat.mod_eq_of_lt hp64]),
      (by reg_val; try rw [Nat.mod_eq_of_lt hc64]), by reg_val, by reg_val, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_same, Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | (rw [Nat.mod_eq_of_lt (show Num.decodeLE (μ.readN (s + 16) 8) < 18446744073709551616 from rdN_lt64 μ (s + 16))]; exact Nat.mod_eq_of_lt (rdN_lt64 μ (s + 16))) | skip

/-- **3976 … 4000**: the helper's result. `Ok` (the word w at out is not 2⁶⁴ − 1) gives 2⁶⁴ − 1 (the
    octet 255), `Err` its code b. ω₀, ω₅, ω₆ are restored from s + 56, + 48, + 40 and the frame popped,
    at the return's `jumpInd`. -/
theorem sk_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s w b r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat s) (h7 : ω[7] = UInt64.ofNat w)
    (h5 : ω[5] = UInt64.ofNat b) (hw : w < 18446744073709551616) (hb : b < 18446744073709551616)
    (hs : 65536 ≤ s ∧ s + 64 < 4294967296) (hrf : ∀ a, s ≤ a → a < s + 64 → μ.readable a = true)
    (m56 : rdN μ (s + 56) 8 = r0) (m48 : rdN μ (s + 48) 8 = r5) (m40 : rdN μ (s + 40) 8 = r6) :
    ∃ ω', FreeStepsH p R 3976 ω μ x 4000 ω' μ x 9 ∧
      ω'[7] = UInt64.ofNat (if w = 18446744073709551615 then b else 18446744073709551615) ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      ω'[1] = UInt64.ofNat (s + 64) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, h5, m56, m48, m40, hrf, ↓rdN_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val⟩
    reg_val
    by_cases hw' : w = 18446744073709551615
    · subst hw'; simp [Nat.mod_eq_of_lt hb]
    · have hne : (w + 1) % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [hne, hw']

end Services.Bootstrap.Acc
