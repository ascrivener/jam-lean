import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `get` of a copied 14-octet key (3820 … 3893), for "transfer-count"

`on_transfer` reads "transfer-count" (14 octets of read-only data at 65956) through a helper that
copies the key into a fresh `Vec<u8>` and then calls the SDK's `get` (47857):
- 7205 … 7233 (inline at the call site): the frame s = sp − 56 (ω₀, ω₅, ω₆ at s + 48, + 40, + 32),
  out at s, then `alloc(14, 1)` (40494) returning to 3820;
- 3820: a null block traps (3895, `gk_null`); else `Vec { 14, ptr, 0 }` at s + 8 and
  `extend_from_slice` (58508) of the key (`gk_vec`);
- 3846: `get(out, ptr, len)` (`gk_get`); 3865: the copy freed (`gk_free`, `gk_nofree`); 3881: the
  return (`gk_ret`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **3820 … 58508**, `alloc` returned a block ptr ≠ 0: the key's `Vec { 14, ptr, 0 }` at s + 8, and the
    call of `extend_from_slice` of the 14 octets at ω₆ (return address 104). -/
theorem gk_vec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s ptr : Nat) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat 14)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296)
    (hs : 65536 ≤ s ∧ s + 56 < 4294967296) (hwf : ∀ a, s ≤ a → a < s + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3820 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 104 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat (s + 8) ∧ ω'[8] = ω[6] ∧
      ω'[9] = UInt64.ofNat 14 ∧ ω'[5] = UInt64.ofNat 14 ∧ ω'[6] = ω[6] ∧
      μ'.readN (s + 8) 8 = Num.encodeLE 8 14 ∧ μ'.readN (s + 16) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (s + 24) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < s + 8 ∨ s + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, hp0', hwf, hr]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_val,
      (by reg_val <;> exact h5), (by reg_val <;> rfl), ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try (simp only [UInt64.toNat_ofNat_of_lt' (show ptr < 2 ^ 64 by omega)])
    all_goals try rfl
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **3820 … 3895**, `alloc` returned null: the allocation-failure trap. -/
theorem gk_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) :
    FreeStepsH p R 3820 ω μ x 3895 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7]

/-- **3846 … 47857**: the call of `get` with out = the word at s, the key's `Vec` (cap, ptr, len at
    s + 8 … + 24): ω₇ = out, ω₈ = ptr, ω₉ = len; ω₆ = cap and ω₅ = ptr kept for the free, return
    address 106. -/
theorem gk_get {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s out cap ptr len : Nat) (h1 : ω[1] = UInt64.ofNat s)
    (hs : 65536 ≤ s ∧ s + 56 < 4294967296) (hrf : ∀ a, s ≤ a → a < s + 56 → μ.readable a = true)
    (m0 : μ.readN s 8 = Num.encodeLE 8 out) (m8 : μ.readN (s + 8) 8 = Num.encodeLE 8 cap)
    (m16 : μ.readN (s + 16) 8 = Num.encodeLE 8 ptr) (m24 : μ.readN (s + 24) 8 = Num.encodeLE 8 len)
    (ho : out < 18446744073709551616) (hc : cap < 18446744073709551616) (hp : ptr < 18446744073709551616)
    (hl : len < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 3846 ω μ x 47857 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 106 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[7] = UInt64.ofNat out ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat cap ∧
      ω'[5] = UInt64.ofNat ptr := by
  have q0 : rdN μ s 8 = out := by unfold rdN; rw [m0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt ho
  have q8 : rdN μ (s + 8) 8 = cap := by unfold rdN; rw [m8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hc
  have q16 : rdN μ (s + 16) 8 = ptr := by unfold rdN; rw [m16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hp
  have q24 : rdN μ (s + 24) 8 = len := by unfold rdN; rw [m24, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, q0, q8, q16, q24, hrf, ↓rdN_fold]
  case post => exact ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val, by reg_val,
    by reg_val⟩

/-- **3865 … 40613**, the key's capacity cap ≠ 0: the call of `dealloc` on ptr (ω₈ = cap, ω₉ = 1),
    return address 108. -/
theorem gk_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (cap ptr : Nat) (h5 : ω[5] = UInt64.ofNat ptr) (h6 : ω[6] = UInt64.ofNat cap)
    (hc : cap ≠ 0) (hc64 : cap < 18446744073709551616) (hp64 : ptr < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 3865 ω μ x 40613 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 108 ∧ ω'[7] = UInt64.ofNat ptr ∧ ω'[1] = ω[1] := by
  have hc' : cap % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc64]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h6, hc']
  case post => exact ⟨by reg_val, (by reg_val; try rw [Nat.mod_eq_of_lt hp64]), (by reg_val <;> rfl)⟩

/-- **3865 … 3881**, the key's capacity 0: no `dealloc`. -/
theorem gk_nofree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h6 : ω[6] = UInt64.ofNat 0) : FreeStepsH p R 3865 ω μ x 3881 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h6]

/-- **3881 … 3893**: ω₀, ω₅, ω₆ restored from s + 48, + 40, + 32 and the frame popped, at the
    return's `jumpInd`. -/
theorem gk_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (s r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat s)
    (hs : 65536 ≤ s ∧ s + 56 < 4294967296) (hrf : ∀ a, s ≤ a → a < s + 56 → μ.readable a = true)
    (m48 : μ.readN (s + 48) 8 = Num.encodeLE 8 r0) (m40 : μ.readN (s + 40) 8 = Num.encodeLE 8 r5)
    (m32 : μ.readN (s + 32) 8 = Num.encodeLE 8 r6)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 3881 ω μ x 3893 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      ω'[1] = UInt64.ofNat (s + 56) ∧ ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6] → ω'[j] = ω[j] := by
  have q48 : rdN μ (s + 48) 8 = r0 := by unfold rdN; rw [m48, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr0
  have q40 : rdN μ (s + 40) 8 = r5 := by unfold rdN; rw [m40, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr5
  have q32 : rdN μ (s + 32) 8 = r6 := by unfold rdN; rw [m32, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hr6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, q48, q40, q32, hrf, ↓rdN_fold]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_frame⟩

end Services.Bootstrap.Acc
