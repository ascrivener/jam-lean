import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.AllocWrap
import PVM.Logic.Go

/-!
# Accumulate's `finish_grow` (40852 / 41016): the allocator's lock around `alloc_impl`

`RawVec`'s growth in accumulate's `Vec` decoders calls 40852 (`finish_grow`), which inlines the
allocator's lock instead of calling the `alloc` / `realloc` wrappers (40494, 40701) refine's
decoders use. With no current block it continues at 41016: the layout's bounds, the lock (the word
at 206848), `alloc_impl` (41177) for ⌈size/32⌉ units of alignment ⌈align/32⌉ with the zero flag
clear, the unlock, and the `Result` written at `out`: `Ok(ptr, size)` (tag 0) or, for a null
block, `Err(align, size)` (tag 1).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **40852 … 41016**, no current block: `finish_grow(out = ω₇, cap = ω₈ = 0, ptr = ω₉,
    new_cap = ω₁₀, align = ω₁₁, elem = ω₁₂)` with size = new_cap · elem > 0 within 2⁶³ − align and
    no overflow. The 40-octet frame (ω₀, ω₅, ω₆ saved at sp − 8, − 16, − 24), align and `out` stored
    at sp − 40 and sp − 32, ω₆ = size, and the call of the alloc path (return address 1994). -/
theorem fg_entry_new {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out ncap al el : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat ncap) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat el)
    (hsz : 0 < ncap * el) (hov : ncap * el + al ≤ 9223372036854775808) (hal : al < 9223372036854775808)
    (hout : out < 18446744073709551616)
    (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 40852 ω μ x 41016 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[6] = UInt64.ofNat (ncap * el) ∧ ω'[0] = UInt64.ofNat 1994 ∧
      rdN μ' (sp - 40) 8 = al ∧ rdN μ' (sp - 32) 8 = out ∧
      rdN μ' (sp - 24) 8 = ω[6].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 8) 8 = ω[0].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 40 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hn64 : ncap * el < 18446744073709551616 := by omega
  have hel : el < 18446744073709551616 := by
    rcases Nat.eq_zero_or_pos ncap with h | h
    · simp [h] at hsz
    · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left el h) hn64
  have hnc : ncap < 18446744073709551616 := by
    rcases Nat.eq_zero_or_pos el with h | h
    · simp [h] at hsz
    · exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right ncap h) hn64
  have hmu : el % 18446744073709551616 * (ncap % 18446744073709551616) / 18446744073709551616 %
      18446744073709551616 = 0 := by
    rw [Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hnc, Nat.mul_comm, Nat.div_eq_of_lt hn64]
  have hml : el % 18446744073709551616 * (ncap % 18446744073709551616) % 18446744073709551616 = ncap * el := by
    rw [Nat.mod_eq_of_lt hel, Nat.mod_eq_of_lt hnc, Nat.mul_comm, Nat.mod_eq_of_lt hn64]
  have hmu2 : el * ncap / 18446744073709551616 % 18446744073709551616 = 0 := by
    rw [Nat.mul_comm, Nat.div_eq_of_lt hn64]
  have hml2 : el * ncap % 18446744073709551616 = ncap * el := by rw [Nat.mul_comm, Nat.mod_eq_of_lt hn64]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, h10, h11, h12, hwf, hr, hmu, hml, hmu2, hml2, Nat.mod_eq_of_lt hal, Nat.mod_eq_of_lt hout,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    · reg_val
    all_goals try simp only [show sp - 40 + 32 = sp - 8 from by omega, show sp - 40 + 24 = sp - 16 from by omega,
      show sp - 40 + 16 = sp - 24 from by omega, show sp - 40 + 8 = sp - 32 from by omega,
      show sp - 40 + 0 = sp - 40 from by omega]
    all_goals first
      | (rd_simp []; done)
      | rd_simp []
    all_goals first
      | rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-- **41016 … 41177**: the layout (align at sp, `out` at sp + 8, size in ω₆) within 2³⁷ − 32, the
    allocator's lock taken, and the call of `alloc_impl`: ω₇ = 196792, ω₈ = ⌈align/32⌉,
    ω₉ = ⌈size/32⌉, ω₁₀ = 0, return address 1996. -/
theorem fg_alloc_lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp al size out : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat size)
    (m0 : rdN μ sp 8 = al) (m8 : rdN μ (sp + 8) 8 = out)
    (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736) (hsp : 65536 ≤ sp ∧ sp + 16 < 4294967296)
    (hout : out < 18446744073709551616)
    (hrs : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 41016 ω μ x 41177 ω' μ' x 30 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat ((al + 31) / 32) ∧
      ω'[9] = UInt64.ofNat ((size + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1996 ∧
      ω'[1] = ω[1] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, m0, m8, hrs, hand, show 137438953440 ≥ al by omega,
    show 137438953440 ≥ size by omega, show ¬ 137438953440 < al by omega, show ¬ 137438953440 < size by omega,
    hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, ?_, by reg_val, by reg_val, ?_, by reg_val, by reg_val,
      fun a ha h1 h2 => ?_, fun a => ?_⟩
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      apply UInt64.toNat.inj
      simp only [UInt64.toNat_ofNat']
      simpa using hand
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rd_simp []
    · rd_simp [hwr]

/-- **41109 … 41175**, a block: `alloc_impl` returned `ptr` ≠ 0; the lock byte cleared and
    `Ok(ptr, size)` (tag 0) written at `out` (from sp + 8); ω₀, ω₅, ω₆ restored from the frame
    (sp + 32, + 24, + 16) and the 40-octet frame popped, at the return's `jumpInd`. -/
theorem fg_alloc_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp al size out ptr r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h6 : ω[6] = UInt64.ofNat size) (h7 : ω[7] = UInt64.ofNat ptr)
    (m0 : rdN μ sp 8 = al) (m8 : rdN μ (sp + 8) 8 = out) (m16 : rdN μ (sp + 16) 8 = r6)
    (m24 : rdN μ (sp + 24) 8 = r5) (m32 : rdN μ (sp + 32) 8 = r0)
    (hal : al < 18446744073709551616) (hs : size < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (hsp : 206852 ≤ sp ∧ sp + 40 < 4294967296) (hout : 206852 ≤ out ∧ out + 24 < 4294967296)
    (dso : out + 24 ≤ sp ∨ sp + 40 ≤ out)
    (hrs : ∀ a, sp ≤ a → a < sp + 40 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) (hwl : μ.writable 206848 = true)
    (hp0 : ptr ≠ 0) :
    ∃ ω' μ', FreeStepsH p R 41109 ω μ x 41175 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 40) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      rdN μ' out 8 = 0 ∧ rdN μ' (out + 8) 8 = ptr ∧
      rdN μ' (out + 16) 8 = size ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hptr]; exact hp0
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, m0, m8, m16, m24, m32, hrs, hro, hwo, hwl, hrl, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold, hp0']
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals try simp only [show 16 + out = out + 16 from Nat.add_comm _ _]
    all_goals first
      | (rd_simp []; done)
      | (rd_simp [hwo]; done)
      | rd_simp []
    all_goals first
      | rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | (rw [PVM.Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by unfold PVM.two32; omega),
          Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

/-- **41109 … 41175**, null: `alloc_impl` returned 0; the lock byte cleared and `Err(align, size)`
    (tag 1) written at `out`; ω₀, ω₅, ω₆ restored and the frame popped, at the return's `jumpInd`. -/
theorem fg_alloc_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp al size out r0 r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h6 : ω[6] = UInt64.ofNat size) (h7 : ω[7] = UInt64.ofNat 0)
    (m0 : rdN μ sp 8 = al) (m8 : rdN μ (sp + 8) 8 = out) (m16 : rdN μ (sp + 16) 8 = r6)
    (m24 : rdN μ (sp + 24) 8 = r5) (m32 : rdN μ (sp + 32) 8 = r0)
    (hal : al < 18446744073709551616) (hs : size < 18446744073709551616)
    (hsp : 206852 ≤ sp ∧ sp + 40 < 4294967296) (hout : 206852 ≤ out ∧ out + 24 < 4294967296)
    (dso : out + 24 ≤ sp ∨ sp + 40 ≤ out)
    (hrs : ∀ a, sp ≤ a → a < sp + 40 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeStepsH p R 41109 ω μ x 41175 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 40) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      rdN μ' out 8 = 1 ∧ rdN μ' (out + 8) 8 = al ∧
      rdN μ' (out + 16) 8 = size ∧ rdN μ' 206848 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, h7, m0, m8, m16, m24, m32, hrs, hro, hwo, hwl, hrl, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold, Nat.mod_eq_of_lt hal]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals try simp only [show 16 + out = out + 16 from Nat.add_comm _ _]
    all_goals first
      | (rd_simp []; done)
      | (rd_simp [hwo]; done)
      | rd_simp []
    all_goals first
      | rfl
      | exact Nat.mod_eq_of_lt (by omega)
      | (rw [PVM.Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by unfold PVM.two32; omega),
          Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega))

end Services.Bootstrap.Acc
