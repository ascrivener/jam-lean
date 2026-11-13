import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Alloc.AllocWrap
import PVM.Logic.Go
import Services.Bootstrap.Decode.HeapWrap
import Services.Bootstrap.Decode.VecU8Pass

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

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

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

/-- 41423: `alloc_impl`'s return, through entry 997 (return address 1996), to 41109. -/
theorem fg_ret_jump {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1996) : FreeStepsH p R 41423 ω μ x 41109 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **`finish_grow` with no current block, the model's `alloc` succeeding without growing the
    heap** (40852 → 41175): from memory holding a well-formed `s`, `Ok(ptr, size)` is written at
    `out` for the model's block `ptr` and state `s'`; memory holds `s'` with the lock clear, the
    heap off the new headers is kept (`HKeepG`), and the stack from sp up is kept outside `out`.
    ω₀, ω₁, ω₅, ω₆ are restored, at the return's `jumpInd`. -/
theorem fg_new_hdr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) {grow : Grow} {hb : Nat} (s s' : State) (sp out ncap al el ptr : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (h : alloc grow hb 1 ((ncap * el + 31) / 32) s = some (ptr, s')) (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat ncap) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat el) (hal : 1 ≤ al ∧ al ≤ 32)
    (hsz : 0 < ncap * el) (hs : ncap * el + 31 < 68719476736)
    (hsp : 2147483840 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hSTk : S0 + 192 ≤ sp ∧ out + 24 ≤ S1) (hHT : s.base + 32 * s.allocated ≤ HT) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40852 ω μ x 41175 ω' μ' x 500 ∧ Rep μ' s' ∧ WF s' ∧
      rdN μ' out 8 = 0 ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = ncap * el ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := fun a h1 h2 => hw a (Or.inr ⟨h1, h2⟩)
  -- 1. the entry: the frame, `out` and align stored, the size
  obtain ⟨ω1, μ1, r1, a1, a6, a0, m0, m8, m16, m24, m32, fr1, rd1, wr1⟩ :=
    fg_entry_new (p := p) (P := P) (R := R) x ω μ sp out ncap al el h1 h7 h8 h10 h11 h12 hsz (by omega) (by omega)
      (by omega) ⟨by omega, hsp.2⟩ (fun a h1 h2 => hst a (by omega) (by omega))
  have hw1 : WrAt μ1 HT S0 S1 := hw.of_eq wr1
  have hl1 : rdN μ1 206848 1 = 0 := by rw [rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega))]; exact hl
  -- 2. the lock and the call of `alloc_impl`
  obtain ⟨ω2, μ2, r2, b7, b8, b9, b10, b0, b1, b4, b5, b6, fr2, wr2⟩ :=
    fg_alloc_lock (p := p) (P := P) (R := R) x ω1 μ1 (sp - 40) al (ncap * el) out a1 a6 m0
      (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8) (by omega) hs ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) hl1
      (by omega) hw1
  have hw2 : WrAt μ2 HT S0 S1 := hw1.of_eq wr2
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => by
    unfold A0 at ha1
    rw [fr2 a (by omega) (Or.inr (by omega)) ha3, fr1 a (by omega) (Or.inl (by omega))]
  have hun : (al + 31) / 32 = 1 := by omega
  -- 3. `alloc_impl` refines the model's `alloc`
  obtain ⟨ω3, μ3, r3, rep3, wf3, e7, e0, e5, e6, e1, ww3, stk3, hk3⟩ :=
    alloc_refines_hdr (p := p) (P := P) (R := R) x ω2 μ2 s s' (sp - 40) _ ptr hwf rep2 h hng
      (by rw [b1, a1]) b7 (by rw [b8, hun]) b9 b10 (by omega) (by omega) hb0 hbT hA hfo hHTs
      ⟨by omega, by omega⟩ hHT hw2
  have rj := fg_ret_jump (p := p) (P := P) (R := R) x ω3 μ3 (by rw [e0, b0])
  -- the block is a chunk of s', so it is not null
  have hb' : s'.base = s.base := by
    rw [alloc_one hwf.1] at h; obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := alloc1_eq h; rw [allocPost_base]
  obtain ⟨pre, post, S, -, -, hcs'⟩ := alloc_chunks hwf h
  have hnew : (⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' := by
    rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
  have hin := Services.Bootstrap.Decode.VecU8.chunk_in wf3 hnew rfl
  simp only at hin
  have hp0 : ptr ≠ 0 := by omega
  -- the frame at sp − 40 … sp, as `fg_alloc_ok` reads it
  have k13 : ∀ a, sp - 40 ≤ a → a < 4294967296 → μ3.read a = μ1.read a := fun a h1 h2 => by
    rw [stk3 a h2 h1, fr2 a h2 (Or.inr (by omega)) (Or.inr (by omega))]
  have q : ∀ o v, sp - 40 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ3 o 8 = v := fun o v h1 h2 hv => by
    rw [rdN_frame fun j hj => k13 _ (by omega) (by omega)]; exact hv
  have hwr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [ww3, wr2, wr1]
  obtain ⟨ω4, μ4, r4, c0, c1, c5, c6, o0, o8, o16, ol, fr4, rd4, wr4⟩ :=
    fg_alloc_ok (p := p) (P := P) (R := R) x ω3 μ3 (sp - 40) al (ncap * el) out ptr ω[0].toNat ω[5].toNat
      ω[6].toNat (by rw [e1, b1, a1]) (by rw [e6, b6, a6]) e7 (q _ _ (by omega) (by omega) m0)
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 16 = sp - 24 by omega]; exact m16))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 24 = sp - 16 by omega]; exact m24))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 32 = sp - 8 by omega]; exact m32))
      (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (by rw [hwr3]; exact hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [hwr3]; exact hst a (by omega) (by omega))
      (by rw [hwr3]; exact hw 206848 (Or.inl ⟨by omega, by omega⟩)) hp0
  have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans rj).trans r4).mono (by omega),
    rep3.congr_lock wf3 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr4 a (by omega) (by unfold A0 at ha1; omega) (Or.inl (by omega))),
    wf3, o0, o8, o16, ol, fun a => by rw [wr4, hwr3], ?_, by rw [c0, dec], ?_, by rw [c5, dec],
    by rw [c6, dec], ?_⟩
  · intro a ha hs ho
    rw [fr4 a ha (by omega) ho, stk3 a ha (by omega), fr2 a ha (Or.inr (by omega)) (Or.inr (by omega)),
      fr1 a ha (Or.inr hs)]
  · rw [c1, h1]; congr 1; omega
  · have k1 : HKeepG μ μ1 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ =>
      fr1 a (by omega) (Or.inl (by omega))
    have k2 : HKeepG μ1 μ2 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact fr2 a (by omega) (by omega) (by omega)
    have k4 : HKeepG μ3 μ4 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact fr4 a (by omega) (by omega) (Or.inl (by omega))
    exact ((k1.trans k2).trans hk3).trans k4

/-- **`finish_grow` with no current block, the model's `alloc` growing the heap** (40852 → 41175),
    under a host fit for the allocator (`HeapHost`), the growth's cost within `cap`; otherwise as
    `fg_new_hdr`, with the heap's pages grown to some h' covering the allocated space: from memory holding a well-formed `s`, `Ok(ptr, size)` is written at
    `out` for the model's block `ptr` and state `s'`; memory holds `s'` with the lock clear, the
    heap off the new headers is kept (`HKeepG`), and the stack from sp up is kept outside `out`.
    ω₀, ω₁, ω₅, ω₆ are restored, at the return's `jumpInd`. -/
theorem fg_new_grow {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs)
    (μ : Memory) {hb : Nat} (s s' : State) (sp out ncap al el ptr pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 ((ncap * el + 31) / 32) s = some (ptr, s')) (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat ncap) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat el) (hal : 1 ≤ al ∧ al ≤ 32)
    (hsz : 0 < ncap * el) (hs : ncap * el + 31 < 68719476736)
    (hsp : 2147483840 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 192 ≤ sp ∧ out + 24 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 40852 ω μ x 41175 ω' μ' x 600 ∧ Rep μ' s' ∧ WF s' ∧
      rdN μ' out 8 = 0 ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = ncap * el ∧
      rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) := by
  have hw := HeapPages.wrAt hp hhb hst
  -- 1. the entry: the frame, `out` and align stored, the size
  obtain ⟨ω1, μ1, r1, a1, a6, a0, m0, m8, m16, m24, m32, fr1, rd1, wr1⟩ :=
    fg_entry_new (p := p) (P := P) (R := env.rel cap) x ω μ sp out ncap al el h1 h7 h8 h10 h11 h12 hsz (by omega) (by omega)
      (by omega) ⟨by omega, hsp.2⟩ (fun a h1 h2 => hst a (by omega) (by omega))
  have hw1 : WrAt μ1 (4096 * ph) S0 S1 := hw.of_eq wr1
  have hl1 : rdN μ1 206848 1 = 0 := by rw [rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega))]; exact hl
  -- 2. the lock and the call of `alloc_impl`
  obtain ⟨ω2, μ2, r2, b7, b8, b9, b10, b0, b1, b4, b5, b6, fr2, wr2⟩ :=
    fg_alloc_lock (p := p) (P := P) (R := env.rel cap) x ω1 μ1 (sp - 40) al (ncap * el) out a1 a6 m0
      (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8) (by omega) hs ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) hl1
      (by omega) hw1
  have hw2 : WrAt μ2 (4096 * ph) S0 S1 := hw1.of_eq wr2
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => by
    unfold A0 at ha1
    rw [fr2 a (by omega) (Or.inr (by omega)) ha3, fr1 a (by omega) (Or.inl (by omega))]
  have hun : (al + 31) / 32 = 1 := by omega
  -- 3. `alloc_impl` refines the model's `alloc`
  obtain ⟨ω3, μ3, r3, rep3, wf3, e7, e0, e5, e6, e1, ⟨h', hp3, hsp3, hh1, hh2⟩, hst3, stk3, hk3⟩ :=
    alloc_refines_growK_hdrG (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω2 μ2 s s' (sp - 40) _ ptr pb
      ph hwf rep2 hbd h48 hhb hbs h hgrown (by rw [b1, a1]) b7 (by rw [b8, hun]) b9 b10
      (by omega) (by omega) hb0 hbT hA hfo hcost hHTs ⟨by omega, by omega⟩ hSb
      (HeapPages.of_eq (HeapPages.of_eq hp wr1) wr2) (fun a h1 h2 => by rw [wr2, wr1]; exact hst a h1 h2) hHT
  have rj := fg_ret_jump (p := p) (P := P) (R := env.rel cap) x ω3 μ3 (by rw [e0, b0])
  -- the block is a chunk of s', so it is not null
  have hb' : s'.base = s.base := by
    rw [alloc_one hwf.1] at h; obtain ⟨-, -, -, -, -, -, -, rfl⟩ := alloc1_grown h hgrown; rw [allocPost_base]
  obtain ⟨pre, post, S, -, -, hcs'⟩ := alloc_chunks hwf h
  have hnew : (⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' := by
    rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
  have hin := Services.Bootstrap.Decode.VecU8.chunk_in wf3 hnew rfl
  simp only at hin
  have hp0 : ptr ≠ 0 := by omega
  -- the frame at sp − 40 … sp, as `fg_alloc_ok` reads it
  have k13 : ∀ a, sp - 40 ≤ a → a < 4294967296 → μ3.read a = μ1.read a := fun a h1 h2 => by
    rw [stk3 a h2 h1, fr2 a h2 (Or.inr (by omega)) (Or.inr (by omega))]
  have q : ∀ o v, sp - 40 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ3 o 8 = v := fun o v h1 h2 hv => by
    rw [rdN_frame fun j hj => k13 _ (by omega) (by omega)]; exact hv
  have hwr3 : ∀ a, S0 ≤ a → a < S1 → μ3.writable a = μ.writable a := fun a h1 h2 => by
    rw [hst3 a h1 h2, hst a h1 h2]
  obtain ⟨ω4, μ4, r4, c0, c1, c5, c6, o0, o8, o16, ol, fr4, rd4, wr4⟩ :=
    fg_alloc_ok (p := p) (P := P) (R := env.rel cap) x ω3 μ3 (sp - 40) al (ncap * el) out ptr ω[0].toNat ω[5].toNat
      ω[6].toNat (by rw [e1, b1, a1]) (by rw [e6, b6, a6]) e7 (q _ _ (by omega) (by omega) m0)
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 16 = sp - 24 by omega]; exact m16))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 24 = sp - 16 by omega]; exact m24))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 32 = sp - 8 by omega]; exact m32))
      (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst3 a (by omega) (by omega)))
      (fun a h1 h2 => hst3 a (by omega) (by omega))
      (HeapPages.wrAt hp3 hh2 hst3 206848 (Or.inl ⟨by omega, by have := hp3; omega⟩)) hp0
  have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans rj).trans r4).mono (by omega),
    rep3.congr_lock wf3 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr4 a (by omega) (by unfold A0 at ha1; omega) (Or.inl (by omega))),
    wf3, o0, o8, o16, ol, ⟨h', HeapPages.of_eq hp3 wr4, hsp3, hh1, hh2⟩,
    fun a h1 h2 => by rw [wr4]; exact hst3 a h1 h2, ?_, by rw [c0, dec], ?_, by rw [c5, dec],
    by rw [c6, dec], ?_⟩
  · intro a ha hs ho
    rw [fr4 a ha (by omega) ho, stk3 a ha (by omega), fr2 a ha (Or.inr (by omega)) (Or.inr (by omega)),
      fr1 a ha (Or.inr hs)]
  · rw [c1, h1]; congr 1; omega
  · have k1 : HKeepG μ μ1 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ =>
      fr1 a (by omega) (Or.inl (by omega))
    have k2 : HKeepG μ1 μ2 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact fr2 a (by omega) (by omega) (by omega)
    have k4 : HKeepG μ3 μ4 (fun a => ∃ c ∈ chunks s', c.addr = a) := fun a ⟨ha1, ha2, _⟩ => by
      unfold Glob at ha1; exact fr4 a (by omega) (by omega) (Or.inl (by omega))
    exact ((k1.trans k2).trans hk3).trans k4


/-- **`finish_grow` with no current block, the model's `alloc` failing** (40852 → 41175), under a
    host fit for the allocator: `Err(align, size)` (tag 1) is written at `out`, memory still holds
    `s` with the lock clear and the heap's pages as they were. -/
theorem fg_new_fail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : X) (ω : Regs)
    (μ : Memory) {hb : Nat} (s : State) (sp out ncap al el pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (h : alloc (growTo pb) hb 1 ((ncap * el + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat ncap) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat el) (hal : 1 ≤ al ∧ al ≤ 32)
    (hsz : 0 < ncap * el) (hs : ncap * el + 31 < 68719476736)
    (hsp : 2147483840 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 192 ≤ sp ∧ out + 24 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 40852 ω μ x 41175 ω' μ' x 600 ∧ Rep μ' s ∧
      rdN μ' out 8 = 1 ∧ rdN μ' (out + 8) 8 = al ∧ rdN μ' (out + 16) 8 = ncap * el ∧
      rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a6, a0, m0, m8, m16, m24, m32, fr1, rd1, wr1⟩ :=
    fg_entry_new (p := p) (P := P) (R := env.rel cap) x ω μ sp out ncap al el h1 h7 h8 h10 h11 h12 hsz
      (by omega) (by omega) (by omega) ⟨by omega, hsp.2⟩ (fun a h1 h2 => hst a (by omega) (by omega))
  have hw1 : WrAt μ1 (4096 * ph) S0 S1 := hw.of_eq wr1
  have hl1 : rdN μ1 206848 1 = 0 := by rw [rdN_frame fun j hj => fr1 _ (by omega) (Or.inl (by omega))]; exact hl
  obtain ⟨ω2, μ2, r2, b7, b8, b9, b10, b0, b1, b4, b5, b6, fr2, wr2⟩ :=
    fg_alloc_lock (p := p) (P := P) (R := env.rel cap) x ω1 μ1 (sp - 40) al (ncap * el) out a1 a6 m0
      (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8) (by omega) hs ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) hl1
      (by omega) hw1
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => by
    unfold A0 at ha1
    rw [fr2 a (by omega) (Or.inr (by omega)) ha3, fr1 a (by omega) (Or.inl (by omega))]
  have hun : (al + 31) / 32 = 1 := by omega
  obtain ⟨ω3, μ3, r3, rep3, e7, e0, e5, e6, e1, hp3, hst3, stk3⟩ :=
    alloc_refines_failKG (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap h275 x ω2 μ2 s (sp - 40) _ pb ph
      hwf rep2 hbd h48 hhb hbs h (by omega) (by rw [b1, a1]) b7 (by rw [b8, hun]) b9 (by omega) (by omega)
      hb0 hbT hA hHTs ⟨by omega, by omega⟩ hSb (HeapPages.of_eq (HeapPages.of_eq hp wr1) wr2)
      (fun a h1 h2 => by rw [wr2, wr1]; exact hst a h1 h2) hHT
  have rj := fg_ret_jump (p := p) (P := P) (R := env.rel cap) x ω3 μ3 (by rw [e0, b0])
  have k13 : ∀ a, sp - 40 ≤ a → a < 4294967296 → μ3.read a = μ1.read a := fun a h1 h2 => by
    rw [stk3 a h2 h1, fr2 a h2 (Or.inr (by omega)) (Or.inr (by omega))]
  have q : ∀ o v, sp - 40 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ3 o 8 = v := fun o v h1 h2 hv => by
    rw [rdN_frame fun j hj => k13 _ (by omega) (by omega)]; exact hv
  obtain ⟨ω4, μ4, r4, c0, c1, c5, c6, o0, o8, o16, ol, fr4, rd4, wr4⟩ :=
    fg_alloc_err (p := p) (P := P) (R := env.rel cap) x ω3 μ3 (sp - 40) al (ncap * el) out ω[0].toNat ω[5].toNat
      ω[6].toNat (by rw [e1, b1, a1]) (by rw [e6, b6, a6]) e7 (q _ _ (by omega) (by omega) m0)
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 8 = sp - 32 by omega]; exact m8))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 16 = sp - 24 by omega]; exact m16))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 24 = sp - 16 by omega]; exact m24))
      (q _ _ (by omega) (by omega) (by rw [show sp - 40 + 32 = sp - 8 by omega]; exact m32))
      (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst3 a (by omega) (by omega)))
      (fun a h1 h2 => hst3 a (by omega) (by omega))
      (HeapPages.wrAt hp3 hhb hst3 206848 (Or.inl ⟨by omega, by omega⟩))
  have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
  refine ⟨ω4, μ4, ((((r1.trans r2).trans r3).trans rj).trans r4).mono (by omega),
    rep3.congr_lock hwf hb0 hbT
      (fun a ha1 ha2 ha3 => fr4 a (by omega) (by unfold A0 at ha1; omega) (Or.inl (by omega))),
    o0, o8, o16, ol, HeapPages.of_eq hp3 wr4, fun a h1 h2 => by rw [wr4]; exact hst3 a h1 h2, ?_,
    by rw [c0, dec], ?_, by rw [c5, dec], by rw [c6, dec]⟩
  · intro a ha hs ho
    rw [fr4 a ha (by omega) ho, stk3 a ha (by omega), fr2 a ha (Or.inr (by omega)) (Or.inr (by omega)),
      fr1 a ha (Or.inr hs)]
  · rw [c1, h1]; congr 1; omega

end Services.Bootstrap.Acc
