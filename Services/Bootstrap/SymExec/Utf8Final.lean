import Services.Bootstrap.SymExec.Utf8Fn
import Services.Bootstrap.CodeF.L11

/-!
# `core::str::from_utf8` (60681): the whole function (symexec)

EXPERIMENTAL, WORK IN PROGRESS (see `Services/Bootstrap/SymExec/README.md`). Assembles the entry
check `check0`, the outer loop `outer_loop` and the epilogue checks `checkOk` / `checkErr` into one
statement about a call of `from_utf8(v: &[u8]) -> Result<&str, Utf8Error>` (GP v0.8.0 §A.5):

- `from_utf8_call` (plan (c)): for every input the call returns to the caller, restores r0, r1,
  r5 and r6, changes memory only in its 32-octet stack frame and the 24-octet result, keeps the
  page map, and the result is `Ok(&v[..len])` (0, p, len) or
  `Err(Utf8Error { valid_up_to: v, error_len })` with v < len, the octet at p + v at least 0x80,
  and error_len `None` or `Some 1..3`.
- `from_utf8_ascii` (plan (b)): if every octet of the input is below 0x80, the result is `Ok` with
  the same pointer and length.

Nothing is claimed about which inputs are valid UTF-8 beyond (b).
-/

namespace Services.Bootstrap.SymExec.Utf8

open PVM PVM.SymExec Num Exec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The 2^64-bit mask with the low 3 bits cleared rounds down to a multiple of 8. -/
theorem and_m8 (n : Nat) (h : n < 2 ^ 64) : n &&& (2 ^ 64 - 8) = n / 8 * 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show n / 8 * 8 = n / 2 ^ 3 * 2 ^ 3 by rfl, Nat.testBit_mul_two_pow,
    Nat.testBit_div_two_pow, show (2 ^ 64 - 8 : Nat) = (2 ^ 61 - 1) * 2 ^ 3 by decide,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hi : 64 ≤ i
  · have : n.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))
    simp [this, show i - 3 + 3 = i by omega]
  · by_cases h3 : 3 ≤ i
    · simp [h3, show i - 3 + 3 = i by omega, show i - 3 < 61 by omega]
    · simp [h3]

/-- The loop's named naturals at its first entry, evaluated. -/
theorem sub0_eval (E : Env) :
    svals E sub0 = [E.ρ 0, E.ρ 1, 0, ((E.ρ 0 : Int) + 0).toNat, E.ρ 4, alignT.eval E, mT.eval E,
      r11T.eval E, E.ρ 8, E.ρ 9, E.ρ 10, E.ρ 11, E.ρ 12, 0, 0] := by
  simp [svals, sub0, SVal.eval, Aff.eval]

theorem alignT_eq (E : Env) :
    alignT.eval E = ((((E.ρ 0 : Int) + 7).toNat &&& (2 ^ 64 - 8)) % 2 ^ 64 + 2 ^ 64 - E.ρ 0) % 2 ^ 64 := by
  show threeRegAlu .sub64 (bitwise (· && ·) (((E.ρ 0 : Int) + 7).toNat) (2 ^ 64 - 8)) (E.ρ 0) 0 = _
  rw [bitwise_and_eq]; rfl

theorem alignT_lt (E : Env) (h : E.ρ 0 < 2 ^ 32) : alignT.eval E < 8 := by
  rw [alignT_eq, show ((E.ρ 0 : Int) + 7).toNat = E.ρ 0 + 7 by omega, and_m8 _ (by omega)]
  have h1 := Nat.div_mul_le_self (E.ρ 0 + 7) 8
  have h2 := Nat.lt_div_mul_add (a := E.ρ 0 + 7) (b := 8) (by decide)
  have hx : (E.ρ 0 + 7) / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hx,
    show (E.ρ 0 + 7) / 8 * 8 + 2 ^ 64 - E.ρ 0 = ((E.ρ 0 + 7) / 8 * 8 - E.ρ 0) + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

/- The ALU values below are unfolded by `rfl` lemmas whose right side is a constructor or matches
   the definition syntactically: a definitional check that unfolds `x + 2^64` runs out of memory. -/
theorem maxU_eq (a b d : Nat) : threeRegAlu .maxU a b d = max a b := rfl
theorem add64_eq (a b x : Nat) : (twoRegImmAlu .addImm64 a b x).getD 0 = (b + x) % two64 := rfl
theorem nadd64_eq (a b x : Nat) :
    twoRegImmAlu .negAddImm64 a b x = some ((x + two64 - b) % two64) := rfl

theorem mT_closed (E : Env) : mT.eval E = (max (E.ρ 1) 15 % 2 ^ 64 + (2 ^ 64 - 15)) % two64 := by
  have e1 : mT.eval E = (twoRegImmAlu .addImm64 0 (threeRegAlu .maxU (E.ρ 1) 15 0 % 2 ^ 64)
      (2 ^ 64 - 15)).getD 0 := rfl
  rw [maxU_eq, add64_eq] at e1
  exact e1

theorem mT_eval (E : Env) (h : E.ρ 1 < 2 ^ 32) : mT.eval E + 15 = max (E.ρ 1) 15 := by
  have e1 := mT_closed E
  simp only [two64] at e1
  omega

theorem r11T_closed (E : Env) : r11T.eval E = (0 + two64 - E.ρ 1) % two64 := by
  have e1 : r11T.eval E = (twoRegImmAlu .negAddImm64 0 (E.ρ 1) 0).getD 0 := rfl
  rw [nadd64_eq, Option.getD_some] at e1
  exact e1

theorem r11T_eval (E : Env) (h0 : E.ρ 1 ≠ 0) (h : E.ρ 1 < 2 ^ 32) :
    r11T.eval E + E.ρ 1 = 2 ^ 64 := by
  have e1 := r11T_closed E
  simp only [two64] at e1
  omega

theorem rd_of_wr {μ : Memory} {a : Nat} (h : μ.writable a = true) : μ.readable a = true := by
  simp only [Memory.writable, beq_iff_eq] at h
  simp only [Memory.readable, h, Option.isSome_some]

/-- The result of a call of `from_utf8` at O, μ the memory at the call and μ' at the return:
    `Ok(&v[..len])` is (0 : u64, p : u64, len : u64); `Err(Utf8Error { valid_up_to, error_len })`
    is (1 : u64, valid_up_to : u64, error_len : `Option<u8>` as a tag octet then a value octet). -/
def Utf8Res (μ μ' : Memory) (pa len O : Nat) : Prop :=
  (μ'.readN O 8 = encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = encodeLE 8 pa ∧
    μ'.readN (O + 16) 8 = encodeLE 8 len) ∨
  ∃ v c2 c3, v < len ∧ ((c2 = 0 ∧ c3 = 1) ∨ (c2 = 1 ∧ (c3 = 1 ∨ c3 = 2 ∨ c3 = 3))) ∧
    128 ≤ decodeLE (μ.readN (pa + v) 1) ∧
    μ'.readN O 8 = encodeLE 8 1 ∧ μ'.readN (O + 8) 8 = encodeLE 8 v ∧
    μ'.readN (O + 16) 1 = encodeLE 1 c2 ∧ μ'.readN (O + 17) 1 = encodeLE 1 c3

/-- What a returned call leaves (ω', μ') as, against the call state (ω, μ). -/
def Utf8Ret (ω : Regs) (μ : Memory) (sp O : Nat) (ω' : Regs) (μ' : Memory) : Prop :=
  ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
  (∀ a, a < 2 ^ 32 → (a < sp ∨ sp + 32 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
  μ'.pages = μ.pages

/-- The named naturals at the entry. -/
def vals0 (pa len sp O ret s5 s6 : Nat) : List Nat :=
  [pa, len, 0, 0, sp, 0, 0, 0, ret, s5, s6, O, pa + len, 0, 0]

section
variable {X : Type} {p : ByteArray} {R : HostRel X}

/-- The calling-convention premises shared by the lemmas below. -/
structure Pre (ω : Regs) (μ : Memory) (pa len sp O ret : Nat) : Prop where
  h0 : ω[0] = UInt64.ofNat ret
  h1 : ω[1] = UInt64.ofNat (sp + 32)
  h7 : ω[7] = UInt64.ofNat O
  h8 : ω[8] = UInt64.ofNat pa
  h9 : ω[9] = UInt64.ofNat len
  hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0
  hpa : pa < 2 ^ 32 ∧ len < 2 ^ 32 ∧ pa + len ≤ 2 ^ 32
  hsp : sp + 32 < 2 ^ 32
  hO : O + 24 < 2 ^ 32
  hOs : O + 24 ≤ sp ∨ sp + 32 ≤ O
  hps : pa + len ≤ sp ∨ sp + 32 ≤ pa
  hrd : ∀ a, pa ≤ a → a < pa + len → μ.readable a = true
  hwf : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true
  hwo : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true
  hrt : ∀ a, 71078 ≤ a → a < 71334 → μ.readable a = true

/-- From 61086 with `HOkE` (named naturals `vals0`) to the return t. -/
theorem finish_ok {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {ω : Regs} {μ : Memory}
    {pa len sp O ret t : Nat} (H : Pre ω μ pa len sp O ret)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    {ω₁ : Regs} {μ₁ : Memory}
    (hA : HOkE.Holds (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) μ ω₁ μ₁) :
    ∃ k ω' μ', FreeStepsH p R 61086 ω₁ μ₁ x t ω' μ' x k ∧ Utf8Ret ω μ sp O ω' μ' ∧
      Utf8Res μ μ' pa len O := by
  obtain ⟨h0, h1, -, -, -, hret, hpa, hsp, hO, hOs, -, -, -, -, -⟩ := H
  have hb : BHold (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ubE := by
    have := UInt64.toNat_lt (ω[5]); have := UInt64.toNat_lt (ω[6])
    simp only [BHold, ubE, vals0]; omega15
  have hl : LBHold (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) lb1 := by simp only [LBHold, lb1, vals0]; omega15
  have hs : ∀ ω₂ μ₂, SepHold (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω₂ μ₂) sepE := fun _ _ =>
    ⟨fun t h1 h2 => by
      simp only [InReg, Aff.eval, env, af, vals0, List.getD_cons_succ, List.getD_cons_zero] at h1 h2
      omega, trivial⟩
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, -, hB⟩ :=
    fork_sound checkOk (hypU (p := p) (P := P)) trivial hb hl hs hA trivial x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  subst hℓ
  rw [svals_idsub15 rfl] at hB
  obtain ⟨⟨r0, r1, r5, r6, -⟩, ⟨c0, c1, c2, -⟩, -, -, hfr, hpg⟩ := hB
  simp only [SVal.eval, Aff.eval, env, af, vr, vals0, List.getD_cons_succ, List.getD_cons_zero]
    at r0 r1 r5 r6 c0 c1 c2
  have hlast := ret_step (R := R) (μ := μ') (x := x) (Services.Bootstrap.CodeF.d_61107 (p := p) (P := P))
    r0 hret.1 (by rw [Services.Bootstrap.Code.jts (p := p) (P := P)]; omega) hret.2.2 (by omega) hjt hbt
  refine ⟨_, ω', μ', hrun.trans hlast, ⟨?_, ?_, ?_, ?_, ?_, hpg⟩, Or.inl ⟨?_, ?_, ?_⟩⟩
  · exact r0.trans h0.symm
  · rw [show ((sp : Int) + 32).toNat = sp + 32 by omega] at r1; exact r1.trans h1.symm
  · exact r5.trans UInt64.ofNat_toNat
  · exact r6.trans UInt64.ofNat_toNat
  · intro a ha hs ho
    refine hfr a ha fun f hf hin => ?_
    simp only [HOkX, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;>
      simp only [InReg, Aff.eval, env, af, vals0, List.getD_cons_succ, List.getD_cons_zero] at hin <;>
      omega
  · simpa using c0
  · simpa [show ((O : Int) + 8).toNat = O + 8 by omega] using c1
  · simpa [show ((O : Int) + 16).toNat = O + 16 by omega] using c2

/-- The named naturals at the error exit: valid_up_to v, error_len (c2, c3). -/
def wE (pa len v sp O ret s5 s6 c2 c3 : Nat) : List Nat :=
  [pa, len, v, 0, sp, 0, 0, 0, ret, s5, s6, O, pa + len, c2, c3]

/-- From 61138 with `HEE` to the return t. -/
theorem finish_err {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] {x : X} {ω : Regs} {μ : Memory}
    {pa len sp O ret t v c2 c3 : Nat} (H : Pre ω μ pa len sp O ret)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv : v < len) (hc : (c2 = 0 ∧ c3 = 1) ∨ (c2 = 1 ∧ (c3 = 1 ∨ c3 = 2 ∨ c3 = 3)))
    (hoct : 128 ≤ decodeLE (μ.readN (pa + v) 1))
    {ω₁ : Regs} {μ₁ : Memory}
    (hA : HEE.Holds (wE pa len v sp O ret ω[5].toNat ω[6].toNat c2 c3) μ ω₁ μ₁) :
    ∃ k ω' μ', FreeStepsH p R 61138 ω₁ μ₁ x t ω' μ' x k ∧ Utf8Ret ω μ sp O ω' μ' ∧
      Utf8Res μ μ' pa len O := by
  obtain ⟨h0, h1, -, -, -, hret, hpa, hsp, hO, hOs, -, -, -, -, -⟩ := H
  have hb : BHold (wE pa len v sp O ret ω[5].toNat ω[6].toNat c2 c3) ubE := by
    have := UInt64.toNat_lt (ω[5]); have := UInt64.toNat_lt (ω[6])
    simp only [BHold, ubE, wE]; omega15
  have hl : LBHold (wE pa len v sp O ret ω[5].toNat ω[6].toNat c2 c3) lb1 := by simp only [LBHold, lb1, wE]; omega15
  have hs : ∀ ω₂ μ₂, SepHold (env (wE pa len v sp O ret ω[5].toNat ω[6].toNat c2 c3) ω₂ μ₂) sepE := fun _ _ =>
    ⟨fun t h1 h2 => by
      simp only [InReg, Aff.eval, env, af, wE, List.getD_cons_succ, List.getD_cons_zero] at h1 h2
      omega, trivial⟩
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, -, hB⟩ :=
    fork_sound checkErr (hypU (p := p) (P := P)) trivial hb hl hs hA trivial x
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  subst hℓ
  rw [svals_idsub15 rfl] at hB
  obtain ⟨⟨r0, r1, r5, r6, -⟩, ⟨c0, c1, c2', c3', -⟩, -, -, hfr, hpg⟩ := hB
  simp only [SVal.eval, Aff.eval, env, af, vr, wE, List.getD_cons_succ, List.getD_cons_zero]
    at r0 r1 r5 r6 c0 c1 c2' c3'
  have hlast := ret_step (R := R) (μ := μ') (x := x) (Services.Bootstrap.CodeF.d_61164 (p := p) (P := P))
    r0 hret.1 (by rw [Services.Bootstrap.Code.jts (p := p) (P := P)]; omega) hret.2.2 (by omega) hjt hbt
  refine ⟨_, ω', μ', hrun.trans hlast, ⟨?_, ?_, ?_, ?_, ?_, hpg⟩,
    Or.inr ⟨v, c2, c3, hv, hc, hoct, ?_, ?_, ?_, ?_⟩⟩
  · exact r0.trans h0.symm
  · rw [show ((sp : Int) + 32).toNat = sp + 32 by omega] at r1; exact r1.trans h1.symm
  · exact r5.trans UInt64.ofNat_toNat
  · exact r6.trans UInt64.ofNat_toNat
  · intro a ha hs ho
    refine hfr a ha fun f hf hin => ?_
    simp only [HEX, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;>
      simp only [InReg, Aff.eval, env, af, wE, List.getD_cons_succ, List.getD_cons_zero] at hin <;>
      omega
  · simpa using c0
  · simpa [show ((O : Int) + 8).toNat = O + 8 by omega] using c1
  · simpa [show ((O : Int) + 16).toNat = O + 16 by omega] using c2'
  · simpa [show ((O : Int) + 17).toNat = O + 17 by omega] using c3'

/-- The outer loop's Ok exit, as the epilogue check needs it. -/
theorem hoke_of {vals : List Nat} {μ : Memory} {ω' : Regs} {μ' : Memory}
    {pa len sp O ret s5 s6 : Nat} (hH : HOk.Holds vals μ ω' μ')
    (hK : ∀ k ∈ keepO, vals.getD k 0 = (vals0 pa len sp O ret s5 s6).getD k 0)
    (hwf : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true)
    (hwo : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    HOkE.Holds (vals0 pa len sp O ret s5 s6) μ ω' μ' := by
  have k0 := hK 0 (by decide); have k1 := hK 1 (by decide); have k4 := hK 4 (by decide)
  have k8 := hK 8 (by decide); have k9 := hK 9 (by decide); have k10 := hK 10 (by decide)
  have k11 := hK 11 (by decide)
  simp only [vals0, List.getD_cons_succ, List.getD_cons_zero] at k0 k1 k4 k8 k9 k10 k11
  simp only [Cut.Holds, HOk, cells1, RegsHold, CellsHold, SVal.eval, Aff.eval, env, af, vr, k0, k1,
    k4, k8, k9, k10, k11] at hH
  obtain ⟨⟨r1, r7, r8, r9, -⟩, ⟨c0, c1, c2, -, -⟩, -, -, hfr, hpg⟩ := hH
  simp only [Cut.Holds, HOkE, cells3, RegsHold, CellsHold, RdHold, WrHold, SVal.eval, Aff.eval,
    env, af, vr, vals0, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨r1, r7, r8, r9, trivial⟩, ⟨c0, c1, c2, trivial⟩,
    ⟨fun t ht => ?_, trivial⟩, ⟨fun t ht => ?_, trivial⟩, fun t ht hf => hfr t ht ?_, hpg⟩
  · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
    rw [readable_pages hpg]; exact rd_of_wr (hwf t (by omega) (by omega))
  · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
    rw [writable_pages hpg]; exact hwo t (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, InReg, Aff.eval, k4,
      List.getD_cons_succ, List.getD_cons_zero] at hf ⊢
    exact hf

/-- The outer loop's error exit, as the epilogue check needs it. -/
theorem hee_of {vals : List Nat} {μ : Memory} {ω' : Regs} {μ' : Memory}
    {pa len sp O ret s5 s6 c2 c3 : Nat} (hH : (HE c2 c3).Holds vals μ ω' μ')
    (hK : ∀ k ∈ keepO, vals.getD k 0 = (vals0 pa len sp O ret s5 s6).getD k 0)
    (hwf : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true)
    (hwo : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    HEE.Holds (wE pa len (vals.getD 2 0) sp O ret s5 s6 c2 c3) μ ω' μ' := by
  have k0 := hK 0 (by decide); have k1 := hK 1 (by decide); have k4 := hK 4 (by decide)
  have k8 := hK 8 (by decide); have k9 := hK 9 (by decide); have k10 := hK 10 (by decide)
  have k11 := hK 11 (by decide)
  simp only [vals0, List.getD_cons_succ, List.getD_cons_zero] at k0 k1 k4 k8 k9 k10 k11
  simp only [Cut.Holds, HE, cells1, RegsHold, CellsHold, SVal.eval, Aff.eval, env, af, vr, k0, k1,
    k4, k8, k9, k10, k11] at hH
  obtain ⟨⟨-, r1, r2, r3, -, r5, r7, -, -, -, -⟩, ⟨c0, c1, c2', -, -⟩, -, -, hfr, hpg⟩ := hH
  simp only [Cut.Holds, HEE, cells3, RegsHold, CellsHold, RdHold, WrHold, SVal.eval, Aff.eval,
    env, af, vr, wE, List.getD_cons_succ, List.getD_cons_zero]
  refine ⟨⟨r1, r2, r3, r5, r7, trivial⟩, ⟨c0, c1, c2', trivial⟩,
    ⟨fun t ht => ?_, trivial⟩, ⟨fun t ht => ?_, trivial⟩, fun t ht hf => hfr t ht ?_, hpg⟩
  · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
    rw [readable_pages hpg]; exact rd_of_wr (hwf t (by omega) (by omega))
  · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
    rw [writable_pages hpg]; exact hwo t (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, InReg, Aff.eval, k4,
      List.getD_cons_succ, List.getD_cons_zero] at hf ⊢
    exact hf

/-- **A call of `core::str::from_utf8`** (60681, plan (c)). Called with the result's address O
    (ω₇), the input's address p (ω₈) and length len (ω₉), the stack pointer sp + 32 (ω₁) and a
    return address ω₀ = ret that `djump` resolves to t. Premises (the calling convention):
    - p < 2^32, len < 2^32, p + len ≤ 2^32 and [p, p + len) readable;
    - the 32-octet frame [sp, sp + 32) below the stack pointer writable, sp + 32 < 2^32;
    - the result [O, O + 24) writable, O + 24 < 2^32, and apart from the frame;
    - the input apart from the frame;
    - the UTF-8 width table [71078, 71334) readable.
    No hypothesis about the table's contents. Then the call returns to t with r0, r1, r5 and r6
    restored, memory changed only in the frame and the result, the page map kept, and the result
    `Ok(&v[..len])` or `Err(Utf8Error { valid_up_to: v, error_len })` with v < len, the octet at
    p + v at least 0x80 and error_len `None` or `Some 1..3` (`Utf8Res`). -/
theorem from_utf8_call {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (pa len sp O ret t : Nat) (H : Pre ω μ pa len sp O ret)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true) :
    ∃ k ω' μ', FreeStepsH p R 60681 ω μ x t ω' μ' x k ∧ Utf8Ret ω μ sp O ω' μ' ∧
      Utf8Res μ μ' pa len O := by
  have H' := H
  obtain ⟨h0, h1, h7, h8, h9, hret, hpa, hsp, hO, hOs, hps, hrd, hwf, hwo, hrt⟩ := H'
  have hB0 : BHold (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ub0 := by
    have := UInt64.toNat_lt (ω[5]); have := UInt64.toNat_lt (ω[6])
    simp only [BHold, ub0, vals0]; omega15
  have hA0 : H0.Holds (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) μ ω μ := by
    simp only [Cut.Holds, H0, RegsHold, CellsHold, RdHold, WrHold, SVal.eval, Aff.eval, env, af,
      vr, vals0, List.getD_cons_succ, List.getD_cons_zero, UInt64.ofNat_toNat]
    refine ⟨⟨h0, ?_, rfl, rfl, h7, h8, h9, trivial⟩, trivial, trivial,
      ⟨fun t ht => ?_, fun t ht => ?_, trivial⟩, fun _ _ _ => trivial, trivial⟩
    · rw [show ((sp : Int) + 32).toNat = sp + 32 by omega]; exact h1
    · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
      exact hwf t (by omega) (by omega)
    · simp only [InReg, Aff.eval, List.getD_cons_succ, List.getD_cons_zero] at ht
      exact hwo t (by omega) (by omega)
  have hasm : FactsHold (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ) asm0 := by
    simp only [asm0, FactsHold, Fact.Holds, Aff.eval, env, af, vals0, List.getD_cons_succ,
      List.getD_cons_zero]
    exact ⟨trivial, fun t h1 h2 => hrd t (by omega) (by omega),
      fun t h1 h2 => hrt t (by omega) (by omega), trivial⟩
  obtain ⟨ℓ, hℓ, k, ω₁, μ₁, hrun, hf, hB⟩ :=
    fork_sound check0 (hypU (p := p) (P := P)) trivial hB0 (lb1_of rfl) (fun _ _ => trivial) hA0
      hasm x
  simp only [leaves0, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl
  · rw [svals_idsub15 rfl] at hB
    obtain ⟨k', ω', μ', h2, hr, hs⟩ := finish_ok (R := R) (x := x) H hjt hbt hB
    exact ⟨_, ω', μ', hrun.trans h2, hr, hs⟩
  · simp only [FactsHold, Fact.Holds, SVal.eval, env, vals0, List.getD_cons_succ,
      List.getD_cons_zero] at hf
    have hl : len ≠ 0 := hf.1
    rw [sub0_eval] at hB
    have ha5 := alignT_lt (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ)
      (by simp only [env, vals0, List.getD_cons_zero]; omega)
    have ha6 := mT_eval (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ)
      (by simp only [env, vals0, List.getD_cons_succ, List.getD_cons_zero]; omega)
    have ha7 := r11T_eval (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ)
      (by simp only [env, vals0, List.getD_cons_succ, List.getD_cons_zero]; omega)
      (by simp only [env, vals0, List.getD_cons_succ, List.getD_cons_zero]; omega)
    generalize alignT.eval (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ) = a5 at hB ha5
    generalize mT.eval (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ) = a6 at hB ha6
    generalize r11T.eval (env (vals0 pa len sp O ret ω[5].toNat ω[6].toNat) ω μ) = a7 at hB ha7
    simp only [env, vals0, List.getD_cons_succ, List.getD_cons_zero,
      show ((pa : Int) + 0).toNat = pa by omega] at hB ha6 ha7
    have hp1 := hB.2.2.2.2.2
    have hR : RdO μ [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O, pa + len, 0, 0] := by
      simp only [RdO, List.getD_cons_succ, List.getD_cons_zero]
      exact ⟨fun t h1 h2 => hrd t h1 h2, fun t h1 h2 => hrt t h1 h2,
        fun t h1 h2 => rd_of_wr (hwf t h1 h2)⟩
    have hK0 : Keep keepO [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O, pa + len, 0, 0]
        [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O, pa + len, 0, 0] :=
      fun _ _ => rfl
    have hInv : Inv1 μ [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O, pa + len, 0, 0]
        [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O, pa + len, 0, 0] ω₁ μ₁ := by
      have := UInt64.toNat_lt (ω[5]); have := UInt64.toNat_lt (ω[6])
      refine ⟨⟨?_, ?_, ?_, hK0⟩, ?_, lb1_of rfl, asm1_of hR hK0 hp1 ?_ ?_ ?_, hB⟩ <;>
        simp only [BHold, ub1, List.getD_cons_succ, List.getD_cons_zero]
      · omega
      · omega
      · omega
      · omega15
      all_goals omega
    obtain ⟨xpc, k2, ω₂, μ₂, h2, hq⟩ := outer_loop (P := P) (R := R) hR x _ ω₁ μ₁ hInv
    have hKV : ∀ vals, Keep keepO [pa, len, 0, pa, sp, a5, a6, a7, ret, ω[5].toNat, ω[6].toNat, O,
        pa + len, 0, 0] vals →
        ∀ k ∈ keepO, vals.getD k 0 = (vals0 pa len sp O ret ω[5].toNat ω[6].toNat).getD k 0 := by
      intro vals hK k hk
      rw [hK k hk]
      simp only [keepO, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rcases hq with ⟨rfl, vals, hH, hK⟩ | ⟨rfl, vals, c2, c3, hH, hK, hc, hi, hoct⟩
    · obtain ⟨k', ω', μ', h3, hr, hs⟩ :=
        finish_ok (R := R) (x := x) H hjt hbt (hoke_of hH (hKV vals hK) hwf hwo)
      exact ⟨_, ω', μ', (hrun.trans h2).trans h3, hr, hs⟩
    · have k0 := hK 0 (by decide); have k1 := hK 1 (by decide)
      simp only [List.getD_cons_succ, List.getD_cons_zero] at k0 k1
      rw [k0] at hoct; rw [k1] at hi
      obtain ⟨k', ω', μ', h3, hr, hs⟩ :=
        finish_err (R := R) (x := x) H hjt hbt hi hc hoct (hee_of hH (hKV vals hK) hwf hwo)
      exact ⟨_, ω', μ', (hrun.trans h2).trans h3, hr, hs⟩

/-- **`from_utf8` on ASCII** (plan (b)): with the premises of `from_utf8_call`, if every octet of
    the input is below 0x80, the call returns `Ok` with the same pointer and length. -/
theorem from_utf8_ascii {P : Program} [Services.Bootstrap.CodeF.HasCodeF p P]
    [Services.Bootstrap.Code.HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (pa len sp O ret t : Nat) (H : Pre ω μ pa len sp O ret)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hasc : ∀ j, j < len → decodeLE (μ.readN (pa + j) 1) < 128) :
    ∃ k ω' μ', FreeStepsH p R 60681 ω μ x t ω' μ' x k ∧ Utf8Ret ω μ sp O ω' μ' ∧
      μ'.readN O 8 = encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = encodeLE 8 pa ∧
      μ'.readN (O + 16) 8 = encodeLE 8 len := by
  obtain ⟨k, ω', μ', h, hr, hs | ⟨v, -, -, hv, -, hoct, -⟩⟩ :=
    from_utf8_call (R := R) x ω μ pa len sp O ret t H hjt hbt
  · exact ⟨k, ω', μ', h, hr, hs⟩
  · exact absurd (hasc v hv) (by omega)

end

end Services.Bootstrap.SymExec.Utf8
