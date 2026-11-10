import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Reader
import Services.Bootstrap.Alloc.Register
import PVM.Logic.Go

/-!
# The `u64` compact decoder (46856, body 39982 … 40212)

46856 decodes a natural below 2^64 in `jam-codec`'s compact form (`Dec.compact`; GP v0.8.0
Appendix C's ℰ for naturals, quirk Q1) from a reader: the prefix octet b, then l octets, l the
number of b's leading ones (8 after 255). It returns ω₇ = 0 and ω₈ = the natural, through ω₀.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `a & 2^j` keeps bit j. -/
theorem band_pow (a j : Nat) (hj : j < 64) :
    Exec.bitwise (· && ·) a (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_two_pow]
  by_cases h : j = i
  · subst h; split <;> simp_all
  · split <;> simp [h, Nat.zero_testBit]

/-- 𝒳₁ of an octet, cut to 64 bits. -/
theorem sxw1_mod (b : Nat) (hb : b < 256) :
    sxw 1 b % 18446744073709551616 = if b < 128 then b else b + 18446744073709551360 := by
  simp only [sxw, Exec.u64, Num.unsigned, Num.signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]
  split <;> simp only [Int.reducePow] <;> omega

/-- Bit j < 8 of a sign-extended octet is the octet's. -/
theorem band_sx (b k j : Nat) (hb : b < 256) (hj : j < 8) (hk : k = 2 ^ j) :
    Exec.bitwise (· && ·) (sxw 1 b % 18446744073709551616) k = b / k % 2 * k := by
  subst hk
  rw [band_pow _ _ (by omega), Nat.testBit_eq_decide_div_mod_eq, sxw1_mod b hb]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [Nat.reducePow]; split <;> split <;> simp_all <;> omega

/-- The low octet of a sign-extended octet is the octet. -/
theorem band_sx255 (b : Nat) (hb : b < 256) :
    Exec.bitwise (· && ·) (sxw 1 b % 18446744073709551616) 255 = b := by
  rw [bitwise_and_low _ 255 8 (by decide) (by decide), sxw1_mod b hb]
  split <;> omega

/-- **46856 … 46886**: the 40-octet frame (s = sp − 40; ω₀, ω₅, ω₆ at s + 32, + 24, + 16), the reader
    (ω₇) kept in ω₆, a zero octet at s + 8, and the read of the prefix octet into it (ω₅ = 1, the
    error flag; return address 1968). -/
theorem cu_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp rd : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hsp : 65536 + 40 ≤ sp ∧ sp < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 40 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46856 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1968 ∧ ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[5] = UInt64.ofNat 1 ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (sp - 40 + 8) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 40 + 32) 8 = ω[0].toNat ∧ rdN μ' (sp - 40 + 24) 8 = ω[5].toNat ∧
      rdN μ' (sp - 40 + 16) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 40 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl
      | rw [Nat.mod_eq_of_lt (by omega)]
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | exact UInt64.ofNat_toNat
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      | exact Nat.mod_mod _ _
      | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
      | decide
      | (simp [Num.decodeLE]; done)
      | omega

/-- **39982 … 40164**, the prefix octet b ∉ {0, 255} with l < 8 leading ones
    (2⁸ − 2^(8−l) ≤ b < 2⁸ − 2^(7−l)): b sign-extended saved at s, a zero word at s + 8, and the read
    of l octets into it (ω₆ = l; return address 1972). -/
theorem cu_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s rd b l : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hs : 65536 ≤ s ∧ s + 40 < 4294967296) (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, s ≤ a → a < s + 40 → μ.writable a = true)
    (hb : rdN μ (s + 8) 1 = b) (hl : l < 8) (hb0 : 0 < b) (hb1 : 256 - 2 ^ (8 - l) ≤ b)
    (hb2 : b < 256 - 2 ^ (7 - l)) :
    ∃ ω' μ', FreeStepsH p R 39982 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 1972 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat l ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (s + 8) ∧ ω'[9] = UInt64.ofNat l ∧
      rdN μ' s 8 = sxw 1 b % 18446744073709551616 ∧ rdN μ' (s + 8) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < s ∨ s + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 40 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hb256 : b < 256 := by rw [← hb]; exact rdN_lt μ _ 1
  have e255 := band_sx255 b hb256
  have e64 := band_sx b 64 6 hb256 (by decide) rfl
  have e32 := band_sx b 32 5 hb256 (by decide) rfl
  have e16 := band_sx b 16 4 hb256 (by decide) rfl
  have e8 := band_sx b 8 3 hb256 (by decide) rfl
  have e4 := band_sx b 4 2 hb256 (by decide) rfl
  have e2 := band_sx b 2 1 hb256 (by decide) rfl
  have e1 := band_sx b 1 0 hb256 (by decide) rfl
  have hbm : b % 18446744073709551616 = b := by omega
  have hb0' : b ≠ 0 := by omega
  have hsx := sxw1_mod b hb256
  have : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5 ∨ l = 6 ∨ l = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceSub, Nat.reducePow] at hb1 hb2 ⊢ <;>
    have hbf : b ≠ 255 := by omega
  · have hps : sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hnn : ¬ ((sxw 1 b % 18446744073709551616 : Nat) : Int) < 0 := by omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w0, ?m0, ?run0, ?post0⟩
    case run0 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, hps, hnn,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post0 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w1, ?m1, ?run1, ?post1⟩
    case run1 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post1 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w2, ?m2, ?run2, ?post2⟩
    case run2 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post2 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 1 := by omega
    have q4 : b / 16 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w3, ?m3, ?run3, ?post3⟩
    case run3 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, q4, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post3 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 1 := by omega
    have q4 : b / 16 % 2 = 1 := by omega
    have q3 : b / 8 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w4, ?m4, ?run4, ?post4⟩
    case run4 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, q4, q3, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post4 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 1 := by omega
    have q4 : b / 16 % 2 = 1 := by omega
    have q3 : b / 8 % 2 = 1 := by omega
    have q2 : b / 4 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w5, ?m5, ?run5, ?post5⟩
    case run5 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, q4, q3, q2, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post5 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 1 := by omega
    have q4 : b / 16 % 2 = 1 := by omega
    have q3 : b / 8 % 2 = 1 := by omega
    have q2 : b / 4 % 2 = 1 := by omega
    have q1 : b / 2 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w6, ?m6, ?run6, ?post6⟩
    case run6 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, q4, q3, q2, q1, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post6 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

  · have q6 : b / 64 % 2 = 1 := by omega
    have q5 : b / 32 % 2 = 1 := by omega
    have q4 : b / 16 % 2 = 1 := by omega
    have q3 : b / 8 % 2 = 1 := by omega
    have q2 : b / 4 % 2 = 1 := by omega
    have q1 : b / 2 % 2 = 1 := by omega
    have q0 : b / 1 % 2 = 0 := by omega
    have hng : ¬ sxw 1 b % 18446744073709551616 < 9223372036854775808 := by rw [hsx]; split <;> omega
    have hlt : ((sxw 1 b % 18446744073709551616 : Nat) : Int) - 18446744073709551616 < 0 := by
      have := Nat.mod_lt (sxw 1 b) (show 0 < 18446744073709551616 by decide); omega
    clear hb1 hb2
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?w7, ?m7, ?run7, ?post7⟩
    case run7 => pvm_go [h1, h6, h7, hwf, hr, hb, e255, e64, e32, e16, e8, e4, e2, e1, hbm, hb0', hbf, q6, q5, q4, q3, q2, q1, q0, hng, hlt,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    case post7 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6, h7]
      all_goals try with_reducible rfl
      all_goals try first
        | (rd_simp []; done)
        | rd_simp []
      all_goals try first
        | with_reducible rfl
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
      all_goals first
        | (congr 1; omega)
        | rfl
        | rw [Nat.mod_eq_of_lt (by omega)]
        | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
        | exact UInt64.ofNat_toNat
        | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
        | exact Nat.mod_mod _ _
        | (simp only [Nat.reduceMul, Nat.reducePow, Nat.mod_mod]; done)
        | decide
        | (simp [Num.decodeLE]; done)
        | omega

end Services.Bootstrap.Acc
