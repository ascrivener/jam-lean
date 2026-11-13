import PVM.SymExec.Check
import Services.Bootstrap.Code

/-!
EXPERIMENTAL (symexec spike, `docs/symexec-spike.md`): symbolic memory. The stretches `z1` and `z2`
of `Services.Bootstrap.Decode.Fixed` (`Zombify`'s `u32` field), whose stack pointer `A` and output
slot `O` are symbolic, re-proved by the executor with the same statements. `z2` ends in a return
through the jump table to a symbolic address (`ret_step`). Written by hand.
-/

namespace PVM.SymExec.FixedZ

open PVM Services.Bootstrap.Code

variable {X : Type} {R : HostRel X}

/-! ## `z1`: 21219 … 21243, a 16-octet frame at A − 16 -/

def st1 : Static :=
  { ub := [4294967296], lb := [65552], rd := [], wr := [(⟨some 0, -16⟩, 16)], sep := [] }

def G1 : Prog :=
  { code := (.node (.node (.node (.node .leaf
    ⟨21219, (.twoReg (.moveReg) 7 6), 21221⟩ .leaf)
    ⟨21221, (.regImm (.loadImm) 0 970), 21225⟩ .leaf)
    ⟨21225, (.twoRegImm (.addImm64) 1 1 18446744073709551600), 21228⟩ (.node .leaf
    ⟨21228, (.twoRegImm (.storeIndU64) 0 1 8), 21231⟩ .leaf))
    ⟨21231, (.regTwoImm (.storeImmIndU32) 1 4 0), 21234⟩ (.node (.node (.node .leaf
    ⟨21234, (.twoRegImm (.addImm64) 8 1 4), 21237⟩ .leaf)
    ⟨21237, (.regImm (.loadImm) 9 4), 21240⟩ .leaf)
    ⟨21240, (.regImm (.loadImm) 0 98), 21243⟩ (.node .leaf
    ⟨21243, (.oneOffset (.jump) 58434), 21247⟩ .leaf)))
    bs := [(58434, true)], jt := [], jsize := 1403 }

def A1 : Spec := { regs := [(1, .var 0)], cells := [] }

def T1 : Spec :=
  { regs := [(0, .const 98), (1, .addr ⟨some 0, -16⟩), (5, .reg0 5), (6, .reg0 6), (7, .reg0 6),
      (8, .addr ⟨some 0, -12⟩), (9, .const 4)]
    cells := [(⟨some 0, -8⟩, 8, .const 970)] }

def F1 : List (Aff × Nat) := [(⟨some 0, -12⟩, 12)]

theorem ok1 : check st1 G1 A1 T1 F1 21219 58434 9 = true := by decide +kernel

/-- The statement of `Services.Bootstrap.Decode.Fixed.z1`, by the executor. -/
theorem z1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A : Nat)
    (hA : 65536 + 16 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A)
    (hw : ∀ a, A - 16 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21219 ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 98 ∧ ω'[1] = UInt64.ofNat (A - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (A - 12) ∧ ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 970 ∧
      (∀ a, a < 4294967296 → (a < A - 12 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω', μ', hrun, ⟨r0, r1, r5, r6, r7, r8, r9, -⟩, ⟨c0, -⟩, hfr, hpg⟩ :=
    check_sound (R := R) ok1 ⟨d_21231 (p := p) (P := P), ⟨d_21225 (p := p) (P := P), ⟨d_21221 (p := p) (P := P), ⟨d_21219 (p := p) (P := P), trivial, trivial⟩, trivial⟩, ⟨d_21228 (p := p) (P := P), trivial, trivial⟩⟩, ⟨d_21240 (p := p) (P := P), ⟨d_21237 (p := p) (P := P), ⟨d_21234 (p := p) (P := P), trivial, trivial⟩, trivial⟩, ⟨d_21243 (p := p) (P := P), trivial, trivial⟩⟩⟩
      ⟨bs_58434 (p := p) (P := P), trivial⟩ trivial (jts (p := p) (P := P))
      [A] ⟨hA.2, trivial⟩ ⟨hA.1, trivial⟩ ω μ trivial
      ⟨fun t ht => by simp only [InReg, Aff.eval] at ht; exact hw t (by simp at ht; omega) (by simp at ht; omega), trivial⟩
      trivial ⟨h1, trivial⟩ trivial x
  simp only [SVal.eval, Aff.eval, List.getD_cons_zero, UInt64.ofNat_toNat] at r1 r8 c0 r5 r6 r7
  refine ⟨ω', μ', hrun, r0, ?_, r5, r6, r7, ?_, r9, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · rw [show A - 16 = ((A : Int) + -16).toNat by omega]; exact r1
  · rw [show A - 12 = ((A : Int) + -12).toNat by omega]; exact r8
  · rw [show A - 8 = ((A : Int) + -8).toNat by omega]; exact c0
  · intro a ha hout
    refine hfr a ha fun f hf hin => ?_
    simp only [F1, List.mem_singleton] at hf; subst hf
    simp only [InReg, Aff.eval, List.getD_cons_zero] at hin
    omega
  · exact readable_pages hpg a
  · exact writable_pages hpg a

/-! ## `z2`: 3780 … 3789 then 21247 … 21282, the `u32` stub and `Zombify`'s return -/

/-- Named naturals: A, O, ret, v5, v6, v. -/
def st2 : Static :=
  { ub := [4294967240, 4294967285, 2807, 18446744073709551616, 18446744073709551616, 4294967296]
    lb := [65552, 0, 1, 0, 0, 0]
    rd := [(⟨some 0, -16⟩, 72)]
    wr := [(⟨some 1, 0⟩, 12)]
    sep := [((⟨some 1, 0⟩, 12), (⟨some 0, -12⟩, 68))] }

def G2 : Prog :=
  { code := (.node (.node (.node (.node .leaf
    ⟨3780, (.twoRegImm (.loadIndI32) 8 1 4), 3783⟩ .leaf)
    ⟨3783, (.twoRegImm (.loadIndU64) 0 1 8), 3786⟩ (.node .leaf
    ⟨3786, (.twoRegImm (.addImm64) 1 1 16), 3789⟩ .leaf))
    ⟨3789, (.regImm (.jumpInd) 0 0), 3791⟩ (.node (.node .leaf
    ⟨21247, (.twoRegImm (.andImm) 7 7 1), 21250⟩ .leaf)
    ⟨21250, (.regImmOffset (.branchNeImm) 7 0 20629), 21254⟩ (.node .leaf
    ⟨21254, (.noArgs (.unlikely)), 21255⟩ .leaf)))
    ⟨21255, (.twoRegImm (.storeIndU32) 8 5 8), 21258⟩ (.node (.node (.node .leaf
    ⟨21258, (.regExtImm (.loadImm64) 7 9223372036854775810), 21268⟩ .leaf)
    ⟨21268, (.twoRegImm (.storeIndU64) 7 5 0), 21270⟩ (.node .leaf
    ⟨21270, (.twoRegImm (.loadIndU64) 0 1 48), 21273⟩ .leaf))
    ⟨21273, (.twoRegImm (.loadIndU64) 5 1 40), 21276⟩ (.node (.node .leaf
    ⟨21276, (.twoRegImm (.loadIndU64) 6 1 32), 21279⟩ .leaf)
    ⟨21279, (.twoRegImm (.addImm64) 1 1 56), 21282⟩ .leaf)))
    bs := [(20629, true), (21247, true), (21254, true)], jt := [(484, 21247)], jsize := 1403 }

def A2 : Spec :=
  { regs := [(1, .addr ⟨some 0, -16⟩), (5, .var 1), (7, .const 0)]
    cells := [(⟨some 0, -12⟩, 4, .var 5), (⟨some 0, -8⟩, 8, .const 970), (⟨some 0, 48⟩, 8, .var 2),
      (⟨some 0, 40⟩, 8, .var 3), (⟨some 0, 32⟩, 8, .var 4)] }

def T2 : Spec :=
  { regs := [(0, .var 2), (1, .addr ⟨some 0, 56⟩), (5, .var 3), (6, .var 4)]
    cells := [(⟨some 1, 0⟩, 8, .const 9223372036854775810), (⟨some 1, 8⟩, 4, .var 5)] }

def F2 : List (Aff × Nat) := [(⟨some 1, 0⟩, 12)]

theorem ok2 : check st2 G2 A2 T2 F2 3780 21282 14 = true := by decide +kernel

/-- The statement of `Services.Bootstrap.Decode.Fixed.z2`, by the executor (14 steps) and one
    return through the jump table. -/
theorem z2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 v : Nat) (hA : 65536 + 16 ≤ A ∧ A + 56 < 4294967296) (hO : O + 12 ≤ 4294967296)
    (hOA : O + 12 ≤ A - 12 ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat (A - 16)) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sv : μ.readN (A - 12) 4 = Num.encodeLE 4 v) (sr : μ.readN (A - 8) 8 = Num.encodeLE 8 970)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 12 → μ.writable a = true)
    (hr : ∀ a, A - 16 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 3780 ω μ x t ω' μ' x 17 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775810 ∧ μ'.readN (O + 8) 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 12 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω', μ', hrun, ⟨r0, r1, r5, r6, -⟩, ⟨c0, c1, -⟩, hfr, hpg⟩ :=
    check_sound (R := R) ok2 ⟨d_21255 (p := p) (P := P), ⟨d_3789 (p := p) (P := P), ⟨d_3783 (p := p) (P := P), ⟨d_3780 (p := p) (P := P), trivial, trivial⟩, ⟨d_3786 (p := p) (P := P), trivial, trivial⟩⟩, ⟨d_21250 (p := p) (P := P), ⟨d_21247 (p := p) (P := P), trivial, trivial⟩, ⟨d_21254 (p := p) (P := P), trivial, trivial⟩⟩⟩, ⟨d_21273 (p := p) (P := P), ⟨d_21268 (p := p) (P := P), ⟨d_21258 (p := p) (P := P), trivial, trivial⟩, ⟨d_21270 (p := p) (P := P), trivial, trivial⟩⟩, ⟨d_21279 (p := p) (P := P), ⟨d_21276 (p := p) (P := P), trivial, trivial⟩, trivial⟩⟩⟩
      ⟨bs_20629 (p := p) (P := P), bs_21247 (p := p) (P := P), bs_21254 (p := p) (P := P), trivial⟩
      ⟨jte_484 (p := p) (P := P), trivial⟩ (jts (p := p) (P := P))
      [A, O, ret, v5, v6, v] ⟨by omega, by omega, by omega, hv5, hv6, hv, trivial⟩
      ⟨hA.1, Nat.zero_le _, hret.1, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, trivial⟩ ω μ
      ⟨fun t ht => by simp only [InReg, Aff.eval] at ht; exact hr t (by simp at ht; omega) (by simp at ht; omega), trivial⟩
      ⟨fun t ht => by simp only [InReg, Aff.eval] at ht; exact hw t (by simp at ht; omega) (by simp at ht; omega), trivial⟩
      ⟨fun t h1 h2 => by simp only [InReg, Aff.eval] at h1 h2; simp at h1 h2; omega, trivial⟩
      ⟨by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + -16).toNat = A - 16 by omega]; exact h1, h5, h7, trivial⟩
      ⟨by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + -12).toNat = A - 12 by omega]; exact sv,
       by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + -8).toNat = A - 8 by omega]; exact sr,
       by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + 48).toNat = A + 48 by omega]; exact s0,
       by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + 40).toNat = A + 40 by omega]; exact s5,
       by simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ]; rw [show ((A : Int) + 32).toNat = A + 32 by omega]; exact s6, trivial⟩ x
  simp only [SVal.eval, Aff.eval, List.getD_cons_zero, List.getD_cons_succ] at r0 r1 r5 r6 c0 c1
  have hlast := ret_step (R := R) (μ := μ') (x := x) (d_21282 (p := p) (P := P)) r0 hret.1
    (by rw [jts (p := p) (P := P)]; omega) hret.2.2 (by omega) hjt hbt
  refine ⟨ω', μ', (hrun.trans hlast).mono (by omega), r0, ?_, r5, r6, ?_, ?_, ?_, fun a => ?_, fun a => ?_⟩
  · rw [show A + 56 = ((A : Int) + 56).toNat by omega]; exact r1
  · simpa using c0
  · rw [show O + 8 = ((O : Int) + 8).toNat by omega]; exact c1
  · intro a ha hout
    refine hfr a ha fun f hf hin => ?_
    simp only [F2, List.mem_singleton] at hf; subst hf
    simp only [InReg, Aff.eval, List.getD_cons_zero, List.getD_cons_succ] at hin
    omega
  · exact readable_pages hpg a
  · exact writable_pages hpg a

end PVM.SymExec.FixedZ
