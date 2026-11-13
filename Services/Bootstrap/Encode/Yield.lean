import Services.Bootstrap.Encode.Fixed

/-!
# `Instruction::encode_to`: `Yield`

`Yield`'s arm (18138) differs from the others in its registers: it keeps the hash's address S + 8 in ω₅
and the writer in ω₆, appends the tag octet 14 (returning to 906 → 20190), then the 32 octets at S + 8
(returning to 908 → 20204, a shared tail).
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 18138 … 18159: the octet 14 goes to sp + 24 and the arm calls `Vec<u8>::extend_from_slice` for it
    (return address 906), with S + 8 in ω₅ and the writer v in ω₆ and ω₇. -/
theorem yieldSeg1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v S : Nat) (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hS : S + 8 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S)
    (hw : ∀ a, sp + 24 ≤ a → a < sp + 25 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 18138 ω μ x 58508 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 906 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat (S + 8) ∧
      ω'[6] = UInt64.ofNat v ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧
      ω'[9] = UInt64.ofNat 1 ∧ μ'.readN (sp + 24) 1 = [UInt8.ofNat 14] ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 25 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h10, h11, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h10, h11, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hS]
    post_simp
    all_goals try assumption

/-- 20190 … 20197: the arm calls `Vec<u8>::extend_from_slice` for the 32 octets at ω₅ (return address
    908), the writer from ω₆. -/
theorem yieldSeg2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (v h : Nat) (hv : v < 18446744073709551616) (hh : h < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat h) (h6 : ω[6] = UInt64.ofNat v) :
    ∃ ω', FreeStepsH p R 20190 ω μ x 58508 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 908 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat h ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h6]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5, h6, Nat.mod_eq_of_lt hv,
      Nat.mod_eq_of_lt hh]

/-- **`Yield`** (tag 14): a value holding the discriminant 2^63 + 13 and then h, the 32 octets of the
    hash, encodes to 14 :: h. -/
theorem yield {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (h : List UInt8) (hh : h.length = 32) :
    EncOk p P (14 :: h) (fun bs => bs.take 8 = Num.encodeLE 8 9223372036854775821 ∧ (bs.drop 8).take 32 = h) := by
  intro X R x ω μ F S v cap ptr len ret t' h0 h1 h7 h8 rep L tab hrt
  have hN : (14 :: h).length = 33 := by simp [hh]
  have hF := L.hF; have hF' := L.hF'; have hv := L.hv; have hS := L.hS; have hS' := L.hS'
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 14) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := R) x ω μ L 14 (by decide) h0 h1 h7 h8 hD
    tab hrt
  rw [show arm 14 = 18138 from rfl] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := yieldSeg1 (p := p) (P := P) (R := R) x
    ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => by rw [st1.wr]; exact L.hwF a (by omega) (by omega))
  have st2 := st1.scratch L (by simp) b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  obtain ⟨ω3, μ3, run3, st3, c5, c6, _⟩ := ext_step (p := p) (P := P) (R := R) x ω2 μ2 μ L st2 (F - 32) 1 906 20190
    b0 b7 (by rw [b8]; congr 1; omega) b9 ⟨by decide, by decide, by decide⟩ jte_452 bs_20190
    (by simp [hh]) (Or.inl ⟨rfl, by decide⟩)
  rw [show F - 32 = F - 56 + 24 by omega, bt] at st3
  obtain ⟨ω4, run4, d0, d1, _, _, d7, d8, d9⟩ := yieldSeg2 (p := p) (P := P) (R := R) x ω3 μ3 v (S + 8)
    (by omega) (by omega) (c5.trans b5) (c6.trans b6)
  obtain ⟨ω5, μ5, run5, st5, _, _, _⟩ := ext_step (p := p) (P := P) (R := R) x ω4 μ3 μ L
    ⟨d1.trans st3.h1, st3.s0, st3.s5, st3.s6, st3.vl, st3.out, st3.keep, st3.rd, st3.wr⟩ (S + 8) 32 908 20204
    d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_453 bs_20204 (by simp [hh]) (Or.inr ⟨by omega, by omega⟩)
  rw [st3.slot L (by simp [hh]) 8 32 (by decide), c0] at st5
  exact close L 20204 _ (by decide) (by simp [hh]) (run1.trans (run2.trans (run3.trans (run4.trans run5))))
    (St.cast (by simp only [List.nil_append, List.singleton_append, List.cons_append]; rfl) st5)

end Services.Bootstrap.Encode.Enc
