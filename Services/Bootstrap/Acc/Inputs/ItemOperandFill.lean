import Services.Bootstrap.Acc.Inputs.ItemOperand

/-!
# `AccumulateItem::decode` (45126), the operand arm: the slot

47158 … 47332 fill the 184-octet operand slot at out from the frame b and the auth trace (the
`Vec<u8>` at b + 272: capacity, pointer, length): + 0 the trace's capacity, + 8 its pointer, + 16 its
length, + 24 … + 48 the work result (b + 8, b + 16, b), + 48 p, + 80 e, + 112 a, + 144 y (from
b + 32, + 64, + 96, + 136), + 176 the gas g; then restore ω₀, ω₅, ω₆ and pop the frame.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}


/-- **47158 … 47231**, the trace decoded (capacity tc ≠ −1 at b + 272): the work result's pointer word (b + 16) and length (b) to out + 32, + 40, p (b + 32 … b + 64) to out + 48 … + 80; e's words (b + 64 … b + 88) loaded and two of them stored. -/
theorem op_fill1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out g : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat g) (m24 : rdN μ (b + 24) 8 = out)
    (htc : rdN μ (b + 272) 8 ≠ 18446744073709551615) (hg : g < 18446744073709551616)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : 65536 ≤ out ∧ out + 184 < 4294967296)
    (dbo : out + 184 ≤ b ∨ b + 424 ≤ out)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47158 ω μ x 47234 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat b ∧
      ω'[2] = UInt64.ofNat (rdN μ (b + 288) 8) ∧
      ω'[3] = UInt64.ofNat (rdN μ (b + 280) 8) ∧
      ω'[4] = UInt64.ofNat g ∧
      ω'[5] = UInt64.ofNat out ∧
      ω'[7] = UInt64.ofNat (rdN μ (b + 272) 8) ∧
      ω'[8] = UInt64.ofNat (rdN μ (b + 88) 8) ∧
      ω'[9] = UInt64.ofNat (rdN μ (b + 80) 8) ∧
      rdN μ' (out + 32) 8 = rdN μ (b + 16) 8 ∧
      rdN μ' (out + 40) 8 = rdN μ (b + 0) 8 ∧
      rdN μ' (out + 48) 8 = rdN μ (b + 32) 8 ∧
      rdN μ' (out + 56) 8 = rdN μ (b + 40) 8 ∧
      rdN μ' (out + 64) 8 = rdN μ (b + 48) 8 ∧
      rdN μ' (out + 72) 8 = rdN μ (b + 56) 8 ∧
      rdN μ' (out + 80) 8 = rdN μ (b + 64) 8 ∧
      rdN μ' (out + 88) 8 = rdN μ (b + 72) 8 ∧
      (∀ a, a < 4294967296 → (a < out + 32 ∨ out + 96 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 184 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have htc' : rdN μ (b + 272) 8 % 18446744073709551616 ≠ 18446744073709551615 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)]; exact htc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, m24, htc', hrf, hro, hwo, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, m24, htc']
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | exact rd_mod64 _ _
      | (congr 1; omega)
      | exact UInt64.ofNat_toNat
      | rfl

/-- **47234 … 47290**: e's last words, a (b + 96 … b + 128) and y (b + 136 … b + 168, three words) to out + 96 … + 160, and the trace's capacity tc to out + 0. -/
theorem op_fill2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out tc w80 w88 : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat out)
    (h7 : ω[7] = UInt64.ofNat tc) (h8 : ω[8] = UInt64.ofNat w88) (h9 : ω[9] = UInt64.ofNat w80)
    (htc : tc < 18446744073709551616) (hw80 : w80 < 18446744073709551616) (hw88 : w88 < 18446744073709551616)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : 65536 ≤ out ∧ out + 184 < 4294967296)
    (dbo : out + 184 ≤ b ∨ b + 424 ≤ out)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47234 ω μ x 47292 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat b ∧
      ω'[2] = ω[2] ∧
      ω'[3] = ω[3] ∧
      ω'[4] = ω[4] ∧
      ω'[5] = UInt64.ofNat out ∧
      ω'[9] = UInt64.ofNat (rdN μ (b + 160) 8) ∧
      ω'[11] = UInt64.ofNat (rdN μ (b + 152) 8) ∧
      rdN μ' (out + 96) 8 = w80 ∧
      rdN μ' (out + 104) 8 = w88 ∧
      rdN μ' (out + 112) 8 = rdN μ (b + 96) 8 ∧
      rdN μ' (out + 120) 8 = rdN μ (b + 104) 8 ∧
      rdN μ' (out + 128) 8 = rdN μ (b + 112) 8 ∧
      rdN μ' (out + 136) 8 = rdN μ (b + 120) 8 ∧
      rdN μ' (out + 144) 8 = rdN μ (b + 136) 8 ∧
      rdN μ' (out + 152) 8 = rdN μ (b + 144) 8 ∧
      rdN μ' out 8 = tc ∧
      (∀ a, a < 4294967296 → (a < out + 0 ∨ out + 8 ≤ a) → (a < out + 96 ∨ out + 160 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 184 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, h8, h9, hrf, hro, hwo, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h7, h8, h9]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | exact rd_mod64 _ _
      | (congr 1; omega)
      | exact UInt64.ofNat_toNat
      | rfl

/-- **47292 … 47328**: the trace's pointer and length (ω₃, ω₂) to out + 8, + 16, the result's capacity word (b + 8) to out + 24, y's last words (ω₁₁, ω₉) to out + 160, + 168 and the gas (ω₄) to out + 176; ω₀, ω₅, ω₆ restored from b + 416, + 408, + 400 and the frame popped, at the return's `jumpInd`. -/
theorem op_fill3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out tp tl g w152 w160 : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat out)
    (h2 : ω[2] = UInt64.ofNat tl) (h3 : ω[3] = UInt64.ofNat tp) (h4 : ω[4] = UInt64.ofNat g)
    (h9 : ω[9] = UInt64.ofNat w160) (h11 : ω[11] = UInt64.ofNat w152)
    (htp : tp < 18446744073709551616) (htl : tl < 18446744073709551616) (hg : g < 18446744073709551616)
    (hw152 : w152 < 18446744073709551616) (hw160 : w160 < 18446744073709551616)
    (hb : 65536 ≤ b ∧ b + 424 < 4294967296) (hout : 65536 ≤ out ∧ out + 184 < 4294967296)
    (dbo : out + 184 ≤ b ∨ b + 424 ≤ out)
    (hrf : ∀ a, b ≤ a → a < b + 424 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 184 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47292 ω μ x 47332 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat (rdN μ (b + 416) 8) ∧
      ω'[1] = UInt64.ofNat (b + 424) ∧
      ω'[5] = UInt64.ofNat (rdN μ (b + 408) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (b + 400) 8) ∧
      rdN μ' (out + 8) 8 = tp ∧
      rdN μ' (out + 16) 8 = tl ∧
      rdN μ' (out + 24) 8 = rdN μ (b + 8) 8 ∧
      rdN μ' (out + 160) 8 = w152 ∧
      rdN μ' (out + 168) 8 = w160 ∧
      rdN μ' (out + 176) 8 = g ∧
      (∀ a, a < 4294967296 → (a < out + 8 ∨ out + 32 ≤ a) → (a < out + 160 ∨ out + 184 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 184 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h2, h3, h4, h9, h11, hrf, hro, hwo, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h2, h3, h4, h9, h11]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | exact rd_mod64 _ _
      | (congr 1; omega)
      | exact UInt64.ofNat_toNat
      | rfl

end Services.Bootstrap.Acc
