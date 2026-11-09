import Services.Bootstrap.Code
import PVM.Logic.Go

/-!
# The compiler's `memset`, zeroing an aligned buffer

`memset` (70133) fills n octets at D (ω₇) with the octet c (ω₈) and returns to ω₀. It writes the
octets before the first 8-aligned address one by one, then whole words of c repeated, then the tail
octets. This file proves the case `Instruction::decode` needs (`Transfer`'s 128-octet memo buffer):
c = 0, D 8-aligned, n a multiple of 8 and at least 16, so only the word loop runs (`memzero`).
-/

namespace Services.Bootstrap.Memzero

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- 70133 … 70198: n ≥ 16, D 8-aligned, c = 0: no leading octets, the word loop's end D + n in ω₁₀,
    its cursor D in ω₁₁ and the zero word in ω₁₂. -/
theorem pre {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (D n : Nat)
    (hD : D % 8 = 0) (hn : 16 ≤ n ∧ n % 8 = 0) (hDn : D + n ≤ 4294967296)
    (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat 0) (h9 : ω[9] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 70133 ω μ x 70199 ω' μ x 15 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[9] = UInt64.ofNat n ∧
      ω'[10] = UInt64.ofNat (D + n) ∧ ω'[11] = UInt64.ofNat D ∧ ω'[12] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, h9, hD, hn, hDn, bitwise_and_m7, bitwise_and_not7]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp

/-- 70199 … 70204: one pass of the word loop: a zero word at Q, the cursor to Q + 8, and the loop
    again while Q + 8 < E, else on to 70207. -/
theorem iter {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (Q E : Nat)
    (hQ : Q + 8 ≤ E) (hE : E ≤ 4294967296)
    (h10 : ω[10] = UInt64.ofNat E) (h11 : ω[11] = UInt64.ofNat Q) (h12 : ω[12] = UInt64.ofNat 0)
    (hw : ∀ a, Q ≤ a → a < Q + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 70199 ω μ x (if Q + 8 < E then 70199 else 70207) ω'
      (μ.writeN Q (Num.encodeLE 8 0)) x 3 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[9] = ω[9] ∧
      ω'[10] = ω[10] ∧ ω'[11] = UInt64.ofNat (Q + 8) ∧ ω'[12] = ω[12] := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hm : Q + 8 < E
  · rw [if_pos hm]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · apply FreeStepsH.step_decode (d_70199 (p := p) (P := P))
      · pvm_simp [h10, h11, h12, hQ, hE, hw, hm]
      pvm_go [h10, h11, h12, hQ, hE, hw, hm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      post_simp
  · rw [if_neg hm]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h10, h11, h12, hQ, hE, hw, hm]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      post_simp

/-- n + m octets are the first n, then the m after them. -/
theorem readN_add' (μ : Memory) (a n m : Nat) : μ.readN a (n + m) = μ.readN a n ++ μ.readN (a + n) m := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.add_assoc]

/-- **The word loop**, from Q with r ≥ 1 words to go to E = Q + 8r: zeros at Q … E, then 70207. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) (E : Nat) (hE : E ≤ 4294967296) :
    ∀ r Q (ω : Regs) (μ : Memory), Q + 8 * r = E → 1 ≤ r →
      ω[10] = UInt64.ofNat E → ω[11] = UInt64.ofNat Q → ω[12] = UInt64.ofNat 0 →
      (∀ a, Q ≤ a → a < E → μ.writable a = true) →
      ∃ ω' μ', FreeStepsH p R 70199 ω μ x 70207 ω' μ' x (3 * r) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[9] = ω[9] ∧
        ω'[10] = ω[10] ∧ ω'[11] = UInt64.ofNat E ∧
        μ'.readN Q (8 * r) = List.replicate (8 * r) 0 ∧
        (∀ a, a < 4294967296 → (a < Q ∨ E ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro r
  induction r with
  | zero => intro Q ω μ _ h; omega
  | succ r ih =>
    intro Q ω μ hQE _ h10 h11 h12 hw
    obtain ⟨ω1, run1, a0, a1, a5, a6, a9, a10, a11, a12⟩ := iter (p := p) (P := P) (R := R) x ω μ Q E
      (by omega) hE h10 h11 h12 (fun a h1 h2 => hw a h1 (by omega))
    have z8 : (μ.writeN Q (Num.encodeLE 8 0)).readN Q 8 = List.replicate 8 0 :=
      (Memory.readN_writeN_same _ _ _ _ (by rfl) (by simp only [two32]; omega)).trans (by rfl)
    by_cases hm : Q + 8 < E
    · rw [if_pos hm] at run1
      obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b9, b10, b11, bz, bfr, brd, bwr⟩ := ih (Q + 8) ω1
        (μ.writeN Q (Num.encodeLE 8 0)) (by omega) (by omega) (a10.trans h10) a11 (a12.trans h12)
        (fun a h1 h2 => by rw [Memory.writable_writeN]; exact hw a (by omega) h2)
      refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b0.trans a0, b1.trans a1, b5.trans a5, b6.trans a6,
        b9.trans a9, b10.trans a10, b11, ?_, ?_, fun a => by rw [brd, Memory.readable_writeN],
        fun a => by rw [bwr, Memory.writable_writeN]⟩
      · rw [show 8 * (r + 1) = 8 + 8 * r by omega, readN_add', bz, ← List.replicate_append_replicate,
          Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega)), z8]
      · intro a h0 h1
        rw [bfr a h0 (by omega), Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega)
          (by simp [two32]; omega)]
    · rw [if_neg hm] at run1
      have hr0 : r = 0 := by omega
      subst hr0
      refine ⟨ω1, μ.writeN Q (Num.encodeLE 8 0), run1.mono (by omega), a0, a1, a5, a6, a9, a10,
        by rw [a11, show Q + 8 = E by omega], z8, ?_, fun a => by rw [Memory.readable_writeN],
        fun a => by rw [Memory.writable_writeN]⟩
      intro a h0 h1
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]

/-- 70207 … 70227: no tail octets (n a multiple of 8, the cursor at the end): return to ω₀. -/
theorem post {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (n E ret t : Nat)
    (hn : n % 8 = 0) (hn64 : n < 18446744073709551616) (hE : E < 18446744073709551616)
    (h9 : ω[9] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat E) (h0 : ω[0] = UInt64.ofNat ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true) :
    ∃ ω', FreeStepsH p R 70207 ω μ x t ω' μ x 4 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h9, h11, h0, hn, hn64, hE, hret, hjt, hbt, bitwise_and_m7]
  · refine ⟨?_, ?_, ?_, ?_⟩
    post_simp

/-- **`memset` to zero, aligned** (70133): called with return address `ret` (ω₀), D (ω₇) 8-aligned,
    the octet 0 (ω₈) and n (ω₉) a multiple of 8 and at least 16, it zeroes D … D + n and returns,
    changing no other memory and keeping ω₀, ω₁, ω₅, ω₆. -/
theorem memzero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (D n ret t : Nat) (hD : D % 8 = 0) (hn : 16 ≤ n ∧ n % 8 = 0) (hDn : D + n ≤ 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat 0)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, D ≤ a → a < D + n → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 70133 ω μ x t ω' μ' x (3 * n + 20) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN D n = List.replicate n 0 ∧
      (∀ a, a < 4294967296 → (a < D ∨ D + n ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, run1, a0, a1, a5, a6, a9, a10, a11, a12⟩ := pre (p := p) (P := P) (R := R) x ω μ D n hD hn hDn h7 h8 h9
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b9, b10, b11, bz, bfr, brd, bwr⟩ := loop (p := p) (P := P) (R := R) x
    (D + n) hDn (n / 8) D ω1 μ (by omega) (by omega) a10 a11 a12 hw
  obtain ⟨ω3, run3, c0, c1, c5, c6⟩ := post (p := p) (P := P) (R := R) x ω2 μ2 n (D + n) ret t hn.2 (by omega)
    (by omega) (b9.trans a9) b11 (b0.trans (a0.trans h0)) hret hjt hbt
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), c0.trans (b0.trans a0),
    c1.trans (b1.trans a1), c5.trans (b5.trans a5), c6.trans (b6.trans a6), ?_, bfr, brd, bwr⟩
  rw [show n = 8 * (n / 8) by omega]; exact bz

end Services.Bootstrap.Memzero
