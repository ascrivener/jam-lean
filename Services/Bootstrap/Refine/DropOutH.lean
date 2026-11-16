import Services.Bootstrap.Refine.DropOut
import Services.Bootstrap.CodeT1BAll

/-!
# Refine's exit: the drop arms of `DeleteItems` and `Imported`

`drop_in_place::<[Instruction]>` (29087, `DropOut`) dispatches each output element through the table at 67760. The
variants holding a `Vec<Vec<u8>>` at the element's words 1 … 3 (`{cap, ptr, len}`), `DeleteItems` (index 5, arm 29270)
and `Imported` (index 19, arm 29476), free each item's buffer with a nonzero capacity (`dealloc(ptr, cap, 1)`), then
the outer buffer (`dealloc(ptr, 24·cap, 8)`), and go on to the next element (29181). The pieces here are those arms,
straight-line; `VK` names the two arms' addresses. The code facts are tier T1B (`docs/code-fact-tiers.md`).
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.DropOutH

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeR Services.Bootstrap.CodeT1B
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.DropOut

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The two arms: dispatch index t, the arm's address, its item loop's head, the step to the next item, the
    landing after an item's `dealloc` and that call's return address. -/
def VK (t arm head nxt back ret : Nat) : Prop :=
  (t = 5 ∧ arm = 29270 ∧ head = 29318 ∧ nxt = 29307 ∧ back = 29336 ∧ ret = 1362) ∨
  (t = 19 ∧ arm = 29476 ∧ head = 29522 ∧ nxt = 29512 ∧ back = 29540 ∧ ret = 1374)

/-- 29188 … arm: element k at E + 232 k (kept at F + 48) of index 5 or 19 dispatches through the table at 67760
    (entry 1360 or 1372 of the jump table) to its arm. -/
theorem ddV {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F E k t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0)
    (hEk : E + 232 * k + 8 ≤ 4294967296) (hEF : E + 232 * k + 8 ≤ F ∨ F + 80 ≤ E + 232 * k)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 8 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 29188 ω μ x arm ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ μ'.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hk : k < 18446744073709551616 := by omega
  have rE := rd8 (by omega) s40
  have r32 := rd8 (by decide) s32
  have r24 := rd8 (by decide) s24
  have r16 := rd8 (by decide) s16
  have rD0 := rd8 (by omega) hD
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 5 := by
      rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
    have rt : rdN μ 67780 4 = 4294900896 := by
      show Num.decodeLE (μ.readN _ 4) = _
      rw [show (67780 : Nat) = 67760 + 4 * 5 from rfl, dtable_entry tab 5 (by decide)]; rfl
    have hrt' : ∀ a, 67780 ≤ a → a < 67784 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
    have sx : sxw 4 4294900896 = 18446744069414584320 + 4294900896 := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
        rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
      post_simp
  · have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 19 := by
      rw [show k * 232 + E = E + 232 * k by omega]; exact rD0
    have rt : rdN μ 67836 4 = 4294900908 := by
      show Num.decodeLE (μ.readN _ 4) = _
      rw [show (67836 : Nat) = 67760 + 4 * 19 from rfl, dtable_entry tab 19 (by decide)]; rfl
    have hrt' : ∀ a, 67836 ≤ a → a < 67840 → μ.readable a = true := fun a h1 h2 => hrt a (by omega) (by omega)
    have sx : sxw 4 4294900908 = 18446744069414584320 + 4294900908 := by decide
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h6, hF0, hF1, hF8, hEk, hEF, hw, hr, hrE, hrE', rE, r32, r24, r16, rD, rt, hrt', sx, e1,
        rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mul_comm k 232]
      post_simp

/-- arm … head: the element `el` (at F + 48) has len ≠ 0 items (its word 3) at ptr (word 2): the end
    ptr + 8 + 24·len goes to F + 8 and the item loop starts at head with ω₅ = ptr + 8 (the first item's buffer
    word). Memory changes only at F + 8 … F + 16. -/
theorem va {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el ptr len t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : 67856 ≤ F ∧ F + 80 ≤ 4294967296 ∧ F % 8 = 0) (hel : el + 32 ≤ 4294967296)
    (hlen : len ≠ 0) (hp : ptr + 8 + 24 * len < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr) (s24 : μ.readN (el + 24) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, el + 16 ≤ a → a < el + 32 → μ.readable a = true)
    (hw : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R arm ω μ x head ω' μ' x 12 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (ptr + 8) ∧
      ω'[6] = ω[6] ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (ptr + 8 + 24 * len) ∧
      (∀ a, a < 4294967296 → (a < F + 8 ∨ F + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have re := rd8 (by omega) s48
  have rp := rd8 (by omega) s16
  have rl := rd8 (by omega) s24
  have hl0 : ¬ len = 0 := hlen
  have hr2 : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, hF0, hF1, hF8, hel, hl0, hp, hr, hr2, hw, re, rp, rl, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]
      post_simp

/-- arm … 29542: no items (len = 0). -/
theorem va0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hel : el + 32 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s24 : μ.readN (el + 24) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, el + 24 ≤ a → a < el + 32 → μ.readable a = true)
    (hr2 : ∀ a, F + 48 ≤ a → a < F + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R arm ω μ x 29542 ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rl := rd8 (by decide) s24
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hF, hel, hr, hr2, re, rl, ↓rdN_fold]
    · refine ⟨?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- head … (head or 29542): the item at g (ω₅ = g + 8) has capacity 0: on to the next item, g + 24 (back to head
    while g + 32 ≠ the end at F + 8, else 29542). -/
theorem vi0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F g en t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hg : g + 32 ≤ 4294967296) (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat (g + 8))
    (s0 : μ.readN g 8 = Num.encodeLE 8 0) (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 en)
    (hr : ∀ a, g ≤ a → a < g + 8 → μ.readable a = true)
    (hr2 : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R head ω μ x (if g + 32 = en then 29542 else head) ω' μ x 6 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (g + 32) ∧ ω'[6] = ω[6] := by
  have rc := rd8 (by decide) s0
  have re := rd8 hen s8
  have hrg : ∀ a, g + 8 - 8 ≤ a → a < g + 8 - 8 + 8 → μ.readable a = true := fun a h1 h2 => hr a (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · by_cases he : g + 32 = en
    · rw [if_pos he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hg, hen, he, hr, hrg, hr2, rc, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    · rw [if_neg he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hg, hen, he, hr, hrg, hr2, rc, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]

/-- head … 40613: the item at g (ω₅ = g + 8) has capacity c ≠ 0: `dealloc(q, c, 1)` with q its buffer (word 1),
    return address `ret` (→ back). -/
theorem vi1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (g c q t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hg : g + 16 ≤ 4294967296) (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hq : q < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat (g + 8))
    (s0 : μ.readN g 8 = Num.encodeLE 8 c) (s8 : μ.readN (g + 8) 8 = Num.encodeLE 8 q)
    (hr : ∀ a, g ≤ a → a < g + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R head ω μ x 40613 ω' μ x 5 ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat c := by
  have rc := rd8 hc1 s0
  have rq := rd8 hq s8
  have hc0 : ¬ c = 0 := hc
  have hrg : ∀ a, g + 8 - 8 ≤ a → a < g + 8 - 8 + 8 → μ.readable a = true := fun a h1 h2 => hr a (by omega) (by omega)
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, hg, hc0, hr, hrg, rc, rq, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]

/-- back … (head or 29542): after an item's `dealloc`, on to the next item, as `vi0`. -/
theorem vb {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F g en t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hg : g + 32 ≤ 4294967296) (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat (g + 8))
    (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 en)
    (hr2 : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R back ω μ x (if g + 32 = en then 29542 else head) ω' μ x 5 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (g + 32) ∧ ω'[6] = ω[6] := by
  have re := rd8 hen s8
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · by_cases he : g + 32 = en
    · rw [if_pos he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hg, hen, he, hr2, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    · rw [if_neg he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hg, hen, he, hr2, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]

/-- 29542 … 29181: the outer capacity (word 1 of `el`) is 0: ω₅ := n (from F), on to the next element. -/
theorem vo0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el n : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 32 ≤ 4294967296)
    (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s0 : μ.readN F 8 = Num.encodeLE 8 n) (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 0)
    (hr : ∀ a, el + 8 ≤ a → a < el + 16 → μ.readable a = true)
    (hr2 : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29542 ω μ x 29181 ω' μ x 5 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = ω[6] := by
  have re := rd8 (by omega) s48
  have rn := rd8 hn s0
  have rc := rd8 (by decide) s8
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hr, hr2, re, rn, rc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

/-- 29542 … 40613: the outer capacity c ≠ 0: `dealloc(ptr, 24·c, 8)` (return address 1356 → 29181), ω₅ := n. -/
theorem vo1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F el n c ptr : Nat) (hF : F + 80 ≤ 4294967296) (hel : el + 32 ≤ 4294967296)
    (hn : n < 18446744073709551616) (hc : c ≠ 0) (hc1 : 24 * c < 18446744073709551616)
    (hptr : ptr < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (s48 : μ.readN (F + 48) 8 = Num.encodeLE 8 el)
    (s0 : μ.readN F 8 = Num.encodeLE 8 n) (s8 : μ.readN (el + 8) 8 = Num.encodeLE 8 c)
    (s16 : μ.readN (el + 16) 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, el + 8 ≤ a → a < el + 24 → μ.readable a = true)
    (hr2 : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 29542 ω μ x 40613 ω' μ x 12 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat ptr := by
  have re := rd8 (by omega) s48
  have rn := rd8 hn s0
  have rc := rd8 (by omega) s8
  have rp := rd8 hptr s16
  have hc0 : ¬ c = 0 := hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hF, hel, hc0, hc1, hr, hr2, re, rn, rc, rp, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1]

end Services.Bootstrap.Refine.DropOutH
