import Services.Bootstrap.Refine.DropOut
import Services.Bootstrap.CodeT1BAll
import Services.Bootstrap.CodeX
import Services.Bootstrap.CodeRAll
import Services.Bootstrap.Decode.DeallocCall

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

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.DropOut Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Picoalloc

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
  have hrE' : ∀ a, k * 232 + E ≤ a → a < k * 232 + E + 8 → μ.readable a = true :=
    fun a h1 h2 => hrE a (by omega) (by omega)
  have hr : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have e1 : (E + 232 * k) % 18446744073709551616 = E + 232 * k := Nat.mod_eq_of_lt (by omega)
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have rD0 := rd8 (by decide) hD
    have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 5 := by
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
  · have rD0 := rd8 (by decide) hD
    have rD : rdN μ (k * 232 + E) 8 = 9223372036854775807 + 19 := by
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
    ∃ ω' μ', FreeStepsH p R arm ω μ x head ω' μ' x 13 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (ptr + 8) ∧
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

/-- head … nxt: the item whose buffer word is at w (ω₅ = w; its capacity at w − 8) has capacity 0. -/
theorem vz {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (w t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hw : 8 ≤ w ∧ w + 24 ≤ 4294967296) (h5 : ω[5] = UInt64.ofNat w)
    (s0 : μ.readN (w - 8) 8 = Num.encodeLE 8 0) (hr : ∀ a, w - 8 ≤ a → a < w → μ.readable a = true) :
    ∃ ω', FreeStepsH p R head ω μ x nxt ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rc := rd8 (by decide) s0
  have rc2 : rdN μ (w + 18446744073709551608) 8 = 0 := by
    have hrd : μ.readN (w + 18446744073709551608) 8 = μ.readN (w - 8) 8 := readN_congr2 (fun j hj => by
      unfold Memory.read
      rw [show (w + 18446744073709551608 + j) % two32 = (w - 8 + j) % two32 by unfold two32; omega])
    unfold rdN; rw [hrd]; exact rc
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, hw, hr, rc2, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some']

/-- nxt … (head or 29542): on to the next item, w + 24 (back to head while w + 24 ≠ the end en at F + 8). -/
theorem vn {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F w en t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hw : w + 24 ≤ 4294967296) (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat w)
    (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 en)
    (hr2 : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R nxt ω μ x (if w + 24 = en then 29542 else head) ω' μ x 4 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (w + 24) ∧ ω'[6] = ω[6] := by
  have re := rd8 hen s8
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · by_cases he : w + 24 = en
    · rw [if_pos he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hw, hen, he, hr2, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, he]
    · rw [if_neg he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hw, hen, he, hr2, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]

/-- head … (head or 29542): an item of capacity 0 (`vz`), then on to the next (`vn`). -/
theorem vi0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F w en t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hw : 8 ≤ w ∧ w + 24 ≤ 4294967296) (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat w)
    (s0 : μ.readN (w - 8) 8 = Num.encodeLE 8 0) (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 en)
    (hr : ∀ a, w - 8 ≤ a → a < w → μ.readable a = true)
    (hr2 : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R head ω μ x (if w + 24 = en then 29542 else head) ω' μ x 7 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (w + 24) ∧ ω'[6] = ω[6] := by
  obtain ⟨ω1, r1, a1, a5, a6⟩ := vz (p := p) (P := P) (R := R) x ω μ w t arm head nxt back ret hv hw h5 s0 hr
  obtain ⟨ω2, r2, b1, b5, b6⟩ := vn (p := p) (P := P) (R := R) x ω1 μ F w en t arm head nxt back ret hv hF hw.2 hen
    (a1.trans h1) (a5.trans h5) s8 hr2
  exact ⟨ω2, r1.trans r2, b1.trans a1, b5, b6.trans a6⟩

/-- head … 40613: the item at w (ω₅ = w) has capacity c ≠ 0 (at w − 8): `dealloc(q, c, 1)` with q its buffer (at w),
    return address `ret` (→ back). -/
theorem vi1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (w c q t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hw : 8 ≤ w ∧ w + 8 ≤ 4294967296) (hc : c ≠ 0) (hc1 : c < 18446744073709551616) (hq : q < 18446744073709551616)
    (h5 : ω[5] = UInt64.ofNat w)
    (s0 : μ.readN (w - 8) 8 = Num.encodeLE 8 c) (s8 : μ.readN w 8 = Num.encodeLE 8 q)
    (hr : ∀ a, w - 8 ≤ a → a < w + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R head ω μ x 40613 ω' μ x 6 ∧ ω'[0] = UInt64.ofNat ret ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat c := by
  have rc := rd8 hc1 s0
  have rq := rd8 hq s8
  have hc0 : ¬ c = 0 := hc
  have rc2 : rdN μ (w + 18446744073709551608) 8 = c := by
    have hrd : μ.readN (w + 18446744073709551608) 8 = μ.readN (w - 8) 8 := readN_congr2 (fun j hj => by
      unfold Memory.read
      rw [show (w + 18446744073709551608 + j) % two32 = (w - 8 + j) % two32 by unfold two32; omega])
    unfold rdN; rw [hrd]; exact rc
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h5, hw, hc0, hr, rc2, rq, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h5]

/-- back … (head or 29542): after an item's `dealloc`, on to the next item, as `vi0`. -/
theorem vb {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P] (x : X)
    (ω : Regs) (μ : Memory) (F w en t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (hF : F + 80 ≤ 4294967296) (hw : w + 24 ≤ 4294967296) (hen : en < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat w)
    (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 en)
    (hr2 : ∀ a, F + 8 ≤ a → a < F + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R back ω μ x (if w + 24 = en then 29542 else head) ω' μ x 5 ∧ ω'[1] = ω[1] ∧
      ω'[5] = UInt64.ofNat (w + 24) ∧ ω'[6] = ω[6] := by
  have re := rd8 hen s8
  rw [show ω = regsNF ω [] from rfl]
  rcases hv with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
  · by_cases he : w + 24 = en
    · rw [if_pos he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hw, hen, he, hr2, re, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_⟩
        all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
          ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, he]
    · rw [if_neg he]
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · pvm_go [h1, h5, hF, hw, hen, he, hr2, re, ↓rdN_fold]
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
    ∃ ω', FreeStepsH p R 29542 ω μ x 40613 ω' μ x 14 ∧ ω'[0] = UInt64.ofNat 1356 ∧ ω'[1] = ω[1] ∧
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

/-- The jump-table facts of an item's `dealloc` return. -/
theorem VK.ret_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    {t arm head nxt back ret : Nat} (hv : VK t arm head nxt back ret) :
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) ∧ P.jumpTable.getD (ret / 2 - 1) 0 = back ∧ P.isBlockStart back = true := by
  rcases hv with ⟨-, -, -, -, rfl, rfl⟩ | ⟨-, -, -, -, rfl, rfl⟩
  · exact ⟨by decide, by simp only [Nat.reduceDiv, Nat.reduceSub, jte_680], bs_29336⟩
  · exact ⟨by decide, by simp only [Nat.reduceDiv, Nat.reduceSub, jte_686], bs_29540⟩

/-- **The item loop** (head … 29542): from item j of len (its words {c i, q i} at ptr + 24 i, ω₅ = ptr + 8 + 24 j, the
    end at F + 8), every item i ≥ j with c i ≠ 0 has its buffer, the allocated chunk `cs i` (distinct), freed; the
    words lie in the data of an allocated chunk `co` that is none of them. The heap context holds for the state
    after the frees; every other allocated chunk stays, with its data; the stack from F up is kept. -/
theorem items_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (F ptr len t arm head nxt back ret : Nat)
    (hv : VK t arm head nxt back ret) (c q : Nat → Nat) (cs : Nat → Chunk) (co : Chunk)
    (hF : 2147483716 ≤ F ∧ S0 + 40 ≤ F ∧ F + 80 ≤ S1) (hptr : ptr + 24 * len + 8 ≤ 2147483648)
    (hc : ∀ i, i < len → c i < 18446744073709551616) (hq : ∀ i, i < len → q i < 18446744073709551616)
    (hca : ∀ i, i < len → c i ≠ 0 → (cs i).addr + 32 = q i)
    (hdist : ∀ i i', i < len → i' < len → i ≠ i' → c i ≠ 0 → c i' ≠ 0 → cs i ≠ cs i')
    (hco : ∀ i, i < len → c i ≠ 0 → cs i ≠ co) (hcoD : ∀ a, ptr ≤ a → a < ptr + 24 * len → InData co a) :
    ∀ m j (ω : Regs) (μ : Memory) (s : State), j + m = len → j < len →
      ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (ptr + 8 + 24 * j) → HeapCtx env pb S0 S1 μ s →
      μ.readN (F + 8) 8 = Num.encodeLE 8 (ptr + 8 + 24 * len) →
      co ∈ chunks s → co.used = true →
      (∀ i, j ≤ i → i < len → μ.readN (ptr + 24 * i) 8 = Num.encodeLE 8 (c i) ∧
        μ.readN (ptr + 24 * i + 8) 8 = Num.encodeLE 8 (q i)) →
      (∀ i, j ≤ i → i < len → c i ≠ 0 → cs i ∈ chunks s ∧ (cs i).used = true) →
      ∃ ω' μ' s' N, FreeStepsH p R head ω μ x 29542 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧
        HeapCtx env pb S0 S1 μ' s' ∧ (∀ a, a < 4294967296 → F ≤ a → μ'.read a = μ.read a) ∧
        (∀ d ∈ chunks s, d.used = true → (∀ i, j ≤ i → i < len → c i ≠ 0 → d ≠ cs i) →
          d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
        μ'.pages = μ.pages ∧ (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
  obtain ⟨hF0, hF1, hF2⟩ := hF
  obtain ⟨hret, hjt, hbt⟩ := hv.ret_ok (p := p) (P := P)
  intro m
  induction m with
  | zero => intro j _ _ _ hjm hj; omega
  | succ m ih =>
    intro j ω μ s hjm hj h1 h5 H s8 hcom hcou hw hcs
    have hS := H.hS1
    have rdw : ∀ a, ptr ≤ a → a < ptr + 24 * len → μ.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (Decode.VecU8.heap_writable H hcom hcou (hcoD a h1 h2))
    have rdF : ∀ a, F ≤ a → a < F + 80 → μ.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (H.st a (by omega) (by omega))
    obtain ⟨wc, wq⟩ := hw j (Nat.le_refl _) hj
    -- after item j, either on to item j + 1 at head, or (j + 1 = len) at 29542
    have tail : ∀ (ω1 : Regs) (μ1 : Memory) (s1 : State) (N1 : Nat),
        FreeStepsH p R head ω μ x (if ptr + 8 + 24 * j + 24 = ptr + 8 + 24 * len then 29542 else head) ω1 μ1 x N1 →
        ω1[1] = ω[1] → ω1[5] = UInt64.ofNat (ptr + 8 + 24 * j + 24) → ω1[6] = ω[6] →
        HeapCtx env pb S0 S1 μ1 s1 → (∀ a, a < 4294967296 → F ≤ a → μ1.read a = μ.read a) →
        (∀ d ∈ chunks s, d.used = true → (c j ≠ 0 → d ≠ cs j) → d ∈ chunks s1 ∧
          ∀ a, InData d a → μ1.read a = μ.read a) →
        μ1.pages = μ.pages → (∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b) →
        ∃ ω' μ' s' N, FreeStepsH p R head ω μ x 29542 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧
          HeapCtx env pb S0 S1 μ' s' ∧ (∀ a, a < 4294967296 → F ≤ a → μ'.read a = μ.read a) ∧
          (∀ d ∈ chunks s, d.used = true → (∀ i, j ≤ i → i < len → c i ≠ 0 → d ≠ cs i) →
            d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
          μ'.pages = μ.pages ∧ (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
      intro ω1 μ1 s1 N1 run1 e1 e5 e6 H1 st1 kp1 pg1 ro1
      by_cases hl : j + 1 = len
      · rw [if_pos (by omega)] at run1
        exact ⟨ω1, μ1, s1, N1, run1, e1, e6, H1, st1, fun d hd hu hne => kp1 d hd hu (fun h => hne j (by omega) hj h),
          pg1, ro1⟩
      · rw [if_neg (by omega)] at run1
        have kco := kp1 co hcom hcou (fun h => (hco j hj h).symm)
        obtain ⟨ω', μ', s', N, run', f1, f6, H', st', kp', pg', ro'⟩ := ih (j + 1) ω1 μ1 s1 (by omega) (by omega)
          (e1.trans h1) (e5.trans (by rw [show ptr + 8 + 24 * j + 24 = ptr + 8 + 24 * (j + 1) by omega])) H1
          (by rw [Memory.readN_congr (fun i hi => st1 _ (by omega) (by omega))]; exact s8) kco.1 hcou
          (fun i hi1 hi2 => by
            obtain ⟨a1, a2⟩ := hw i (by omega) hi2
            refine ⟨?_, ?_⟩
            · rw [Memory.readN_congr (fun k hk => kco.2 _ (hcoD _ (by omega) (by omega)))]; exact a1
            · rw [Memory.readN_congr (fun k hk => kco.2 _ (hcoD _ (by omega) (by omega)))]; exact a2)
          (fun i hi1 hi2 hci => (kp1 (cs i) (hcs i (by omega) hi2 hci).1 (hcs i (by omega) hi2 hci).2
            (fun h => hdist i j hi2 hj (by omega) hci h)).1 |> fun h => ⟨h, (hcs i (by omega) hi2 hci).2⟩)
        refine ⟨ω', μ', s', N1 + N, run1.trans run', f1.trans e1, f6.trans e6, H',
          fun a h0 ha => by rw [st' a h0 ha, st1 a h0 ha], fun d hd hu hne => ?_, pg'.trans pg1, fun b hb hwb => ?_⟩
        rotate_left
        · have hwb1 : μ1.writable b = false := by unfold Memory.writable at hwb ⊢; rw [pg1]; exact hwb
          rw [ro' b hb hwb1, ro1 b hb hwb]
        obtain ⟨hd1, kd1⟩ := kp1 d hd hu (fun h => hne j (Nat.le_refl _) hj h)
        obtain ⟨hd', kd'⟩ := kp' d hd1 hu (fun i hi1 hi2 hci => hne i (by omega) hi2 hci)
        exact ⟨hd', fun a ha => by rw [kd' a ha, kd1 a ha]⟩
    by_cases hc0 : c j = 0
    · obtain ⟨ω1, run1, e1, e5, e6⟩ := vi0 (p := p) (P := P) (R := R) x ω μ F (ptr + 8 + 24 * j) (ptr + 8 + 24 * len)
        t arm head nxt back ret hv (by omega) ⟨by omega, by omega⟩ (by omega) h1 h5
        (by rw [show ptr + 8 + 24 * j - 8 = ptr + 24 * j by omega, wc, hc0]) s8
        (fun a h1 h2 => rdw a (by omega) (by omega)) (fun a h1 h2 => rdF a (by omega) (by omega))
      exact tail ω1 μ s 7 run1 e1 e5 e6 H (fun _ _ _ => rfl) (fun d hd _ _ => ⟨hd, fun _ _ => rfl⟩) rfl
        (fun _ _ _ => rfl)
    · obtain ⟨hcsj, hcsu⟩ := hcs j (Nat.le_refl _) hj hc0
      obtain ⟨ω1, run1, a0, a1, a5, a6, a7, -⟩ := vi1 (p := p) (P := P) (R := R) x ω μ (ptr + 8 + 24 * j) (c j) (q j)
        t arm head nxt back ret hv ⟨by omega, by omega⟩ hc0 (hc j hj) (hq j hj) h5
        (by rw [show ptr + 8 + 24 * j - 8 = ptr + 24 * j by omega]; exact wc)
        (by rw [show ptr + 8 + 24 * j = ptr + 24 * j + 8 by omega]; exact wq)
        (fun a h1 h2 => rdw a (by omega) (by omega))
      obtain ⟨ω2, μ2, run2, H2, -, pg2, ro2, stk2, -, keep2, b0, b1, b5, b6⟩ :=
        Decode.DeallocCall.dealloc_call (R := R) (p := p) (P := P) env pb S0 S1 x ω1 μ s F (q j) ret back (cs j) H hcsj
          hcsu (hca j hj hc0) a0 (a1.trans h1) a7 hret hjt hbt hF0 ⟨hF1, by omega⟩
      obtain ⟨ω3, run3, c1, c5, c6⟩ := vb (p := p) (P := P) (R := R) x ω2 μ2 F (ptr + 8 + 24 * j) (ptr + 8 + 24 * len)
        t arm head nxt back ret hv (by omega) (by omega) (by omega) (by rw [b1, a1]; exact h1) (by rw [b5, a5]; exact h5)
        (by rw [Memory.readN_congr (fun i hi => stk2 _ (by omega) (by omega))]; exact s8)
        (fun a h1 h2 => by
          have := rdF a (by omega) (by omega)
          unfold Memory.readable at this ⊢
          rw [pg2]; exact this)
      exact tail ω3 μ2 (free s (q j)) _ (run1.trans (run2.trans run3)) (c1.trans (b1.trans a1)) c5
        (c6.trans (b6.trans a6)) H2 (fun a h0 ha => stk2 a h0 ha) (fun d hd hu hne => keep2 d hd hu (hne hc0)) pg2
        ro2

/-- An allocated chunk's data lies below 2^31. -/
theorem data_lo {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State} (H : HeapCtx env pb S0 S1 μ s)
    {d : Chunk} (hd : d ∈ chunks s) (hu : d.used = true) {a : Nat} (ha : InData d a) : a < 2147483648 := by
  have := Decode.VecU8.chunk_in H.wf hd hu
  have := H.hbT
  unfold InData at ha
  omega

/-- A memory with the same pages, keeping the reads of what is not writable, keeps them from μ's view. -/
theorem ro_trans {μ μ1 μ2 : Memory} (pg : ∀ a, μ1.writable a = μ.writable a)
    (r1 : ∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b)
    (r2 : ∀ b, b < two32 → μ1.writable b = false → μ2.read b = μ1.read b) :
    ∀ b, b < two32 → μ.writable b = false → μ2.read b = μ.read b :=
  fun b hb hw => by rw [r2 b hb (by rw [pg]; exact hw), r1 b hb hw]

/-- **One heap element dropped** (29188 … 29181): element k at el = E + 232 k, of index 5 (`DeleteItems`) or 19
    (`Imported`), whose `Vec<Vec<u8>>` {c0, ptr, len} (words 1 … 3) holds len items {c i, q i} at ptr + 24 i: every
    item with c i ≠ 0 has its buffer, the allocated chunk `cs i`, freed, then the outer buffer, the chunk `co`, if
    c0 ≠ 0. The element lies in the data of an allocated chunk `cb` that is none of those. On to the next element
    with ω₅ = n (from F). The heap context holds after the frees; every other allocated chunk stays with its data; the
    frame from F up is kept but for F + 8 … F + 16 and F + 48 … F + 56; the pages and the read-only bytes are kept. -/
theorem drop_vv {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (F E k n t arm head nxt back ret : Nat) (hv : VK t arm head nxt back ret)
    (c0 ptr len : Nat) (c q : Nat → Nat) (cs : Nat → Chunk) (co cb : Chunk)
    (hF : 2147483716 ≤ F ∧ S0 + 40 ≤ F ∧ F + 80 ≤ S1 ∧ F % 8 = 0)
    (hel : E + 232 * k + 32 ≤ 2147483648) (hn : n < 18446744073709551616)
    (hco0 : c0 ≠ 0 → co.addr + 32 = ptr) (hc01 : 24 * c0 < 18446744073709551616) (hlen0 : len ≠ 0 → c0 ≠ 0)
    (hptr : ptr + 24 * len + 8 ≤ 2147483648)
    (hc : ∀ i, i < len → c i < 18446744073709551616) (hq : ∀ i, i < len → q i < 18446744073709551616)
    (hca : ∀ i, i < len → c i ≠ 0 → (cs i).addr + 32 = q i)
    (hdist : ∀ i i', i < len → i' < len → i ≠ i' → c i ≠ 0 → c i' ≠ 0 → cs i ≠ cs i')
    (hco : ∀ i, i < len → c i ≠ 0 → cs i ≠ co) (hcoD : ∀ a, ptr ≤ a → a < ptr + 24 * len → InData co a)
    (hcbD : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → InData cb a)
    (hcbco : c0 ≠ 0 → cb ≠ co) (hcbcs : ∀ i, i < len → c i ≠ 0 → cb ≠ cs i)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat k) (H : HeapCtx env pb S0 S1 μ s)
    (cbm : cb ∈ chunks s) (cbu : cb.used = true) (com : c0 ≠ 0 → co ∈ chunks s ∧ co.used = true)
    (hcs : ∀ i, i < len → c i ≠ 0 → cs i ∈ chunks s ∧ (cs i).used = true)
    (s0 : μ.readN F 8 = Num.encodeLE 8 n)
    (s40 : μ.readN (F + 40) 8 = Num.encodeLE 8 E) (s32 : μ.readN (F + 32) 8 = Num.encodeLE 8 9223372036854775807)
    (s24 : μ.readN (F + 24) 8 = Num.encodeLE 8 9223372036854775832) (s16 : μ.readN (F + 16) 8 = Num.encodeLE 8 67760)
    (hD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (e8 : μ.readN (E + 232 * k + 8) 8 = Num.encodeLE 8 c0)
    (e16 : μ.readN (E + 232 * k + 16) 8 = Num.encodeLE 8 ptr)
    (e24 : μ.readN (E + 232 * k + 24) 8 = Num.encodeLE 8 len)
    (hw : ∀ i, i < len → μ.readN (ptr + 24 * i) 8 = Num.encodeLE 8 (c i) ∧
      μ.readN (ptr + 24 * i + 8) 8 = Num.encodeLE 8 (q i))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true) :
    ∃ ω' μ' s' N, FreeStepsH p R 29188 ω μ x 29181 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = ω[6] ∧ HeapCtx env pb S0 S1 μ' s' ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (c0 ≠ 0 → d ≠ co) → (∀ i, i < len → c i ≠ 0 → d ≠ cs i) →
        d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
  obtain ⟨hF0, hF1, hF2, hF8⟩ := hF
  have hS := H.hS1
  have hwF : ∀ a, F ≤ a → a < F + 80 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have rdcb : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H cbm cbu (hcbD a h1 h2))
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a48, afr, ard, awr⟩ := ddV (p := p) (P := P) (R := R) x ω μ F E k t arm head nxt
    back ret hv ⟨by omega, by omega, hF8⟩ (by omega) (Or.inl (by omega)) h1 h6 s40 s32 s24 s16 hD tab hrt
    (fun a h1 h2 => rdcb a h1 (by omega)) hwF
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
  have k1 : ∀ a l, a + l ≤ 2147483648 → μ1.readN a l = μ.readN a l :=
    fun a l h => Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))
  have ro1 : ∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b := fun b hb hwb => by
    refine afr b (by unfold two32 at hb; omega) ?_
    by_cases h : F + 48 ≤ b ∧ b < F + 56
    · have := hwF b (by omega) (by omega); rw [hwb] at this; exact absurd this (by decide)
    · omega
  -- the items, from arm to 29542
  have mid : ∃ ω2 μ2 s2 N2, FreeStepsH p R arm ω1 μ1 x 29542 ω2 μ2 x N2 ∧ ω2[1] = ω[1] ∧ ω2[6] = ω[6] ∧
      HeapCtx env pb S0 S1 μ2 s2 ∧
      (∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → μ2.read a = μ1.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (∀ i, i < len → c i ≠ 0 → d ≠ cs i) →
        d ∈ chunks s2 ∧ ∀ a, InData d a → μ2.read a = μ1.read a) ∧
      (∀ a, μ2.readable a = μ1.readable a) ∧ (∀ a, μ2.writable a = μ1.writable a) ∧
      (∀ b, b < two32 → μ1.writable b = false → μ2.read b = μ1.read b) := by
    by_cases hl : len = 0
    · obtain ⟨ω2, run2, b1, b6⟩ := va0 (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) t arm head nxt back ret hv
        (by omega) (by omega) (a1.trans h1) a48 (by rw [k1 _ _ (by omega), e24, hl])
        (fun a h1 h2 => by rw [ard]; exact rdcb a (by omega) h2)
        (fun a h1 h2 => by rw [ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
      exact ⟨ω2, μ1, s, 3, run2, b1.trans a1, b6.trans a6, H1, fun _ _ _ _ => rfl,
        fun d hd _ _ => ⟨hd, fun _ _ => rfl⟩, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    · have hc0 : c0 ≠ 0 := hlen0 hl
      obtain ⟨hcom, hcou⟩ := com hc0
      obtain ⟨ω2, μ2, run2, b1, b5, b6, b8, bfr, brd, bwr⟩ := va (p := p) (P := P) (R := R) x ω1 μ1 F (E + 232 * k) ptr
        len t arm head nxt back ret hv ⟨by omega, by omega, hF8⟩ (by omega) hl (by omega) (a1.trans h1) a48
        (by rw [k1 _ _ (by omega)]; exact e16) (by rw [k1 _ _ (by omega)]; exact e24)
        (fun a h1 h2 => by rw [ard]; exact rdcb a (by omega) h2)
        (fun a h1 h2 => by rw [awr]; exact hwF a h1 h2)
      have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.GrowOne.ctx_high H1 (fun a ha => bfr a (by omega) (Or.inl (by omega))) bwr
      have k2 : ∀ a l, a + l ≤ 2147483648 → μ2.readN a l = μ.readN a l := fun a l h => by
        rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (Or.inl (by omega)))]; exact k1 a l h
      obtain ⟨ω3, μ3, s3, N3, run3, c1, c6, H3, st3, kp3, pg3, ro3⟩ := items_loop (p := p) (P := P) (R := R) env pb S0
        S1 x F ptr len t arm head nxt back ret hv c q cs co ⟨hF0, hF1, hF2⟩ hptr hc hq hca hdist hco hcoD len 0 ω2 μ2 s
        (by omega) (by omega) (b1.trans (a1.trans h1)) (by rw [b5]) H2 b8 hcom hcou
        (fun i _ hi => by rw [k2 _ _ (by omega), k2 _ _ (by omega)]; exact hw i hi)
        (fun i _ hi hci => hcs i hi hci)
      refine ⟨ω3, μ3, s3, 13 + N3, run2.trans run3, by rw [c1, b1, a1], by rw [c6, b6, a6], H3,
        fun a h0 hF hne => by rw [st3 a h0 hF, bfr a h0 hne], fun d hd hu hne => ?_,
        fun a => by unfold Memory.readable; rw [pg3]; exact congrFun (funext brd) a,
        fun a => by unfold Memory.writable; rw [pg3]; exact congrFun (funext bwr) a, fun b hb hwb => ?_⟩
      · obtain ⟨hd3, kd3⟩ := kp3 d hd hu (fun i _ hi hci => hne i hi hci)
        exact ⟨hd3, fun a ha => by
          rw [kd3 a ha, bfr a (by have := data_lo H hd hu ha; omega) (Or.inl (by have := data_lo H hd hu ha; omega))]⟩
      · have hwb2 : μ2.writable b = false := by rw [bwr]; exact hwb
        rw [ro3 b hb hwb2]
        refine bfr b (by unfold two32 at hb; omega) ?_
        by_cases h : F + 8 ≤ b ∧ b < F + 16
        · have := hwF b (by omega) (by omega); rw [← awr, hwb] at this; exact absurd this (by decide)
        · omega
  obtain ⟨ω2, μ2, s2, N2, run2, b1, b6, H2, st2, kp2, rd2, wr2, ro2⟩ := mid
  have kcb := kp2 cb cbm cbu hcbcs
  have rcb : ∀ a l, E + 232 * k ≤ a → a + l ≤ E + 232 * k + 32 → μ2.readN a l = μ.readN a l := fun a l h h' => by
    rw [Memory.readN_congr (fun j hj => kcb.2 _ (hcbD _ (by omega) (by omega)))]; exact k1 a l (by omega)
  have rdcb2 : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 32 → μ2.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable H2 kcb.1 cbu (hcbD a h1 h2))
  have rdF2 : ∀ a, F ≤ a → a < F + 80 → μ2.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (H2.st a (by omega) (by omega))
  have f48 : μ2.readN (F + 48) 8 = Num.encodeLE 8 (E + 232 * k) := by
    rw [Memory.readN_congr (fun j hj => st2 _ (by omega) (by omega) (Or.inr (by omega)))]; exact a48
  have f0 : μ2.readN F 8 = Num.encodeLE 8 n := by
    rw [Memory.readN_congr (fun j hj => st2 _ (by omega) (by omega) (Or.inl (by omega))),
      Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))]; exact s0
  have fr12 : ∀ a, a < 4294967296 → F ≤ a → (a < F + 8 ∨ F + 16 ≤ a) → (a < F + 48 ∨ F + 56 ≤ a) →
      μ2.read a = μ.read a := fun a h0 hF hne hne' => by rw [st2 a h0 hF hne, afr a h0 hne']
  have kp12 : ∀ d ∈ chunks s, d.used = true → (∀ i, i < len → c i ≠ 0 → d ≠ cs i) →
      d ∈ chunks s2 ∧ ∀ a, InData d a → μ2.read a = μ.read a := fun d hd hu hne => by
    obtain ⟨hd2, kd2⟩ := kp2 d hd hu hne
    exact ⟨hd2, fun a ha => by
      rw [kd2 a ha, afr a (by have := data_lo H hd hu ha; omega) (Or.inl (by have := data_lo H hd hu ha; omega))]⟩
  have ro12 := ro_trans awr ro1 ro2
  by_cases hc0 : c0 = 0
  · obtain ⟨ω3, run3, c1, c5, c6⟩ := vo0 (p := p) (P := P) (R := R) x ω2 μ2 F (E + 232 * k) n (by omega) (by omega) hn
      (b1.trans h1) f48 f0 (by rw [rcb _ _ (by omega) (by omega), e8, hc0])
      (fun a h1 h2 => rdcb2 a (by omega) (by omega)) rdF2
    exact ⟨ω3, μ2, s2, 20 + N2 + 5, (run1.trans run2).trans run3, by rw [c1, b1], c5, by rw [c6, b6], H2, fr12,
      fun d hd hu _ hne => kp12 d hd hu hne, fun a => by rw [rd2, ard], fun a => by rw [wr2, awr], ro12⟩
  · obtain ⟨hcom, hcou⟩ := com hc0
    obtain ⟨hco2, -⟩ := kp2 co hcom hcou (fun i hi hci => hco i hi hci |>.symm)
    obtain ⟨ω3, run3, c0', c1, c5, c6, c7⟩ := vo1 (p := p) (P := P) (R := R) x ω2 μ2 F (E + 232 * k) n c0 ptr (by omega)
      (by omega) hn hc0 hc01 (by omega) (b1.trans h1) f48 f0 (by rw [rcb _ _ (by omega) (by omega)]; exact e8)
      (by rw [rcb _ _ (by omega) (by omega)]; exact e16) (fun a h1 h2 => rdcb2 a (by omega) (by omega)) rdF2
    obtain ⟨ω4, μ4, run4, H4, -, pg4, ro4, stk4, -, keep4, d0, d1, d5, d6⟩ :=
      Decode.DeallocCall.dealloc_call (R := R) (p := p) (P := P) env pb S0 S1 x ω3 μ2 s2 F ptr 1356 29181 co H2 hco2
        hcou (hco0 hc0) c0' (by rw [c1, b1]; exact h1) c7 (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_677]) bs_29181 hF0 ⟨hF1, by omega⟩
    refine ⟨ω4, μ4, free s2 ptr, 20 + N2 + 14 + 249, ((run1.trans run2).trans run3).trans run4,
      by rw [d1, c1, b1], by rw [d5, c5], by rw [d6, c6, b6], H4,
      fun a h0 hF hne hne' => by rw [stk4 a h0 hF, fr12 a h0 hF hne hne'], fun d hd hu hne hne' => ?_,
      fun a => by unfold Memory.readable; rw [pg4]; exact (congrFun (funext rd2) a).trans (ard a),
      fun a => by unfold Memory.writable; rw [pg4]; exact (congrFun (funext wr2) a).trans (awr a),
      fun b hb hwb => ?_⟩
    · obtain ⟨hd2, kd2⟩ := kp12 d hd hu hne'
      obtain ⟨hd4, kd4⟩ := keep4 d hd2 hu (hne hc0)
      exact ⟨hd4, fun a ha => by rw [kd4 a ha, kd2 a ha]⟩
    · have hwb2 : μ2.writable b = false := by rw [wr2, awr]; exact hwb
      rw [ro4 b hb hwb2, ro12 b hb hwb]

end Services.Bootstrap.Refine.DropOutH
