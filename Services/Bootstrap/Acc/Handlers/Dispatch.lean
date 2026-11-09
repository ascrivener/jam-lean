import Services.Bootstrap.CodeAAll
import Services.Bootstrap.Decode.Loop
import PVM.Logic.Go

/-!
# The instruction dispatch of bootstrap's accumulate, and the shape of a handler summary

Bootstrap's accumulate runs each instruction of an operand in a loop (8540 … 14546; see
`Services/Bootstrap/Acc/README.md`), with the frame pointer ω₁ = sp = 4278057152 (`SP`). One pass of
the loop takes the next 232-octet `Instruction` value from the operand's `Vec`, copies it to
sp + 744 and logs it. It then copies it again to sp + 1144 and reaches the **dispatch point 8822**.

From 8822 to 8868:
- The binary reads the discriminant word d at sp + 1144.
- It computes the tag. If 2⁶³ ≤ d < 2⁶³ + 24, the tag is d − 2⁶³ + 1, using ω₆ = 2⁶³ + 24 and the
  constant 2⁶³ + 1 at sp + 216. Otherwise it is 0 (`CreateService`, the variant whose first word
  holds data).
- It stores the low four octets of the word at sp + 192 at sp + 1380.
- It jumps through the 25-entry table at 65736 (`jumpTab`) to the handler.

Every handler that returns ends at **14278**. There the 144-octet `Result<InstructionOutput,
InstructionError>` at sp + 1000 (`RES`) is formatted, logged and pushed onto the results. As the
binary lays it out (read off the handlers, `NoCall.lean`):
- `Err(e)` is the octet 255 at `RES`, then e's index in `InstructionError`'s declaration order
  (`Spec.Err`: `createService` = 0, …, `lookup` = 6, …, `invalid` = 11) at `RES` + 1;
- `Ok(r)` is r's index in `InstructionOutput` (`Spec.Ret`: `unit` = 0, …, `data` = 5, `dataVec` = 6) at
  `RES`, and r's fields from `RES` + 8. For `data(d)` that is the `Vec<u8>`'s capacity, pointer and
  length at `RES` + 8, + 16 and + 24.
The tail at 14278 reads only ω₁ and memory.

## The pattern of a handler summary

A handler summary for instruction `I` is a theorem `Handlers.I` (or `I_case` for one branch):
- **From** 8822, under `AtDispatch ω μ bs`: the frame, the jump table, and the instruction's 232
  octets `bs` in both of its copies (sp + 744 and sp + 1144). It also takes facts about `bs`
  (discriminant and fields), in the form the decode proofs' `ElemOk` leave them
  (`bs.take 8 = …`, `(bs.drop 8).take 32 = …`).
- **Host calls**: each one through the contract (`accContract env`), with its arguments named in the
  docstring. Handlers with no host call are stated for any `R`.
- **To** 14278, with ω'₁ = ω₁. It states the result's octets at `RES` and every other memory change
  as `KeepsExcept μ μ' rs`: memory is unchanged outside the listed (start, length) ranges. Readable
  and writable pages are kept.
- A handler that traps instead ends in `FreeRunH … .panic`.
- Summaries assume `[HasCode p P] [HasCodeA p P]`: the handlers are in `CodeA`, and the jump
  table's size (`jts`) is a `Code` fact.

Later handlers (with heap allocation, `core::fmt` or several calls) keep the same entry, exit and
result description and add their own hypotheses (a heap, a formatting summary) and results (a new
context x').
-/

namespace Services.Bootstrap.Acc.Handlers

open PVM Services.Bootstrap Services.Bootstrap.CodeA

/-- The frame pointer ω₁ of accumulate's entry function (6378 … 15368, a 1856-octet frame). -/
abbrev SP : Nat := 4278057152

/-- Where a handler leaves its result: sp + 1000. -/
abbrev RES : Nat := 4278058152

/-- The jump table of the dispatch at 65736 (in the read-only data): 25 little-endian `i32`
    offsets from 65736, one per tag. -/
def jumpTab : List UInt8 :=
  [106, 0, 255, 255, 226, 0, 255, 255, 210, 0, 255, 255, 172, 0, 255, 255, 132, 0, 255, 255,
   160, 0, 255, 255, 224, 0, 255, 255, 222, 0, 255, 255, 198, 0, 255, 255, 8, 1, 255, 255,
   8, 1, 255, 255, 138, 0, 255, 255, 246, 0, 255, 255, 152, 0, 255, 255, 124, 0, 255, 255,
   148, 0, 255, 255, 120, 1, 255, 255, 120, 0, 255, 255, 118, 0, 255, 255, 112, 0, 255, 255,
   2, 1, 255, 255, 8, 1, 255, 255, 250, 0, 255, 255, 234, 0, 255, 255, 206, 0, 255, 255]

/-- **The state at the dispatch point 8822.**
    - ω₁ = sp and ω₆ = 2⁶³ + 24, and the word at sp + 216 is 2⁶³ + 1: these make the tag.
    - The frame sp … sp + 1856 is writable.
    - The jump table is readable and holds `jumpTab`.
    - The instruction's 232 octets `bs` are at sp + 744 and at sp + 1144. -/
structure AtDispatch (ω : Regs) (μ : Memory) (bs : List UInt8) : Prop where
  sp : ω[1] = UInt64.ofNat 4278057152
  r6 : ω[6] = UInt64.ofNat 9223372036854775832
  c216 : μ.readN 4278057368 8 = Num.encodeLE 8 9223372036854775809
  frame : ∀ a, 4278057152 ≤ a → a < 4278059008 → μ.writable a = true
  tabR : ∀ a, 65736 ≤ a → a < 65836 → μ.readable a = true
  tab : μ.readN 65736 100 = jumpTab
  slotA : μ.readN 4278057896 232 = bs
  slotB : μ.readN 4278058296 232 = bs

/-- Memory `μ'` agrees with `μ` outside the ranges `rs`, each given as (start, length). -/
def KeepsExcept (μ μ' : Memory) (rs : List (Nat × Nat)) : Prop :=
  ∀ a, a < 4294967296 → (∀ r ∈ rs, a < r.1 ∨ r.1 + r.2 ≤ a) → μ'.read a = μ.read a

/-- A word of the slot, from the 232 octets and the decode's description of them. -/
theorem slot_word {μ : Memory} {base : Nat} {bs : List UInt8} (h : μ.readN base 232 = bs) (o : Nat)
    (ho : o + 8 ≤ 232) {w : List UInt8} (hw : (bs.drop o).take 8 = w) : μ.readN (base + o) 8 = w := by
  rw [Decode.Loop.readN_sub μ base 232 o 8 bs h ho, hw]

/-- The first word of the slot (the discriminant). -/
theorem slot_word0 {μ : Memory} {base : Nat} {bs : List UInt8} (h : μ.readN base 232 = bs)
    {w : List UInt8} (hw : bs.take 8 = w) : μ.readN base 8 = w := by
  have := slot_word h 0 (by decide) (w := w) (by simpa using hw)
  simpa using this

/-- Any word of memory, named: `obtain ⟨v, hv, hm⟩ := word_exists μ a` gives v < 2⁶⁴ with
    `μ.readN a 8 = ℰ₈(v)`. (The dispatch copies the word at sp + 192 without looking at it;
    naming it keeps the steps' terms small.) -/
theorem word_exists (μ : Memory) (a : Nat) :
    ∃ v, v < 18446744073709551616 ∧ μ.readN a 8 = Num.encodeLE 8 v :=
  ⟨rdN μ a 8, rdN_lt64 μ a, (encodeLE_rdN μ a 8).symm⟩

/-- Any n octets of memory, named as a number v < 256ⁿ. -/
theorem bytes_exist (μ : Memory) (a n : Nat) : ∃ v, v < 256 ^ n ∧ μ.readN a n = Num.encodeLE n v :=
  ⟨rdN μ a n, rdN_lt μ a n, (encodeLE_rdN μ a n).symm⟩

/-- ℕ_{a…+n} ⊆ 𝕍_μ (`Memory.rangeReadable`, as Ω's `readMem` checks it) from readability octet by
    octet. (The same as `Services.Witness.rangeReadable_of`, which lives behind witness's imports.) -/
theorem rangeReadable_of' {μ : Memory} {a n : Nat} (h : ∀ j, a ≤ j → j < a + n → μ.readable j = true)
    (hb : a + n ≤ 2 ^ 32) : μ.rangeReadable a n = true := by
  unfold Memory.rangeReadable
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n == 0) = false := by simp [hn]
  rw [hn', Bool.false_or, Bool.and_eq_true, List.all_eq_true]
  refine ⟨by simp [hb], fun k hk => ?_⟩
  simp only [List.mem_range] at hk
  have hpg : pageSize = 4096 := rfl
  have hk' : (a / pageSize + k) * pageSize ≤ a + n - 1 := by
    rw [hpg] at hk ⊢
    have := Nat.div_mul_le_self (a + n - 1) 4096
    have : a / 4096 + k ≤ (a + n - 1) / 4096 := by omega
    calc (a / 4096 + k) * 4096 ≤ (a + n - 1) / 4096 * 4096 := Nat.mul_le_mul_right _ this
      _ ≤ a + n - 1 := by omega
  let j := max a ((a / pageSize + k) * pageSize)
  have hj : μ.readable j = true := h j (Nat.le_max_left _ _) (by simp only [j]; omega)
  have hpage : j / pageSize = a / pageSize + k := by
    simp only [j, hpg] at hk' ⊢
    rcases Nat.le_total a ((a / 4096 + k) * 4096) with h1 | h1
    · rw [Nat.max_eq_right h1]; simp
    · rw [Nat.max_eq_left h1]
      have : k = 0 := by omega
      subst this; simp
  simp only [Memory.readable] at hj ⊢
  rw [← hpage]
  simpa [hpg, Nat.mul_div_cancel] using hj

/-- The jump table's entry for tag t. -/
theorem tab_entry {μ : Memory} (h : μ.readN 65736 100 = jumpTab) (t : Nat) (ht : t < 25) :
    μ.readN (65736 + 4 * t) 4 = (jumpTab.drop (4 * t)).take 4 :=
  Decode.Loop.readN_sub μ 65736 100 (4 * t) 4 jumpTab h (by omega)

end Services.Bootstrap.Acc.Handlers
