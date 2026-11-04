import PVM.Logic.Det

/-!
# Code facts: what a proof needs to know about a program, as one checkable list

A proof that follows a large program through Ψ₁ needs only a few facts about it: that the blob
passes 𝔳_blob, and, at each index it visits, the decoded instruction and ı + 1 + skip(ı); for
branches and jumps, whether the targets are block starts; for `jump_ind`/`load_imm_jump_ind`, the
jump table. `checkCode p fs` checks a list of such facts against the blob `p` in one `Bool`.

`checkCode_sound` turns `checkCode p fs = true` into the facts themselves, with `deblob p i = some P`
at each listed index. So a theorem about a program can take `checkCode p fs = true` as a hypothesis
and be proved from the list alone, whatever evaluates the hypothesis (the kernel, or compiled code
for blobs too large for the kernel).
-/

namespace PVM

/-- The most gas the basic block of a step on a counted chain may cost (GP eq. `gascostforblock`):
    2^13, above the costliest block of the services proved about here (`PVM.FreeStepsH`). -/
def stepCostCap : Nat := 8192

/-- One fact about a program. -/
inductive CodeFact where
  /-- At index i: 𝔳_inst, the decoded instruction, and ı + 1 + skip(ı). -/
  | instr (i : Nat) (ins : Instr) (next : Nat)
  /-- Whether n ∈ ϖ (a basic-block start). -/
  | blockStart (n : Nat) (b : Bool)
  /-- |**j**|. -/
  | jumpTableSize (n : Nat)
  /-- **j**_k = t. -/
  | jumpEntry (k t : Nat)
  /-- s ∈ ϖ, no index in (s, e) is in ϖ, and ϱ^Δ of the block at s is at most `stepCostCap`. -/
  | block (s e : Nat)
  deriving DecidableEq, Repr

/-- Whether a fact holds of a program. -/
def CodeFact.holds (P : Program) : CodeFact → Bool
  | .instr i ins n => P.vInst i && P.decode i == some ins && P.next i == n
  | .blockStart n b => P.isBlockStart n == b
  | .jumpTableSize n => P.jumpTable.size == n
  | .jumpEntry k t => P.jumpTable.getD k 0 == t
  | .block s e => P.isBlockStart s && ((List.range (e - s - 1)).all fun k => !P.isBlockStart (s + 1 + k)) &&
      decide (P.blockCost s ≤ stepCostCap)

/-- The blob deblobs, passes 𝔳_blob, and every listed fact holds. -/
def checkCode (p : ByteArray) (fs : List CodeFact) : Bool :=
  match Blob.parse? p with
  | some P => P.vBlob && fs.all (·.holds P)
  | none => false

/-- What `checkCode` establishes. -/
structure CodeOk (p : ByteArray) (fs : List CodeFact) (P : Program) : Prop where
  parse : Blob.parse? p = some P
  vBlob : P.vBlob = true
  facts : ∀ f ∈ fs, f.holds P = true

theorem checkCode_sound {p : ByteArray} {fs : List CodeFact} (h : checkCode p fs = true) :
    ∃ P, CodeOk p fs P := by
  unfold checkCode at h
  split at h
  · rename_i P hP
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨P, hP, h.1, h.2⟩
  · cases h

namespace CodeOk

variable {p : ByteArray} {fs : List CodeFact} {P : Program}

theorem instr (h : CodeOk p fs P) {i : Nat} {ins : Instr} {n : Nat}
    (hm : CodeFact.instr i ins n ∈ fs) :
    deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n := by
  have hf := h.facts _ hm
  simp only [CodeFact.holds, Bool.and_eq_true, beq_iff_eq] at hf
  refine ⟨?_, hf.1.2, hf.2⟩
  simp [deblob, h.parse, h.vBlob, hf.1.1]

theorem blockStart (h : CodeOk p fs P) {n : Nat} {b : Bool} (hm : CodeFact.blockStart n b ∈ fs) :
    P.isBlockStart n = b := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

theorem jumpTableSize (h : CodeOk p fs P) {n : Nat} (hm : CodeFact.jumpTableSize n ∈ fs) :
    P.jumpTable.size = n := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

theorem jumpEntry (h : CodeOk p fs P) {k t : Nat} (hm : CodeFact.jumpEntry k t ∈ fs) :
    P.jumpTable.getD k 0 = t := by
  have hf := h.facts _ hm
  simpa [CodeFact.holds] using hf

/-- 𝔏(ı) = s when s ∈ ϖ and nothing in (s, ı] is. -/
theorem _root_.PVM.Program.blockStartFrom_eq (P : Program) {s : Nat} (hs : P.isBlockStart s = true) :
    ∀ i, s ≤ i → (∀ k, s < k → k ≤ i → P.isBlockStart k = false) → P.blockStartFrom i = s := by
  intro i
  induction i with
  | zero => intro h _; rw [Nat.le_zero.1 h]; rfl
  | succ i ih =>
    intro hsi hno
    rw [Program.blockStartFrom]
    by_cases he : s = i + 1
    · subst he; rw [if_pos hs]
    · rw [if_neg (by rw [hno (i + 1) (by omega) (Nat.le_refl _)]; decide)]
      exact ih (by omega) (fun k h1 h2 => hno k h1 (by omega))

theorem cost (h : CodeOk p fs P) {s e i : Nat} (hm : CodeFact.block s e ∈ fs) (hi : s ≤ i ∧ i < e) :
    P.blockCost (P.blockStartOf i) ≤ stepCostCap := by
  have hf := h.facts _ hm
  simp only [CodeFact.holds, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    decide_eq_true_eq] at hf
  obtain ⟨⟨hs, hno⟩, hc⟩ := hf
  rw [Program.blockStartOf, P.blockStartFrom_eq hs i hi.1 (fun k h1 h2 => by
    have := hno (k - s - 1) (by omega)
    rwa [show s + 1 + (k - s - 1) = k by omega] at this)]
  exact hc

/-- An instruction fact, with the cost of the block it is in. -/
theorem instrCost (h : CodeOk p fs P) {i : Nat} {ins : Instr} {n s e : Nat}
    (hm : CodeFact.instr i ins n ∈ fs) (hb : CodeFact.block s e ∈ fs) (hi : s ≤ i ∧ i < e) :
    deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap :=
  let ⟨a, b, c⟩ := h.instr hm
  ⟨a, b, c, h.cost hb hi⟩

end CodeOk

/-- A gas-free step at a listed instruction is the instruction's mutation, with ε^μ. -/
theorem Program.freeStep_of_decode {P : Program} {i : Nat} {ins : Instr} (ω : Regs) (μ : Memory)
    (h : P.decode i = some ins) :
    P.freeStep i ω μ =
      let m := P.exec i ins ω μ
      finalState .cont i ω μ m (memoryException μ m.reads m.writes) := by
  simp [Program.freeStep, h]

end PVM
