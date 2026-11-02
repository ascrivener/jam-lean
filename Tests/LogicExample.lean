import PVM

/-!
# A worked "for all inputs" proof with the gas-free logic

The program counts ω₈ down to zero and halts:

```
0: add_imm_64     ω₈ ← ω₈ + (−1)          95 88 ff   (opcode 149)
3: branch_ne_imm  if ω₈ ≠ 0 goto 0         52 08 fd   (opcode 82)
6: jump_ind       ω₀ + 0                    32 00      (opcode 50)
```

**Theorem** (`countdown_spec`): for every initial register file with ω₀ = 2^32 − 2^16, every
memory and every amount of gas, Ψ either runs out of gas or halts with ω₈ = 0.

The proof never mentions gas or basic blocks: `psi_freeRun` moves it to the gas-free machine,
and an invariant on the program counter does the rest.
-/

namespace PVM.Tests.Countdown

open PVM

/-- The PVM blob: |j| = 0, z = 0, |c| = 8, **c**, **k** = 0b01001001. -/
def blob : ByteArray := ⟨#[0, 0, 8, 149, 0x88, 0xff, 82, 0x08, 0xfd, 50, 0x00, 73]⟩

/-- The program the blob decodes to. -/
def prog : Program :=
  { code := ⟨#[149, 0x88, 0xff, 82, 0x08, 0xfd, 50, 0x00]⟩
    mask := #[true, false, false, true, false, false, true, false]
    jumpTable := #[] }

/-- ω₀ as Y sets it: the address whose dynamic jump halts. -/
def haltAddr : UInt64 := UInt64.ofNat (2 ^ 32 - 2 ^ 16)

/-- Field-wise equality test for programs (`Program` has no `DecidableEq`). -/
def progBEq (P Q : Program) : Bool :=
  P.code.data == Q.code.data && P.mask == Q.mask && P.jumpTable == Q.jumpTable

theorem eq_of_progBEq {P Q : Program} (h : progBEq P Q = true) : P = Q := by
  obtain ⟨⟨c⟩, k, j⟩ := P
  obtain ⟨⟨c'⟩, k', j'⟩ := Q
  simp only [progBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

/-- The blob deblobs to `prog` at each instruction (checked by kernel evaluation). -/
theorem deblob_eq (i : Nat) (hi : i = 0 ∨ i = 3 ∨ i = 6) : deblob blob i = some prog := by
  have key : (deblob blob i).map (progBEq · prog) = some true := by
    rcases hi with rfl | rfl | rfl <;> decide +kernel
  cases h : deblob blob i with
  | none => rw [h] at key; cases key
  | some P =>
    rw [h, Option.map_some] at key
    rw [eq_of_progBEq (Option.some.inj key)]

theorem dec0 : prog.decode 0 = some (.twoRegImm .addImm64 8 8 (UInt64.ofNat (2 ^ 64 - 1))) := by
  decide +kernel
theorem dec3 : prog.decode 3 = some (.regImmOffset .branchNeImm 8 0 0) := by decide +kernel
theorem dec6 : prog.decode 6 = some (.regImm .jumpInd 0 0) := by decide +kernel
theorem next0 : prog.next 0 = 3 := by decide +kernel
theorem next3 : prog.next 3 = 6 := by decide +kernel
theorem bs0 : prog.isBlockStartInt 0 = true := by decide +kernel
theorem bs6 : prog.isBlockStart 6 = true := by decide +kernel

/-- No memory is accessed: ε^μ = ▸. -/
theorem noMem (μ : Memory) : memoryException μ [] [] = none := rfl

-- Each step is unfolded in two passes: first reduce `exec` on the decoded instruction, then the
-- arithmetic, so that `simp` never rewrites inside `exec`'s other branches.

/-- Step at 0: ω₈ gets a new value, nothing else changes, and control moves to 3. -/
theorem step0 (ω : Regs) (μ : Memory) : ∃ v, prog.freeStep 0 ω μ = (.cont, 3, ω.set 8 v, μ) := by
  simp only [Program.freeStep, dec0, Option.getD_some, Program.exec]
  simp only [next0, Program.finalState, noMem]
  exact ⟨_, rfl⟩

/-- Step at 3: back to 0 while ω₈ ≠ 0, on to 6 once ω₈ = 0. -/
theorem step3 (ω : Regs) (μ : Memory) :
    prog.freeStep 3 ω μ = (.cont, if ω[8] = 0 then 6 else 0, ω, μ) := by
  simp only [Program.freeStep, dec3, Option.getD_some, Program.exec]
  simp only [Program.branch, next3, bs0, bs6, Exec.regImmBranchCond, Program.finalState, noMem]
  rw [show ω.get 8 = ω[8] from rfl]
  by_cases h : ω[8] = 0
  · simp [h]
  · have : ω[8].toNat ≠ 0 := by intro h'; exact h (UInt64.toNat_inj.1 (by simpa using h'))
    simp [h, this]

/-- Step at 6: with ω₀ = 2^32 − 2^16 the dynamic jump halts. -/
theorem step6 (ω : Regs) (μ : Memory) (h0 : ω[0] = haltAddr) :
    prog.freeStep 6 ω μ = (.halt, 6, ω, μ) := by
  simp only [Program.freeStep, dec6, Option.getD_some, Program.exec]
  rw [show ω.get 0 = haltAddr from h0]
  simp only [Program.djump, Program.finalState, noMem]
  simp [haltAddr, two32]

/-- The invariant: ω₀ still holds the halt address, and the program counter is at 0 or 3, or at
    6 with ω₈ = 0. -/
def Inv (i : Nat) (ω : Regs) (_ : Memory) : Prop :=
  ω[0] = haltAddr ∧ (i = 0 ∨ i = 3 ∨ (i = 6 ∧ ω[8] = 0))

theorem inv_step (i : Nat) (ω : Regs) (μ : Memory) (i' : Nat) (ω' : Regs) (μ' : Memory)
    (hI : Inv i ω μ) (hn : FreeNext blob i ω μ i' ω' μ') : Inv i' ω' μ' := by
  obtain ⟨h0, hpc⟩ := hI
  obtain ⟨P, hP, hs⟩ := hn
  have hpc' : i = 0 ∨ i = 3 ∨ i = 6 := by omega
  rw [deblob_eq i hpc'] at hP
  cases hP
  rcases hpc with rfl | rfl | ⟨rfl, -⟩
  · obtain ⟨v, hv⟩ := step0 ω μ
    rw [hv] at hs
    cases hs
    exact ⟨by simp [h0], by simp⟩
  · rw [step3] at hs
    cases hs
    by_cases h8 : ω[8] = 0
    · exact ⟨h0, by simp [h8]⟩
    · exact ⟨h0, by simp [h8]⟩
  · rw [step6 ω μ h0] at hs
    cases hs

theorem inv_exit (j : Nat) (ωj : Regs) (μj : Memory) (ε : Status) (ω' : Regs) (μ' : Memory)
    (hI : Inv j ωj μj) (hx : FreeExit blob j ωj μj ε ω' μ') : ε = .halt ∧ ω'[8] = 0 := by
  obtain ⟨h0, hpc⟩ := hI
  have hpc' : j = 0 ∨ j = 3 ∨ j = 6 := by omega
  cases hx with
  | invalid hd => rw [deblob_eq j hpc'] at hd; cases hd
  | step hP hs hne =>
    rw [deblob_eq j hpc'] at hP
    cases hP
    rcases hpc with rfl | rfl | ⟨rfl, h8⟩
    · obtain ⟨v, hv⟩ := step0 ωj μj
      rw [hv] at hs; cases hs; exact absurd rfl hne
    · rw [step3] at hs; cases hs; exact absurd rfl hne
    · rw [step6 ωj μj h0] at hs
      cases hs
      simp [h8]

/-- **For every initial register file with ω₀ = 2^32 − 2^16, every memory and every amount of gas,
    the countdown program either runs out of gas or halts with ω₈ = 0.** -/
theorem countdown_spec (ω : Regs) (μ : Memory) (gas : UInt64) (ch : Bool) (h0 : ω[0] = haltAddr)
    (hno : (psi blob 0 gas ch ω μ).status ≠ .oog) :
    (psi blob 0 gas ch ω μ).status = .halt ∧ (psi blob 0 gas ch ω μ).regs[8] = 0 := by
  obtain ⟨e, hrun, -⟩ := psi_freeRun hno
  exact FreeRun.of_invariant Inv (fun ε ω' _ => ε = .halt ∧ ω'[8] = 0) inv_step inv_exit
    ⟨h0, Or.inl rfl⟩ hrun

/-! ### Code facts (`PVM.Logic.Code`) for the same blob, checked by the kernel -/

def facts : List CodeFact :=
  [.instr 0 (.twoRegImm .addImm64 8 8 (UInt64.ofNat (2 ^ 64 - 1))) 3,
   .instr 3 (.regImmOffset .branchNeImm 8 0 0) 6,
   .instr 6 (.regImm .jumpInd 0 0) 8,
   .blockStart 0 true, .blockStart 3 false, .jumpTableSize 0]

example : checkCode blob facts = true := by decide +kernel
-- A wrong fact is rejected: the instruction at 3 does not continue at 5.
example : checkCode blob [.instr 3 (.regImmOffset .branchNeImm 8 0 0) 5] = false := by decide +kernel
-- From the check: deblob succeeds at 3 and decodes the branch there.
example : ∃ P, deblob blob 3 = some P ∧ P.decode 3 = some (.regImmOffset .branchNeImm 8 0 0) := by
  obtain ⟨P, hP⟩ := checkCode_sound (show checkCode blob facts = true by decide +kernel)
  obtain ⟨h1, h2, _⟩ := hP.instr (i := 3) (ins := .regImmOffset .branchNeImm 8 0 0) (n := 6)
    (by simp [facts])
  exact ⟨P, h1, h2⟩

end PVM.Tests.Countdown
