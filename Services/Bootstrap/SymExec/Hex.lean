import Services.Bootstrap.SymExec.Prog

/-!
EXPERIMENTAL (symexec Phase 2, `docs/symexec-spike.md`): a table read at a symbolic index. One
iteration of bootstrap's hex-digit loop (pc 60546 … 60568, see `Services.Bootstrap.Fmt.Hex`)
on a symbolic word w: `load_u8 ω₁₀, [71060 + (w & 15)]` reads the digit table
`0123456789abcdef`, and the octet stored at the cursor is entry w & 15 of the table. Written by
hand.
-/

namespace Services.Bootstrap.SymExec.Hex

open PVM PVM.SymExec

/-- The digit table at 71060. -/
def digits : List Nat := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102]

/-- Named naturals: ρ₀ = w, the word; ρ₁ = A, the digit cursor. -/
def st : Static :=
  { ub := [18446744073709551616, 4294967296], lb := [0, 65536], rd := [(⟨none, 71060⟩, 16)],
    wr := [(⟨some 1, 0⟩, 1)], sep := [] }

def A : Spec :=
  { regs := [(7, .var 1), (8, .const 71060), (9, .var 0), (12, .const 3)]
    cells := (List.range 16).map fun j => (⟨none, (71060 + j : Nat)⟩, 1, .const (digits.getD j 0)) }

/-- The digit of w & 15 at A; the cursor moves down; the digit count goes up. -/
def T : Spec :=
  { regs := [(7, .addr ⟨some 1, -1⟩), (8, .const 71060), (12, .const 4)]
    cells := [(⟨some 1, 0⟩, 1, .tbl digits (.alu2i .andImm (.const 0) (.var 0) 15))] }

theorem ok : check st Services.Bootstrap.SymExec.prog A T [(⟨some 1, 0⟩, 1)] 60546 60568 9 = true := by
  decide +kernel

end Services.Bootstrap.SymExec.Hex
