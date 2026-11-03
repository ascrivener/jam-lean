import Services.Witness.Code

namespace Services.Witness

open PVM Services.Witness.Code

/-- **The halting step** at 43609: `jump_ind ω₀` with ω₀ = 2^32 − 2^16 halts (GP §A.5.1:
    djump to 2^32 − 2^16 is ∎), leaving registers and memory as they are. -/
theorem halt_43609 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 4294901760) : FreeExit p 43609 ω μ .halt ω μ := by
  have hd := d_43609 (p := p) (P := P)
  have hs : P.freeStep 43609 ω μ = (.halt, 43609, ω, μ) := by
    have h0' : ω.get 0 = UInt64.ofNat 4294901760 := h0
    simp [Program.freeStep, hd.2.1, Program.exec, h0', Program.djump, Program.finalState,
      memoryException, two32]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

end Services.Witness
