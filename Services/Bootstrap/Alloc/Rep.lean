import Services.Picoalloc.Init
import PVM.Logic.Words

/-!
# The allocator's state in memory

bootstrap links picoalloc 5.2.0 (through jam-pvm-common) with its allocator at `A0`: the bins'
first free chunks (`u32` × 2432) at `A0`, the heap base (`u64`) at `A0 + 9728`, the bitmap's
secondary words (`u64` × 38) at `A0 + 9736` and primary word at `A0 + 10040`, the allocated space
(`u32`, in units of 32 octets) at `A0 + 10048`, and the mutex at `A0 + 10056`. A chunk's header is
`prev` and `size` (`u32` each) at its address, and for a free chunk `next` and `prevL` after
them.

`Rep μ s` says memory μ holds the model state `s` (`Services/Picoalloc/Model.lean`): its fields,
and the header of every chunk of `s`. Only those headers matter: `chunks s` and the lists are
read from them alone, and the octets inside allocated blocks are the program's.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc

/-- The allocator's address in bootstrap. -/
def A0 : Nat := 196792

/-- **Memory μ holds the allocator state `s`.** -/
structure Rep (μ : Memory) (s : State) : Prop where
  heads : ∀ b, b < binCount → rdN μ (A0 + 4 * b) 4 = s.heads b
  sec : ∀ p, p < 38 → rdN μ (A0 + 9736 + 8 * p) 8 = s.secondary p
  pri : rdN μ (A0 + 10040) 8 = s.primary
  base : rdN μ (A0 + 9728) 8 = s.base
  alloc : rdN μ (A0 + 10048) 4 = s.allocated
  prev : ∀ c ∈ chunks s, rdN μ c.addr 4 = (s.hdr c.addr).prev
  size : ∀ c ∈ chunks s, rdN μ (c.addr + 4) 4 = (s.hdr c.addr).size
  next : ∀ c ∈ chunks s, c.used = false → rdN μ (c.addr + 8) 4 = (s.hdr c.addr).next
  prevL : ∀ c ∈ chunks s, c.used = false → rdN μ (c.addr + 12) 4 = (s.hdr c.addr).prevL

end Services.Bootstrap.Alloc
