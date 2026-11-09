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


/-- `Rep` at chosen addresses: the fields, the `prev` and `size` of the headers at `H`, and the
    links of those at `F`. The operations' steps go between such states. -/
structure RepAt (μ : Memory) (s : State) (H F : Nat → Prop) : Prop where
  heads : ∀ b, b < binCount → rdN μ (A0 + 4 * b) 4 = s.heads b
  sec : ∀ p, p < 38 → rdN μ (A0 + 9736 + 8 * p) 8 = s.secondary p
  pri : rdN μ (A0 + 10040) 8 = s.primary
  base : rdN μ (A0 + 9728) 8 = s.base
  alloc : rdN μ (A0 + 10048) 4 = s.allocated
  prev : ∀ a, H a → rdN μ a 4 = (s.hdr a).prev
  size : ∀ a, H a → rdN μ (a + 4) 4 = (s.hdr a).size
  next : ∀ a, F a → rdN μ (a + 8) 4 = (s.hdr a).next
  prevL : ∀ a, F a → rdN μ (a + 12) 4 = (s.hdr a).prevL

/-- A read whose octets a write sequence kept is the same read. -/
theorem rdN_frame {μ μ' : Memory} {a n : Nat} (h : ∀ j, j < n → μ'.read (a + j) = μ.read (a + j)) :
    rdN μ' a n = rdN μ a n := by
  unfold rdN; rw [readN_congr2 h]

/-- A heap octet off the headers at `G`: from the end of the allocator's fields (206864) up to the
    stack (2³¹), and outside the first 16 octets (`prev`, `size`, `next`, `prevL`) of each
    header at an address in `G`. -/
def OffHdr (G : Nat → Prop) (a : Nat) : Prop :=
  206864 ≤ a ∧ a < 2147483648 ∧ ∀ h, G h → a < h ∨ h + 16 ≤ a

/-- **The heap's frame**: μ' reads as μ at every heap octet off the headers at `G`. The
    allocator's steps write only its fields, the stack and the headers they touch, so a chunk's
    data (from its address + 32) keeps its octets. -/
def HKeep (μ μ' : Memory) (G : Nat → Prop) : Prop := ∀ a, OffHdr G a → μ'.read a = μ.read a

theorem HKeep.refl (μ : Memory) (G : Nat → Prop) : HKeep μ μ G := fun _ _ => rfl

theorem HKeep.trans {μ μ1 μ2 : Memory} {G : Nat → Prop} (h1 : HKeep μ μ1 G) (h2 : HKeep μ1 μ2 G) :
    HKeep μ μ2 G := fun a ha => (h2 a ha).trans (h1 a ha)

/-- More headers, or headers at addresses below 206864 (outside the heap) dropped. -/
theorem HKeep.mono {μ μ' : Memory} {G G' : Nat → Prop} (h : HKeep μ μ' G)
    (hG : ∀ b, G b → G' b ∨ b + 16 ≤ 206864) : HKeep μ μ' G' := fun a ⟨h1, h2, h3⟩ =>
  h a ⟨h1, h2, fun b hb => by rcases hG b hb with h | h; exact h3 b h; omega⟩

/-- A frame that keeps every octet below 2³¹ outside some written ranges, each inside the
    allocator's fields or a header at `G`, is a heap frame. -/
theorem HKeep.of_low {μ μ' : Memory} {G : Nat → Prop}
    (h : ∀ a, 206864 ≤ a → a < 2147483648 → (∀ b, G b → a < b ∨ b + 16 ≤ a) → μ'.read a = μ.read a) :
    HKeep μ μ' G := fun a ⟨h1, h2, h3⟩ => h a h1 h2 h3

/-! ### The heap frame with the globals

`HKeepG` is `HKeep` with the program's globals below the allocator (196616 … `A0`) also kept: the
allocator's steps write none of them. (The `alloc` wrapper's lock takes the word at 196608, so the
globals start after it.) It implies `HKeep` (`HKeepG.hkeep`). -/

/-- The program's globals below the allocator: from 196616 (after the wrapper's lock word at 196608,
    the start of the read-write data) up to `A0`. -/
def Glob (a : Nat) : Prop := 196616 ≤ a ∧ a < 196792

/-- `OffHdr`, or a global below the allocator off the headers at `G`. -/
def OffHdrG (G : Nat → Prop) (a : Nat) : Prop :=
  (Glob a ∨ 206864 ≤ a) ∧ a < 2147483648 ∧ ∀ h, G h → a < h ∨ h + 16 ≤ a

/-- **The heap frame with the globals**: μ' reads as μ at every heap octet and every global below
    the allocator off the headers at `G`. -/
def HKeepG (μ μ' : Memory) (G : Nat → Prop) : Prop := ∀ a, OffHdrG G a → μ'.read a = μ.read a

theorem HKeepG.hkeep {μ μ' : Memory} {G : Nat → Prop} (h : HKeepG μ μ' G) : HKeep μ μ' G :=
  fun a ⟨h1, h2, h3⟩ => h a ⟨Or.inr h1, h2, h3⟩

/-- The globals below the allocator are kept, when no header at `G` meets them. -/
theorem HKeepG.glob {μ μ' : Memory} {G : Nat → Prop} (h : HKeepG μ μ' G)
    (hG : ∀ b, G b → b + 16 ≤ 196616 ∨ 196792 ≤ b) : ∀ a, Glob a → μ'.read a = μ.read a :=
  fun a ha => h a ⟨Or.inl ha, by unfold Glob at ha; omega, fun b hb => by
    unfold Glob at ha; rcases hG b hb with h | h <;> omega⟩

theorem HKeepG.refl (μ : Memory) (G : Nat → Prop) : HKeepG μ μ G := fun _ _ => rfl

theorem HKeepG.trans {μ μ1 μ2 : Memory} {G : Nat → Prop} (h1 : HKeepG μ μ1 G) (h2 : HKeepG μ1 μ2 G) :
    HKeepG μ μ2 G := fun a ha => (h2 a ha).trans (h1 a ha)

/-- More headers, or headers below the globals (196616) or inside the allocator's fields (196792 …
    206864) dropped. -/
theorem HKeepG.mono {μ μ' : Memory} {G G' : Nat → Prop} (h : HKeepG μ μ' G)
    (hG : ∀ b, G b → G' b ∨ b + 16 ≤ 196616 ∨ (196792 ≤ b ∧ b + 16 ≤ 206864)) : HKeepG μ μ' G' :=
  fun a ⟨h1, h2, h3⟩ =>
    h a ⟨h1, h2, fun b hb => by rcases hG b hb with h | h; exact h3 b h; unfold Glob at h1; omega⟩

/-- A frame that keeps every global below the allocator and every octet from 206864 below 2³¹
    outside some written ranges, each inside the allocator's fields or a header at `G`. -/
theorem HKeepG.of_low {μ μ' : Memory} {G : Nat → Prop}
    (h : ∀ a, (196616 ≤ a ∧ a < 196792 ∨ 206864 ≤ a) → a < 2147483648 → (∀ b, G b → a < b ∨ b + 16 ≤ a) →
      μ'.read a = μ.read a) :
    HKeepG μ μ' G := fun a ⟨h1, h2, h3⟩ => h a h1 h2 h3

end Services.Bootstrap.Alloc
