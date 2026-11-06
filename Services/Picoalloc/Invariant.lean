import Services.Picoalloc.Model

/-!
# picoalloc's heap invariant

The heap, read from the state: the chunks, walked from the base by their sizes, partition the
address space `[base, base + 32 · maxSize)`; each records its predecessor's size; no two free
chunks are adjacent; each free chunk is in the free list of its bin (`binDown` of its size), the
lists are doubly linked through the headers, and the bitmap marks exactly the non-empty bins.

`Chunks s` is that partition as a list (address, size, used), and `WF s` the invariant. The
contract of the operations (`Contract.lean`) is stated over `Chunks`.
-/

namespace Picoalloc

/-- A chunk: its address, its size in units, and whether it is allocated. -/
structure Chunk where
  addr : Nat
  size : Nat
  used : Bool
deriving DecidableEq, Repr

/-- The chunks from `a` on, at most `fuel` of them, walked by the size words, until `limit`. -/
def walk (s : State) (a limit : Nat) : Nat → List Chunk
  | 0 => []
  | fuel + 1 =>
    if a ≥ limit then []
    else
      let w := (s.hdr a).size
      ⟨a, wordSize w, wordUsed w⟩ :: walk s (a + 32 * wordSize w) limit fuel

/-- The end of the address space. -/
def State.top (s : State) : Nat := s.base + 32 * maxSize

/-- The walk's bound on the number of chunks (each is at least one unit). -/
@[irreducible] def walkFuel : Nat := maxSize

/-- The heap's chunks, from the base. -/
@[irreducible] def chunks (s : State) : List Chunk := walk s s.base s.top walkFuel

/-- The chunks are contiguous from `a`, each of positive size, and end exactly at `limit`. -/
def Tiles : Nat → Nat → List Chunk → Prop
  | a, limit, [] => a = limit
  | a, limit, c :: cs => c.addr = a ∧ 0 < c.size ∧ Tiles (a + 32 * c.size) limit cs

/-- No two adjacent chunks are free. -/
def Coalesced : List Chunk → Prop
  | c :: d :: cs => (c.used || d.used) ∧ Coalesced (d :: cs)
  | _ => True

/-- Each chunk after the first records its predecessor's size. -/
def PrevOk (s : State) : List Chunk → Prop
  | c :: d :: cs => (s.hdr d.addr).prev = c.size ∧ PrevOk s (d :: cs)
  | _ => True

/-- `l` is the list linked from `a` through the `next` fields, ending at 0. -/
def Linked (s : State) : Nat → List Nat → Prop
  | a, [] => a = 0
  | a, x :: xs => a = x ∧ x ≠ 0 ∧ Linked s (s.hdr x).next xs

/-- `l`'s `prevL` fields point back: the first to `p`, each other to its predecessor. -/
def BackLinked (s : State) : Nat → List Nat → Prop
  | _, [] => True
  | p, x :: xs => (s.hdr x).prevL = p ∧ BackLinked s x xs

/-- The free lists: each bin's list, linked from its head and back, without repeats, holds
    exactly the free chunks of that bin; the bitmap marks the non-empty bins. -/
structure ListsOk (s : State) (cs : List Chunk) : Prop where
  lists : ∀ b, b < binCount → ∃ l, Linked s (s.heads b) l ∧ BackLinked s 0 l ∧ l.Nodup ∧
    ∀ a, a ∈ l ↔ ∃ c ∈ cs, c.addr = a ∧ c.used = false ∧ binDown c.size = b
  bits : ∀ b, b < binCount → ((s.secondary (b / 64)).testBit (b % 64) ↔ s.heads b ≠ 0)
  prim : ∀ p, p < 38 → (s.primary.testBit p ↔ s.secondary p % 2 ^ 64 ≠ 0)
  words : ∀ p, p < 38 → s.secondary p < 2 ^ 64
  primW : s.primary < 2 ^ 38

/-- The parts of the invariant about the chunk list, named (a `structure` field applying these
    recursive predicates to `chunks s` directly is slow to elaborate). -/
@[irreducible] def TilesOk (s : State) : Prop := Tiles s.base s.top (chunks s)
@[irreducible] def CoalOk (s : State) : Prop := Coalesced (chunks s)
@[irreducible] def PrevsOk (s : State) : Prop := PrevOk s (chunks s)
@[irreducible] def ListsOk' (s : State) : Prop := ListsOk s (chunks s)
@[irreducible] def SpaceOk (s : State) : Prop := ∀ c ∈ chunks s, (c.used → c.addr + 32 * c.size ≤ s.base + 32 * s.allocated) ∧
    c.addr + 32 ≤ s.base + 32 * s.allocated

/-- **The heap invariant** of an initialized allocator. -/
def WF (s : State) : Prop :=
  s.base ≠ 0 ∧ s.base % 32 = 0 ∧ s.top < 2 ^ 32 ∧ TilesOk s ∧ CoalOk s ∧ PrevsOk s ∧ ListsOk' s ∧
    SpaceOk s

end Picoalloc
