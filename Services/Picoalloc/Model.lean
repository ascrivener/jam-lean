/-!
# picoalloc, as a functional model

The heap allocator of the JAM service SDK (`jam-pvm-common`) is picoalloc 5.2 (`realloc_inplace`
enabled). This is its algorithm as Lean functions, operation by operation, over its state: the
metadata of the `Allocator` struct and the chunk headers in the heap. It is the model the
compiled code is proved to refine; nothing here depends on a binary.

Sizes are in units of 32 octets (`ALLOCATION_GRANULARITY`). Chunk addresses are absolute. A chunk
starts with a one-unit header: the previous chunk's size, then the size word `size << 1 | used`, and,
for a free chunk, its neighbours in its bin's free list. Free chunks are kept in 2432 bins
(`size_to_bin_round_down`), with a two-level bitmap of the non-empty bins.
-/

namespace Picoalloc

/-- `MAX_ALLOCATION_SIZE` and the SDK's `total_space`: 1 GiB, in units. -/
@[irreducible] def maxSize : Nat := 33554432

theorem maxSize_val : maxSize = 33554432 := by unfold maxSize; rfl

/-- The bins' mantissa bits and count (`calculate_optimal_bin_config` for 1 GiB and 4096 bins). -/
def mantissaBits : Nat := 7
def binCount : Nat := 2432

/-- `f` with the value at `a` replaced. -/
def upd {β : Type} (f : Nat → β) (a : Nat) (b : β) : Nat → β := fun x => if x = a then b else f x

theorem upd_self {β : Type} (f : Nat → β) (a : Nat) (b : β) : upd f a b a = b := by simp [upd]
theorem upd_ne {β : Type} (f : Nat → β) {a x : Nat} (b : β) (h : x ≠ a) : upd f a b x = f x := by
  simp [upd, h]

/-- A chunk header (`FreeChunkHeader`; an allocated chunk uses only `prev` and `size`). -/
structure Hdr where
  prev : Nat
  size : Nat
  next : Nat
  prevL : Nat
deriving Inhabited, Repr

/-- The allocator's state: `allocated_space`, `base_address`, the bitmap of non-empty bins, the
    bins' first free chunks, and the headers in the heap by address. -/
structure State where
  allocated : Nat
  base : Nat
  primary : Nat
  secondary : Nat → Nat
  heads : Nat → Nat
  hdr : Nat → Hdr

/-- `ChunkSize`: the size word of a chunk. -/
def sizeWord (size : Nat) (used : Bool) : Nat := 2 * size + if used then 1 else 0
def wordSize (w : Nat) : Nat := w / 2
def wordUsed (w : Nat) : Bool := w % 2 == 1

/-- The position of the highest set bit of a nonzero 32-bit value (`31 − leading_zeros`). -/
def log2 (x : Nat) : Nat := Nat.log2 x

/-- `to_bin_index_generic::<7, ROUND_UP>`. -/
def toBin (roundUp : Bool) (size : Nat) : Nat :=
  if size = 0 then 0
  else if size < 2 ^ mantissaBits then size - 1
  else
    let start := log2 size - mantissaBits
    let exponent := start + 1
    let m0 := (size / 2 ^ start) % 2 ^ mantissaBits
    let m := if roundUp && size % 2 ^ start != 0 then m0 + 1 else m0
    let out := exponent * 2 ^ mantissaBits
    if roundUp then out + m - 1 else (out ||| m) - 1

/-- `size_to_bin_round_down` / `size_to_bin_round_up`, clamped at `MAX_ALLOCATION_SIZE`. -/
def binDown (size : Nat) : Nat := toBin false (min size maxSize)
def binUp (size : Nat) : Nat := toBin true (min size maxSize)

/-- `lowest_set_bit_after`: the lowest set bit of `v` at or after bit `i`, if any. -/
def lowestAfter (v i : Nat) : Option Nat :=
  let after := v / 2 ^ i * 2 ^ i
  if after % 2 ^ 64 = 0 then none
  else (List.range 64).find? (fun b => after.testBit b)

/-- `BitMask::set`. -/
def setBit (s : State) (bin : Nat) : State :=
  { s with secondary := upd s.secondary (bin / 64) (s.secondary (bin / 64) ||| 2 ^ (bin % 64))
           primary := s.primary ||| 2 ^ (bin / 64) }

/-- `BitMask::unset`. -/
def unsetBit (s : State) (bin : Nat) : State :=
  let w := s.secondary (bin / 64) &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin % 64))
  { s with secondary := upd s.secondary (bin / 64) w
           primary := if w = 0 then s.primary &&& ((2 ^ 64 - 1) ^^^ 2 ^ (bin / 64)) else s.primary }

/-- `BitMask::find_first`: the first non-empty bin at or after `bin`. -/
def findFirst (s : State) (bin : Nat) : Option Nat :=
  let p := bin / 64
  let sec := if s.primary.testBit p then lowestAfter (s.secondary p) (bin % 64) else none
  match sec with
  | some b => some (p * 64 + b)
  | none =>
    match lowestAfter s.primary (p + 1) with
    | none => none
    | some p' => (lowestAfter (s.secondary p') 0).map (p' * 64 + ·)

def setHdr (s : State) (a : Nat) (f : Hdr → Hdr) : State :=
  { s with hdr := upd s.hdr a (f (s.hdr a)) }

/-- `unregister_free_space_first_chunk`. -/
def unregisterFirst (s : State) (chunk bin : Nat) : State :=
  let next := (s.hdr chunk).next
  let s := { s with heads := upd s.heads bin next }
  if next = 0 then unsetBit s bin else setHdr s next (fun h => { h with prevL := 0 })

/-- `unregister_free_space`. -/
def unregister (s : State) (chunk bin : Nat) : State :=
  if s.heads bin = chunk then unregisterFirst s chunk bin
  else
    let next := (s.hdr chunk).next
    let prevL := (s.hdr chunk).prevL
    let s := setHdr s prevL (fun h => { h with next := next })
    if next = 0 then s else setHdr s next (fun h => { h with prevL := prevL })

/-- `register_free_space`: a free chunk of `size` units at `chunk`, first in its bin. Returns the
    size for the next chunk's `prev` (or `prev` unchanged when `size` is 0). -/
def register (s : State) (chunk prev size : Nat) : State × Nat :=
  if size = 0 then (s, prev)
  else
    let bin := binDown size
    let next := s.heads bin
    let s := { s with heads := upd s.heads bin chunk }
    let s := setHdr s chunk (fun _ => ⟨prev, sizeWord size false, next, 0⟩)
    let s := if next = 0 then s else setHdr s next (fun h => { h with prevL := chunk })
    (setBit s bin, size)

/-- `register_allocation`. -/
def registerAlloc (s : State) (chunk prev size : Nat) : State :=
  setHdr s chunk (fun h => { h with prev := prev, size := sizeWord size true })

/-- The environment's `expand_memory_until(base, size)`: whether the heap could grow to cover
    `base + 32 · size` octets (the `grow_heap` host call). -/
abbrev Grow := Nat → Nat → Bool

/-- `initialize`: on first use, one free chunk spanning the whole address space at `heapBase`. -/
def init (grow : Grow) (heapBase : Nat) (s : State) : Option State :=
  if s.base ≠ 0 then some s
  else if !grow heapBase 1 then none
  else
    let s := { s with base := heapBase, allocated := 1 }
    let bin := binDown maxSize
    let s := setBit s bin
    let s := setHdr s heapBase (fun _ => ⟨0, sizeWord maxSize false, 0, 0⟩)
    some { s with heads := upd s.heads bin heapBase }

/-- `alloc_impl` (not zeroed): a chunk for `req` units aligned to `align` units, as its data's
    address and the new state. -/
def alloc (grow : Grow) (heapBase : Nat) (align req : Nat) (s : State) : Option (Nat × State) := do
  if align = 0 ∨ align &&& (align - 1) ≠ 0 then none
  let s ← init grow heapBase s
  let minSize := req + 1 + (align - 1)
  if minSize > maxSize then none
  let bin ← (findFirst s (binUp minSize)).orElse (fun _ => findFirst s (binDown minSize))
  let chunk := s.heads bin
  let chunkSize := wordSize (s.hdr chunk).size
  if chunkSize < minSize then none
  let chunkOff := (chunk - s.base) / 32
  let dataOff := (chunkOff + 1 + (align - 1)) / align * align
  let headerOff := dataOff - 1
  let allocChunk := s.base + 32 * headerOff
  let lhs := headerOff - chunkOff
  let rhs := chunkSize - req - lhs - 1
  let endOff := dataOff + req + (if rhs = 0 then 0 else 1)
  let s ← if s.allocated < endOff then
      (if grow s.base endOff then some { s with allocated := endOff } else none)
    else some s
  let prev := (s.hdr chunk).prev
  let s := unregisterFirst s chunk bin
  let (s, prev) := register s chunk prev lhs
  let s := registerAlloc s allocChunk prev (req + 1)
  let next := allocChunk + 32 * (1 + req)
  let (s, prev) := register s next (req + 1) rhs
  let final := next + 32 * rhs
  let s := if final < s.base + 32 * maxSize then setHdr s final (fun h => { h with prev := prev }) else s
  return (allocChunk + 32, s)

/-- `free`'s merge with the previous chunk, if free: the state, the merged chunk, its size and its
    `prev`. -/
def mergePrev (s : State) (chunk size prev : Nat) : State × Nat × Nat × Nat :=
  if chunk ≠ s.base then
    let pc := chunk - 32 * prev
    let pw := (s.hdr pc).size
    if !wordUsed pw then (unregister s pc (binDown (wordSize pw)), pc, size + wordSize pw, (s.hdr pc).prev)
    else (s, chunk, size, prev)
  else (s, chunk, size, prev)

/-- `free`'s merge with the next chunk, if below `T` and free: the state and the merged size. -/
def mergeNext (s : State) (chunk size T : Nat) : State × Nat :=
  if chunk + 32 * size < T then
    if !wordUsed (s.hdr (chunk + 32 * size)).size then
      (unregister s (chunk + 32 * size) (binDown (wordSize (s.hdr (chunk + 32 * size)).size)),
        size + wordSize (s.hdr (chunk + 32 * size)).size)
    else (s, size)
  else (s, size)

/-- `free`'s last step: the merged chunk registered, and the next chunk's `prev`, below `T`. -/
def freeFinal (s : State) (chunk prev size T : Nat) : State :=
  if chunk + 32 * size < T then
    setHdr (register s chunk prev size).1 (chunk + 32 * size) (fun h => { h with prev := (register s chunk prev size).2 })
  else (register s chunk prev size).1

/-- `free`: the chunk of the data at `ptr` becomes free, merged with free neighbours. -/
def free (s : State) (ptr : Nat) : State :=
  let chunk := ptr - 32
  let m := mergePrev s chunk (wordSize (s.hdr chunk).size) (s.hdr chunk).prev
  let n := mergeNext m.1 m.2.1 m.2.2.1 (s.base + 32 * maxSize)
  freeFinal n.1 m.2.1 m.2.2.2 n.2 (s.base + 32 * maxSize)

/-- The usable size of the allocation at `ptr`, in units (`usable_size_impl`). -/
def usable (s : State) (ptr : Nat) : Nat := wordSize (s.hdr (ptr - 32)).size - 1

/-- `shrink_inplace` (for a new size below the current one, nonzero): the chunk keeps `newReq + 1`
    units; the rest, merged with a free next chunk, becomes free. -/
def shrink (s : State) (ptr newReq : Nat) : State :=
  let chunk := ptr - 32
  let newSize := newReq + 1
  let cur := wordSize (s.hdr chunk).size
  if newSize ≥ cur then s
  else
    let s := setHdr s chunk (fun h => { h with size := sizeWord newSize true })
    let n := mergeNext s chunk cur (s.base + 32 * maxSize)
    freeFinal n.1 (chunk + 32 * newSize) newSize (n.2 - newSize) (s.base + 32 * maxSize)

/-- `grow_inplace`: the allocation at `ptr` grows into a free next chunk, if one is large enough;
    the rest of that chunk, if any, stays free. -/
def growInplace (grow : Grow) (s : State) (ptr newReq : Nat) : Option State := do
  let chunk := ptr - 32
  let newSize := newReq + 1
  let cur := wordSize (s.hdr chunk).size
  if cur ≥ newSize then return s
  let endAll := s.base + 32 * maxSize
  let onc := chunk + 32 * cur
  if onc ≥ endAll then none
  let onw := (s.hdr onc).size
  if wordUsed onw then none
  let avail := cur + wordSize onw
  if avail < newSize then none
  let remaining := avail - newSize
  let nnc := chunk + 32 * newSize
  let endOff := (nnc - s.base) / 32 + (if remaining = 0 then 0 else 1)
  let s ← if s.allocated < endOff then
      (if grow s.base endOff then some { s with allocated := endOff } else none)
    else some s
  let s := unregister s onc (binDown (wordSize onw))
  let s := setHdr s chunk (fun h => { h with size := sizeWord newSize true })
  return freeFinal s nnc newSize remaining endAll

/-- `realloc`: the new data address and state, and whether the old data must be copied there
    (`copy_nonoverlapping` of the old usable size, then `free` of the old chunk). -/
def realloc (grow : Grow) (heapBase : Nat) (s : State) (ptr align newReq : Nat) :
    Option (Nat × State × Bool) := do
  let cur := usable s ptr
  if newReq = cur then return (ptr, s, false)
  if newReq = 0 then none
  if newReq < cur then return (ptr, shrink s ptr newReq, false)
  match growInplace grow s ptr newReq with
  | some s' => return (ptr, s', false)
  | none =>
    let (p, s') ← alloc grow heapBase align newReq s
    return (p, free s' ptr, true)

end Picoalloc
