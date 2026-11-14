import Services.Bootstrap.Encode.HeapPad
import Services.Bootstrap.Encode.VariantsVec

/-!
# `VecSrc` from the allocator's context

The heap octets `VecSrc q n` of a `Vec<u8>` field (`Encode.VariantsVec`), and the side condition
0 < n → 65536 ≤ q of `heapD` and the arms, from `HeapPad.pad_readable`: for the data address q of an
allocated chunk c holding the n octets, every address of the stretch is readable and in
[65536, 2^32), unless c is the heap's last chunk and the octets leave fewer than 24 of it unused.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Encode.HeapPad

/-- **`VecSrc` is readable for a `Vec` in an allocated chunk.** -/
theorem vecSrc_heap {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true)
    {q n : Nat} (hq : c.addr + 32 = q) (hn : n ≤ 32 * (c.size - 1))
    (hlast : c.addr + 32 * c.size < s.base + 1073741824 ∨ n + 24 ≤ 32 * (c.size - 1)) :
    (0 < n → 65536 ≤ q) ∧ ∀ a, VecSrc q n a → 65536 ≤ a ∧ a < 4294967296 ∧ μ.readable a = true := by
  obtain ⟨h1, h2⟩ := pad_readable H hc hu hq hn hlast
  exact ⟨fun _ => h1, fun a ⟨_, ha1, ha2⟩ => h2 a ha1 ha2⟩

end Services.Bootstrap.Encode.Enc
