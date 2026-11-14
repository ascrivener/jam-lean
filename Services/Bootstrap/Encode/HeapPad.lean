import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Decode.VecU8Pass

/-!
# The heap octets around an allocated chunk's data are readable

`Vec<u8>::extend_from_slice` (`Writer.extend_ok`, through `memcpy`) is proved for a source at least 24
octets apart from the destination, at 65536 or above and 16 octets below 2^32. An encoder arm that
copies a `Vec`'s n octets from the heap at q states this through its heap octets `Src`, taken as the
padded stretch [q − 24, q + n + 24), and `Src` must be readable. `pad_readable`: for q the data address
of an allocated chunk c (q = c.addr + 32) holding n ≤ 32 · (c.size − 1) octets, the allocator's context
`HeapCtxC` makes every address of the stretch readable and puts it in [65536, 2^32), provided c is not
the last chunk of the heap's 2^30-octet address space or the n octets leave 24 octets of c unused.

The end of the stretch can pass c's end by up to 24 octets. It is then inside the next chunk's
header (each chunk, used or not, has its first unit inside the allocated space, `SpaceOk`), which lies
in the heap's writable pages. When c is the heap's last chunk (it ends at base + 2^30) there is no
next chunk, and the bound proved is only c's own end: hence the alternative `n + 24 ≤ 32 · (c.size − 1)`.
-/

namespace Services.Bootstrap.Encode.HeapPad

open PVM Picoalloc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx

/-- A chunk of a tiling that ends before its limit is followed by a chunk at its end. -/
theorem Tiles.next {a limit : Nat} {cs : List Chunk} (h : Tiles a limit cs) :
    ∀ c ∈ cs, c.addr + 32 * c.size < limit → ∃ d ∈ cs, d.addr = c.addr + 32 * c.size := by
  induction cs generalizing a with
  | nil => simp
  | cons e cs ih =>
    obtain ⟨h1, h2, h3⟩ := h
    intro c hc hlt
    rcases List.mem_cons.mp hc with rfl | hc
    · cases cs with
      | nil => simp [Tiles] at h3; omega
      | cons d cs =>
        obtain ⟨d1, -, -⟩ := h3
        exact ⟨d, by simp, by omega⟩
    · obtain ⟨d, hd, e⟩ := ih h3 c hc hlt
      exact ⟨d, List.mem_cons_of_mem _ hd, e⟩

/-- **The padded stretch around a chunk's data is readable** (see the module doc). -/
theorem pad_readable {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true)
    {q n : Nat} (hq : c.addr + 32 = q) (hn : n ≤ 32 * (c.size - 1))
    (hlast : c.addr + 32 * c.size < s.base + 1073741824 ∨ n + 24 ≤ 32 * (c.size - 1)) :
    65536 ≤ q ∧ ∀ a, q ≤ a + 24 → a < q + n + 24 → 65536 ≤ a ∧ a < 4294967296 ∧ μ.readable a = true := by
  have hwf := H.wf
  obtain ⟨hb1, hb2, hb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in hwf hc hu
  obtain ⟨ph, hph1, hph2, hp, hph3, hph4⟩ := H.pages
  have hb0 := H.hb0
  have hbT := H.hbT
  have hpos : 0 < c.size := by
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    exact (ht.mem_lt c hc).2.2
  have hSb := H.hSb
  have hS1 := H.hS1
  have hst : ∀ a, S0 ≤ a → a < S0 → μ.writable a = true := fun a h1 h2 => by omega
  have hw := HeapPages.wrAt hp hph2 hst
  -- the end of the stretch lies in the allocated space
  have hend : q + n + 24 ≤ s.base + 32 * s.allocated := by
    rcases hlast with hl | hl
    · have ht := hwf.2.2.2.1
      unfold TilesOk at ht
      have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
      obtain ⟨d, hd, hda⟩ := Tiles.next ht c hc (by omega)
      have hsp := hwf.2.2.2.2.2.2.2
      unfold SpaceOk at hsp
      have := (hsp d hd).2
      omega
    · omega
  refine ⟨by omega, fun a h1 h2 => ⟨by omega, by omega, ?_⟩⟩
  exact Memory.readable_of_writable (hw a (Or.inl ⟨by omega, by omega⟩))

end Services.Bootstrap.Encode.HeapPad
