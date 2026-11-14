# Refine's output encoder (`Instruction::encode_to`, `Vec<Instruction>::encode`)

These proofs show that refine's output encoder (entry 30145) appends GP v0.8.0's encoding (Appendix C) of
each output instruction, and that the whole vector is encoded as ℰ(n) followed by the elements.

## Contracts
- **`EncOk` (`Dispatch.lean`):** one element whose encoding reads only its 232-octet slot. Its stack frame
  is [F − 136, F).
- **`EncOkM` (`EncM.lean`):** `EncOk` for elements that also read memory outside the slot (`Src`), with the
  same frame.
- **`EncOkMD D` (`EncMD.lean`):** `EncOkM` with stack frame [F − D, F). Arms that call the length prefix
  (30977) reach F − 192; Provide's inline `[u8]` helper (3716) reaches F − 232. `EncOkM.toMD232` lifts every
  `EncOkM` arm, and `encode_okMD(_big)` run the loop with D = 232 per element call.

## Obligations left to the top level
These are hypotheses of the arms that refine's top-level proof (`Refine/`, T1) must **discharge**. They
must not be passed up as assumptions of the final theorem.

1. **`hlast` (heap padding at the heap's top).** Every heap source of a Vec arm is read through
   `extend_from_slice`, whose `memcpy` lemmas need 24 octets of readable padding on each side
   (`VecSrc q n`). `pad_readable` / `vecSrc_heap` (`HeapPad.lean`, `VecSrcHeap.lean`) discharge this from
   `HeapCtxC` for a used chunk c holding the data, except when c is the heap's last tile:
   `hlast : c.addr + 32·c.size < s.base + 2^30 ∨ n + 24 ≤ 32·(c.size − 1)`.
   It fails only if a used chunk ends exactly at the top of the allocator's 1 GiB region. The page bound
   does not exclude this (4096·pb is far above base + 2^30). The intended discharge is that refine's heap
   use is bounded by the payload's size, so no used chunk reaches the top. An alternative, to be proposed
   first, is an `allocated < 2^25 − 1` field in `HeapCtxC` maintained by the allocator lemmas.
2. **Writer capacity.** `encode_okM_big` / `encode_okMD_big` assume the output buffer holds
   |ℰ(n)| + the elements + 2 octets. Refine allocates exactly 232·n + 6 octets, so the writer's grow path
   (58615/58717 → realloc) must be proved, with an `Exhausts` outcome, before this hypothesis can go.

## Arms not yet proved
- **Provide, Inline shape (17):** needs code facts for 3716–3790, which T1 is regenerating.
- **The Vec arms 0, 5, 11, 12, 13 and 24:** in progress.
