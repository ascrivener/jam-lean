import Services.Witness
import Services.Witness.Code
import Services.Witness.Memcpy
import Services.Witness.DecodeU32
import Services.Witness.Prefix
import Services.Witness.ErrTail0
import Services.Witness.ErrTail1
import Services.Witness.ErrTail2
import Services.Witness.ErrTail3
import Services.Witness.ErrTail4
import Services.Witness.ErrTail5
import Services.Witness.ErrTail

/-!
# Results about specific services' deployed code

Built on `JAM`; nothing in `PVM` or `JAM` depends on this library.

* `Services.Witness` — the witness bounty-market service: its accumulate is confined to its own
  account, and its refine exports nothing.
* `Services.Witness.Code` — generated: the code facts the witness proofs use, which `checkCode`
  checks against the blob (`lake build witnesscheck`).
* `Services.Witness.Memcpy` — the compiler's `memcpy` in witness, summarized for fewer than 16
  octets: `memcpy_loop` (the byte loop, by induction) and `memcpy_small` (the whole call).
* `Services.Witness.DecodeU32` — the SDK's `u32` decoder in witness, summarized for every
  encoding ℰ(n) of every n < 2^32 (`decodeU32`): ω₈ = n, the reader advanced past ℰ(n).
* `Services.Witness.ErrTail0` … `ErrTail5` — generated segment theorems: the 1542 steps
  of the path witness's refine takes after a bad payload (pc 74620, reached for an empty payload
  or a tag ≥ 12), each from the facts it reads to the facts it leaves, for every payload of 1 to
  15 octets (`lake exe genwitnesssteps seg 74620 a b ErrTailk`).
* `Services.Witness.ErrTail` — generated: the segments composed (`ErrTail.run`), from pc 74620 to
  the halting step, ending with ω₇ = 206816, ω₈ = 2 and the octets [12, 0] there.
* `Services.Witness.Prefix` — generated: the first 702 steps of witness's refine, proved
  symbolically from those code facts.
-/
