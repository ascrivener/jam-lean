import Services.Witness
import Services.Witness.Code
import Services.Witness.Memcpy
import Services.Witness.DecodeU32
import Services.Witness.DecodeC
import Services.Bootstrap.Code
import Services.Bootstrap.Memcpy
import Services.Bootstrap.Prefix
import Services.Witness.Prefix
import Services.Witness.ErrTail0
import Services.Witness.ErrTail1
import Services.Witness.ErrTail2
import Services.Witness.ErrTail3
import Services.Witness.ErrTail4
import Services.Witness.ErrTail5
import Services.Witness.ErrTail
import Services.Witness.EmptyTail0
import Services.Witness.EmptyTail1
import Services.Witness.EmptyTail2
import Services.Witness.EmptyTail3
import Services.Witness.EmptyTail4
import Services.Witness.EmptyTail5
import Services.Witness.EmptyTail
import Services.Witness.Front1
import Services.Witness.Front2
import Services.Witness.Front3
import Services.Witness.Front4

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
* `Services.Witness.DecodeC` — witness's inline decode of the core index c (from pc 43276, step
  702), summarized for every c < 2^16 (`decodeC`): the reader advanced past ℰ(c) at ω₁ + 16 and
  the call to the `u32` decoder. (Witness rejects c ≥ 2^16, which no refine call passes.)
* `Services.Witness.ErrTail0` … `ErrTail5` — generated segment theorems: the 1542 steps
  of the path witness's refine takes after a bad payload (pc 74620, reached for an empty payload
  or a tag ≥ 12), each from the facts it reads to the facts it leaves, for every payload of 1 to
  15 octets (`lake exe genwitnesssteps seg 74620 a b ErrTailk`).
* `Services.Witness.ErrTail` — generated: the segments composed (`ErrTail.run`), from pc 74620 to
  the halting step, ending with ω₇ = 206816, ω₈ = 2 and the octets [12, 0] there.
* `Services.Witness.EmptyTail0` … `EmptyTail5`, `Services.Witness.EmptyTail` — the same for the
  empty payload, whose path from pc 74620 differs: 1445 steps to the same halting step and
  output [12, 0], here at ω₇ = 206752 (`genwitnesssteps seg0` / `chain0`).
* `Services.Witness.Prefix` — generated: the first 702 steps of witness's refine, proved
  symbolically from those code facts.
* `Services.Witness.Front1` … `Front4` — generated segment theorems for the code between the
  summarized calls of witness's front end (after the `u32` decodes of i, s and |y|, through the
  allocator, and from the payload copy to `Op::decode`'s error jump at 74620), for every input
  width, with the payload length Y, the tag T ≥ 12, the service id S and the reader position Q
  symbolic (`genwitnesssteps segx`).
* `Services.Bootstrap.Code`, `.Prefix`, `.Memcpy` — the same tooling on a second service, Parity's
  bootstrap service (`services/bootstrap`): its code facts (`lake build bootstrapcheck`), the
  first 600 steps of its refine with what they leave (`prefix_from_Y`, `PrefixPost`), and
  `memcpy_small`. The bootstrap blob has witness's `memcpy` at another address, so this is
  witness's proof with the pcs moved (`genwitnesssteps --service bootstrap memcpy`).
-/
