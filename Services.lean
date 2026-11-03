import Services.Witness
import Services.Witness.Code
import Services.Witness.Memcpy
import Services.Witness.DecodeU32
import Services.Witness.Prefix

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
* `Services.Witness.Prefix` — generated: the first 702 steps of witness's refine, proved
  symbolically from those code facts.
-/
