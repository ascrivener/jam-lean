import Services.Witness
import Services.Witness.Prefix

/-!
# Results about specific services' deployed code

Built on `JAM`; nothing in `PVM` or `JAM` depends on this library.

* `Services.Witness` — the witness bounty-market service: its accumulate is confined to its own
  account, and its refine exports nothing.
* `Services.Witness.Prefix` — generated: the first 39 steps of witness's refine, proved
  symbolically from code facts that `checkCode` checks against the blob.
-/
