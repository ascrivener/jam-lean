import Services.Witness
import Services.Witness.Code
import Services.Witness.Memcpy
import Services.Witness.DecodeU32
import Services.Witness.DecodeC
import Services.Bootstrap.Code
import Services.Bootstrap.Memcpy
import Services.Bootstrap.PrefixC
import Services.Bootstrap.Prefix
import Services.Bootstrap.CodeOk
import Services.Bootstrap.CodeX
import Services.Bootstrap.CodeXOk
import Services.Bootstrap.BParams
import Services.Bootstrap.Reader
import Services.Bootstrap.DecodeU32
import Services.Bootstrap.DecodeU16
import Services.Bootstrap.MemcpyBig
import Services.Bootstrap.Memzero
import Services.Bootstrap.ReaderBig
import Services.Bootstrap.BTail1
import Services.Bootstrap.BTail2
import Services.Bootstrap.BTail3
import Services.Bootstrap.BTail4
import Services.Bootstrap.BTail5
import Services.Bootstrap.BTail6
import Services.Bootstrap.BTail7
import Services.Bootstrap.BTail8
import Services.Bootstrap.Glue
import Services.Bootstrap.EmptyPayload
import Services.Bootstrap.PsiREmpty
import Services.Bootstrap.GlueY
import Services.Bootstrap.GlueY2
import Services.Bootstrap.OTail
import Services.Bootstrap.VTail1
import Services.Bootstrap.VTail2
import Services.Bootstrap.VTail3
import Services.Bootstrap.VTail4
import Services.Bootstrap.VTail5
import Services.Bootstrap.VTail6
import Services.Bootstrap.VTail7
import Services.Bootstrap.VTail8
import Services.Bootstrap.NoInstrArgs
import Services.Bootstrap.NoInstrHead
import Services.Bootstrap.NoInstrFinish
import Services.Bootstrap.NoInstrTail1
import Services.Bootstrap.NoInstrTail2
import Services.Bootstrap.NoInstrTail3
import Services.Bootstrap.NoInstrTail4
import Services.Bootstrap.NoInstrTail5
import Services.Bootstrap.NoInstrTail6
import Services.Bootstrap.NoInstrTail7
import Services.Bootstrap.NoInstrTail8
import Services.Bootstrap.NoInstr
import Services.Bootstrap.DecodeLoop
import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.Decode.Hash
import Services.Bootstrap.Decode.Fixed
import Services.Bootstrap.Decode.HashU64
import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.Decode.Upgrade
import Services.Bootstrap.Decode.Lookup
import Services.Bootstrap.Decode.Transfer
import Services.Bootstrap.Decode.Loop
import Services.Bootstrap.Decode.Elems
import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.Decode.AllocOk
import Services.Bootstrap.Decode.LookedUp
import Services.Bootstrap.Decode.VecEmpty
import Services.Bootstrap.Decode.Provide
import Services.Bootstrap.Decode.RandomStorage
import Services.Bootstrap.Decode.Bless
import Services.Bootstrap.Decode.Designate
import Services.Bootstrap.Decode.VecU8Small
import Services.Bootstrap.Decode.LookedUpSmall
import Services.Bootstrap.Decode.VecU8Loop
import Services.Picoalloc.Model
import Services.Picoalloc.Invariant
import Services.Picoalloc.FreeLists
import Services.Picoalloc.ListFacts
import Services.Picoalloc.Alloc
import Services.Picoalloc.Free
import Services.Picoalloc.Realloc
import Services.Picoalloc.Init
import Services.Picoalloc.First
import Services.Picoalloc.AllocAlign
import Services.Bootstrap.Alloc.Rep
import Services.Bootstrap.Alloc.Arith
import Services.Bootstrap.Alloc.Register
import Services.Bootstrap.Alloc.RegisterRep
import Services.Bootstrap.Alloc.FreeNext
import Services.Bootstrap.Alloc.UnregisterRep
import Services.Bootstrap.Alloc.FreePrev
import Services.Bootstrap.Alloc.Stages
import Services.Bootstrap.Alloc.StageA
import Services.Bootstrap.Alloc.FreeImpl
import Services.Bootstrap.Alloc.FreeRefines
import Services.Bootstrap.Alloc.Dealloc
import Services.Bootstrap.Alloc.AllocPro
import Services.Bootstrap.Alloc.AllocFind
import Services.Bootstrap.Alloc.AllocSearch
import Services.Bootstrap.Alloc.AllocSplit
import Services.Bootstrap.Alloc.AllocUnreg
import Services.Bootstrap.Alloc.AllocWrite
import Services.Bootstrap.Alloc.AllocRight
import Services.Bootstrap.Alloc.AllocTail
import Services.Bootstrap.Alloc.AllocImpl
import Services.Bootstrap.Alloc.AllocRefines
import Services.Bootstrap.Alloc.AllocWrap
import Services.Bootstrap.Alloc.AllocGrow
import Services.Bootstrap.Alloc.AllocGrowMid
import Services.Bootstrap.Alloc.AllocGrowImpl
import Services.Bootstrap.Alloc.AllocGrowRefines
import Services.Bootstrap.Alloc.AllocInit
import Services.Bootstrap.Alloc.AllocWrapGrow
import Services.Bootstrap.Alloc.AllocFirst
import Services.Bootstrap.Alloc.AllocFailModel
import Services.Bootstrap.Alloc.AllocFailSteps
import Services.Bootstrap.Alloc.AllocFailGrow
import Services.Bootstrap.Alloc.AllocFailRefines
import Services.Bootstrap.Alloc.AllocAlignSteps
import Services.Bootstrap.Alloc.AllocAlignImpl
import Services.Bootstrap.Alloc.AllocAlignRefines
import Services.Witness.Prefix
import Services.Witness.EmptyTail
import Services.Witness.Front1
import Services.Witness.Front2
import Services.Witness.Front3
import Services.Witness.Front4
import Services.Witness.Args
import Services.Witness.ErrTail
import Services.Witness.BadPayload
import Services.Witness.Halt
import Services.Witness.Lift
import Services.Witness.PsiRLift
import Services.Witness.PsiR
import Services.Witness.EFront3
import Services.Witness.EmptyPayload
import Services.Witness.PsiREmpty
import Services.Witness.Blob
import Services.Witness.CodeOk
import Services.Witness.Rejects
import Services.Witness.Confined
import Services.Bootstrap.Alloc.ReallocEntry
import Services.Bootstrap.Alloc.ReallocShrink
import Services.Bootstrap.Alloc.ReallocReg
import Services.Bootstrap.Alloc.ReallocStages
import Services.Bootstrap.Alloc.ReallocImpl
import Services.Bootstrap.Alloc.ReallocRefines
import Services.Bootstrap.Alloc.ReallocInplace
import Services.Bootstrap.Alloc.ReallocGrow
import Services.Bootstrap.Alloc.ReallocGrowUnreg
import Services.Bootstrap.Alloc.ReallocGrowReg
import Services.Bootstrap.Alloc.ReallocGrowStages
import Services.Bootstrap.Alloc.ReallocGrowImpl
import Services.Bootstrap.Alloc.ReallocGrowRefines
import Services.Bootstrap.Alloc.ReallocZero
import Services.Bootstrap.Alloc.ReallocWrap
import Services.Bootstrap.Alloc.ReallocGrowHeap
import Services.Bootstrap.Alloc.ReallocGrowPost
import Services.Bootstrap.Alloc.ReallocGrowHeapImpl
import Services.Bootstrap.Alloc.ReallocGrowHeapRefines
import Services.Bootstrap.Alloc.ReallocFallback
import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Alloc.ReallocFallbackPre
import Services.Bootstrap.Alloc.ReallocFallbackRefines
import Services.Bootstrap.Alloc.ReallocFallbackCopy
import Services.Bootstrap.Alloc.ReallocFallbackAlloc
import Services.Bootstrap.Alloc.ReallocFallbackGrowFail
import Services.Bootstrap.Alloc.ReallocFallbackHeap
import Services.Bootstrap.Alloc.ReallocFallbackWrap
import Services.Bootstrap.Alloc.ReallocCases
import Services.Bootstrap.Alloc.Pages

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
* `Services.Witness.ErrTail` — generated (`genwitnesssteps cut 74620 ErrTail 0 1542 every=16
  out`): the 1542 steps of the path witness's refine takes after a bad payload (pc 74620, reached
  for an empty payload or a tag ≥ 12), for every payload of 1 to 15 octets, cut into 97 segments of
  at most 16 steps (`ErrTail/S0` … `S96`). The state at each cut is a structure (`ErrTail/St`:
  the registers, octets and page access the rest of the path reads), each segment proves
  `Stₖ → ∃ run, Stₖ₊₁`, and `chain` composes them by transitivity. Each segment's two
  declarations fit one refine of witness-lean's on-chain check.
* `Services.Witness.PsiR` — **witness's Ψ_R rejects a payload with a bad tag** (`psiR_badTag`): for
  every core index c < 2^16, item index i < 2^16, service id < 2^32 and payload of 1 to 15 octets
  whose first octet is at least 12, Ψ_R's result is ℰ(`Rejected(BadPayload)`) = [12, 0], or ∞.
  From `BadPayload.run_badTag` through `PsiRLift.psiR_of_run` (Ψ_R's code lookup and arguments,
  Y's start) and `Lift.psiM_of_run` (`psiM_of_freeRunH`, the halting step `Halt.halt_43609`).
* `Services.Witness.BadPayload` — witness's refine on a payload with a bad tag, end to end
  (`run_badTag`): the prefix, the decodes, the front segments, the payload copy and the error
  tail chained with `chase`, from Y's registers to the halt with [12, 0], for every input width.
* `Services.Witness.EmptyTail` — the same for the empty payload, whose path from pc 74620
  differs: 1445 steps (91 segments) to the same halting step and output [12, 0], here at
  ω₇ = 206752 (`genwitnesssteps cut0`).
* `Services.Witness.EFront3`, `Services.Witness.EmptyPayload` — the empty payload's front end
  (after the `u32` decode of |y| = 0, to `Op::decode`'s error jump) and its run end to end
  (`run_empty`), from Y's registers to the halt with [12, 0] at ω₇ = 206752.
* `Services.Witness.PsiREmpty` — **witness's Ψ_R rejects the empty payload** (`psiR_empty`), and
  **milestone A′** (`psiR_rejects`): for every c < 2^16, i < 2^16, service id < 2^32 and payload
  that is empty or of 1 to 15 octets with first octet ≥ 12, Ψ_R's result is [12, 0] or ∞; and
  `psiR_rejects_exact`: with a refine gas limit of at least `PsiR.gasBound` (about 3.9 · 10⁷) and
  every block costing at most 7761 gas (`checkMaxBlockCost`, checked by `witnesscheck`), exactly
  [12, 0].
* `Services.Witness.Prefix` — generated: the first 702 steps of witness's refine, proved
  symbolically from those code facts.
* `Services.Witness.Front1` … `Front4` — generated segment theorems for the code between the
  summarized calls of witness's front end (after the `u32` decodes of i, s and |y|, through the
  allocator, and from the payload copy to `Op::decode`'s error jump at 74620), for every input
  width, with the payload length Y, the tag T ≥ 12, the service id S and the reader position Q
  symbolic. `Front1` and `Front2` (5 and 14 steps) are `genwitnesssteps segx` segments; `Front3`
  (275 steps, 18 segments) and `Front4` (68 steps, 5 segments) are `genwitnesssteps cut … frame`
  chains, whose `run` states what a `segx` segment would.
* `Services.Bootstrap.Code`, `.Prefix`, `.Memcpy` — the same tooling on a second service, Parity's
  bootstrap service (`services/bootstrap`): its code facts (`lake build bootstrapcheck`), the
  first 600 steps of its refine with what they leave (`prefix_from_Y`, `PrefixPost`), and
  `memcpy_small`. The bootstrap blob has witness's `memcpy` at another address, so this is
  witness's proof with the pcs moved (`genwitnesssteps --service bootstrap memcpy`).
-/
