import Services.Bootstrap.Prefix
import Services.Bootstrap.CodeX

/-!
# `lake build bootstrapcheck`: the vendored bootstrap blob meets the facts its proofs assume

Checks `checkCode` of the PVM code of `services/bootstrap/jam-bootstrap-service.jam` against
`Services.Bootstrap.Code.facts` and `Services.Bootstrap.CodeX.facts`, and the section sizes and data octets of
`Services.Bootstrap.Prefix.layoutOk`: the hypotheses `Services.Bootstrap.Prefix.prefix_from_Y`
makes about the bytes. Like `witnesscheck`, this runs compiled code over the blob; everything
else is checked by the kernel.
-/

open JAM PVM

def main (args : List String) : IO UInt32 := do
  let path := args.headD "services/bootstrap/jam-bootstrap-service.jam"
  let bytes ← IO.FS.readBinFile path
  let some code := splitMetadata bytes.toList
    | IO.eprintln "not a code preimage ℰ(↕m, c)"; return 1
  let some jb := JamBlob.parse? code
    | IO.eprintln "not a standard program blob"; return 1
  let n := Services.Bootstrap.Code.facts.length
  if !checkCode jb.code Services.Bootstrap.Code.facts then
    IO.eprintln s!"checkCode fails for the {n} facts of Services.Bootstrap.Code"
    return 1
  let nx := Services.Bootstrap.CodeX.facts.length
  if !checkCode jb.code Services.Bootstrap.CodeX.facts then
    IO.eprintln s!"checkCode fails for the {nx} facts of Services.Bootstrap.CodeX"
    return 1
  if !Services.Bootstrap.Prefix.layoutOk jb then
    IO.eprintln "the section sizes differ from Services.Bootstrap.Prefix.layoutOk"
    return 1
  IO.println s!"bootstrapcheck: the blob passes 𝔳_blob, the {n} + {nx} code facts and the section sizes and data octets of Services.Bootstrap.Prefix, so `prefix_from_Y` applies"
  return 0
