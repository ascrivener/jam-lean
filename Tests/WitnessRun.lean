import JAM

/-!
# `lake build witnessrun`: the real witness binary, run by the model

Runs Ψ_R (`JAM.psiR`) on the vendored `services/witness/witness-service.jam` for work items whose
payload does not decode as a witness `Op`, and checks the output is
ℰ(`Verified::Rejected(Rejection::BadPayload)`) = [12, 0], with no exports.

This is a test, not a proof: it runs compiled code on fixed inputs. It checks that the model
executes real compiled Rust (argument decoding, `fetch`, `grow_heap`, the allocator, SCALE
decoding and encoding, `core::fmt` for the log line, and the `log` call the paper does not define)
the way the service's authors expect. The ∀-quantified statement is the goal of the symbolic proof
described in the README.
-/

open PVM JAM

def mkItem (h : List UInt8) (sid : Nat) (y : List UInt8) : WorkItem where
  service := sid
  codeHash := ⟨h.toArray⟩
  payload := ⟨y.toArray⟩
  refineGasLimit := 1000000000
  accumulateGasLimit := 0
  exportCount := 0
  importSegments := []
  extrinsics := []

def ctx0 : RefineContext where
  anchorHash := ⟨#[]⟩
  anchorSlot := 0
  anchorStateRoot := ⟨#[]⟩
  anchorAccOutLog := ⟨#[]⟩
  lookupAnchorHash := ⟨#[]⟩
  lookupAnchorSlot := 10
  lookupAnchorStateRoot := ⟨#[]⟩

def mkPkg (h : List UInt8) (sid n : Nat) (w : WorkItem) : WorkPackage where
  authToken := ⟨#[]⟩
  authCodeHost := sid
  authCodeHash := ⟨h.toArray⟩
  authConfig := ⟨#[]⟩
  context := ctx0
  items := List.replicate n w

/-- (core, item index, service id, payload): payloads that are empty, start with a tag ≥ 12, or
    are a valid tag with the rest missing. -/
def cases : List (Nat × Nat × Nat × List UInt8) :=
  [(3, 0, 7, []), (3, 0, 7, [12]), (3, 0, 7, [255, 1, 2, 3]), (3, 0, 7, [0]),
   (200, 5, 70000, [255]), (3, 0, 2 ^ 31, [99]), (3, 0, 7, List.replicate 5000 255)]

def main (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile (args.headD "services/witness/witness-service.jam")
  let h := (Blake2b.hash256 bytes).toList
  let mut ok := true
  for (c, i, sid, y) in cases do
    let acct : ServiceAccount :=
      { codeHash := h, balance := 0, minAccGas := 0, minMemoGas := 0,
        preimages := Std.ExtTreeMap.ofList [(h, bytes.toList)],
        requests := Std.ExtTreeMap.ofList [((h, bytes.size), [0])] }
    let r := psiR .tiny (Std.ExtTreeMap.ofList [(sid, acct)]) c i (mkPkg h sid (i + 1) (mkItem h sid y))
      [] (List.replicate (i + 1) []) (List.replicate (i + 1) []) 0
    let out := match r.result with | .ok b => some b.toList | _ => none
    let pass := out == some [12, 0] && r.exports.isEmpty
    ok := ok && pass
    IO.println s!"c={c} i={i} s={sid} |y|={y.length} (first octet {y.head?}): output {out}, gas {r.gasUsed}: {if pass then "ok" else "FAIL"}"
  IO.println (if ok then "witnessrun: every malformed payload gives Rejected(BadPayload)" else "witnessrun: FAILED")
  return if ok then 0 else 1
