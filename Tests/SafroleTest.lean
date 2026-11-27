import Tests.SafroleHarness
import JamCrypto.Ring

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.SafroleHarness`. -/

open JAM.Tests in
def main (args : List String) : IO UInt32 := do
  let base : System.FilePath := args.headD "vendor/jam-test-vectors/stf/safrole"
  let srs := JamCrypto.Ring.withSelectors
    (← JamCrypto.Ring.Srs.load "JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin")
  let mut code : UInt32 := 0
  -- V of the v0.8.0 chains (davxy/jam-test-vectors README), which size v0.8.0's ring domain.
  for (label, params, validators) in [("tiny", JAM.V080.tiny080, 6), ("full", JAM.V080.full080, 1023)] do
    let dir := base / label
    let mut o : Safrole.Oracle := {}
    for f in ← PVM.Tests.jsonFiles dir do
      match o.add params (← PVM.Tests.readJson f) with
      | .ok o' => o := o'
      | .error e => IO.eprintln s!"oracle {f}: {e}"; return 1
    let r ← Stf.runSuite "safroletest" [(label, params, dir)] (Safrole.check o.crypto) Safrole.known
    if r != 0 then code := r
    -- The same vectors with JamCrypto's ring VRF (GP v0.8.0 path): O, 𝔹̄° and Y computed, not looked up.
    let real := JamCrypto.Ring.crypto srs validators o.crypto .v080
    let t0 ← IO.monoMsNow
    let r ← Stf.runSuite "safroletest (JamCrypto ring VRF)" [(label, params, dir)]
      (Safrole.check real) Safrole.known
    IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
    if r != 0 then code := r
  return code
