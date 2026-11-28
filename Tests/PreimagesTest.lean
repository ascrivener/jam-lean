import Tests.PreimagesHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.PreimagesHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "preimagestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/preimages") JAM.Tests.Preimages.check
