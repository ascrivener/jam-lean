import Tests.AssurancesHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.AssurancesHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "assurancestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/assurances") JAM.Tests.Assurances.check
    JAM.Tests.Assurances.knownDeviations
