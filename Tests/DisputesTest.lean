import Tests.DisputesHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.DisputesHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "disputestest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/disputes") JAM.Tests.Disputes.check
