import Tests.StatisticsHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.StatisticsHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "statstest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/statistics") JAM.Tests.Statistics.check
