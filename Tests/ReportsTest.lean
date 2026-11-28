import Tests.ReportsHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.ReportsHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "reportstest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/reports") JAM.Tests.Reports.check
