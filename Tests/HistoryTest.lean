import Tests.HistoryHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.HistoryHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "historytest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/history") JAM.Tests.History.check
