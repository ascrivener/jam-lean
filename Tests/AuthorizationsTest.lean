import Tests.AuthorizationsHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.AuthorizationsHarness`. -/

def main (args : List String) : IO UInt32 :=
  JAM.Tests.Stf.runSuite "authtest"
    (JAM.Tests.Stf.defaultDirs args "vendor/jam-test-vectors/stf/authorizations") JAM.Tests.Authorizations.check
