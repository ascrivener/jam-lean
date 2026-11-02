import JAM.Constants
import JAM.Codec

/-!
# Chain parameters

The protocol constants that the `fetch` host call reports (case 0, GP v0.8.0 Appendix B), in its
order. `full` is the Gray Paper's chain (`JAM.Constants`, generated from `definitions.tex`). `tiny`
is the test-vector chain of davxy/jam-test-vectors `v0.8.0` (README "Chainspec Parameters"), which
differs only in the values listed there.
-/

namespace JAM

open Constants

/-- The parameters `fetch` case 0 encodes, in its order (GP Appendix B, Ω_Y). -/
structure Params where
  itemDeposit : Nat        -- 𝖡_I
  byteDeposit : Nat        -- 𝖡_L
  baseDeposit : Nat        -- 𝖡_S
  coreCount : Nat          -- 𝖢
  expungePeriod : Nat      -- 𝖣
  epochLen : Nat           -- 𝖤
  reportAccGas : Nat       -- 𝖦_A
  packageAuthGas : Nat     -- 𝖦_I
  packageRefGas : Nat      -- 𝖦_R
  blockAccGas : Nat        -- 𝖦_T
  recentHistoryLen : Nat   -- 𝖧
  maxPackageItems : Nat    -- 𝖨
  maxReportDeps : Nat      -- 𝖩
  maxBlockTickets : Nat    -- 𝖪
  maxLookupAnchorAge : Nat -- 𝖫
  authPoolSize : Nat       -- 𝖮
  slotSeconds : Nat        -- 𝖯
  authQueueSize : Nat      -- 𝖰
  rotationPeriod : Nat     -- 𝖱
  maxPackageXts : Nat      -- 𝖳
  assuranceTimeout : Nat   -- 𝖴
  maxAuthCodeSize : Nat    -- 𝖶_A
  maxBundleSize : Nat      -- 𝖶_B
  maxServiceCodeSize : Nat -- 𝖶_C
  maxPackageImports : Nat  -- 𝖶_M
  maxReportVarSize : Nat   -- 𝖶_R
  memoSize : Nat           -- 𝖶_T
  maxPackageExports : Nat  -- 𝖶_X
  epochTailStart : Nat     -- 𝖸

/-- The Gray Paper's full chain. -/
def Params.full : Params :=
  { itemDeposit := Citemdeposit, byteDeposit := Cbytedeposit, baseDeposit := Cbasedeposit,
    coreCount := Ccorecount, expungePeriod := Cexpungeperiod, epochLen := Cepochlen,
    reportAccGas := Creportaccgas, packageAuthGas := Cpackageauthgas,
    packageRefGas := Cpackagerefgas, blockAccGas := Cblockaccgas,
    recentHistoryLen := Crecenthistorylen, maxPackageItems := Cmaxpackageitems,
    maxReportDeps := Cmaxreportdeps, maxBlockTickets := Cmaxblocktickets,
    maxLookupAnchorAge := Cmaxlookupanchorage, authPoolSize := Cauthpoolsize,
    slotSeconds := Cslotseconds, authQueueSize := Cauthqueuesize,
    rotationPeriod := Crotationperiod, maxPackageXts := Cmaxpackagexts,
    assuranceTimeout := Cassurancetimeoutperiod, maxAuthCodeSize := Cmaxauthcodesize,
    maxBundleSize := Cmaxbundlesize, maxServiceCodeSize := Cmaxservicecodesize,
    maxPackageImports := Cmaxpackageimports, maxReportVarSize := Cmaxreportvarsize,
    memoSize := Cmemosize, maxPackageExports := Cmaxpackageexports,
    epochTailStart := Cepochtailstart }

/-- The test vectors' tiny chain: 2 cores, an expunge period of 32 and epochs of 12 slots,
    tail start 10, 3 tickets per extrinsic, rotation period 4, 𝖦_T = 20,000,000 and
    𝖦_R = 1,000,000,000. -/
def Params.tiny : Params :=
  { Params.full with coreCount := 2, expungePeriod := 32, epochLen := 12, epochTailStart := 10,
                     maxBlockTickets := 3, rotationPeriod := 4, blockAccGas := 20000000,
                     packageRefGas := 1000000000 }

/-- ℰ of the parameters as `fetch` case 0 returns them (GP Appendix B, Ω_Y). -/
def Params.encode (c : Params) : List UInt8 :=
  let e := Codec.fixed
  e 8 c.itemDeposit ++ e 8 c.byteDeposit ++ e 8 c.baseDeposit ++ e 2 c.coreCount ++
    e 4 c.expungePeriod ++ e 4 c.epochLen ++ e 8 c.reportAccGas ++ e 8 c.packageAuthGas ++
    e 8 c.packageRefGas ++ e 8 c.blockAccGas ++ e 2 c.recentHistoryLen ++ e 2 c.maxPackageItems ++
    e 2 c.maxReportDeps ++ e 2 c.maxBlockTickets ++ e 4 c.maxLookupAnchorAge ++
    e 2 c.authPoolSize ++ e 2 c.slotSeconds ++ e 2 c.authQueueSize ++ e 2 c.rotationPeriod ++
    e 2 c.maxPackageXts ++ e 2 c.assuranceTimeout ++ e 4 c.maxAuthCodeSize ++
    e 4 c.maxBundleSize ++ e 4 c.maxServiceCodeSize ++ e 4 c.maxPackageImports ++
    e 4 c.maxReportVarSize ++ e 4 c.memoSize ++ e 4 c.maxPackageExports ++ e 4 c.epochTailStart

end JAM
