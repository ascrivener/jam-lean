/-
  GENERATED FILE: do not edit by hand.
  Produced by `scripts/gen_constants.py` from the Gray Paper v0.8.1, `text/definitions.tex`.
  CI regenerates it from the pinned paper and fails on any difference.
-/

namespace JAM.Constants

/-- The period, in seconds, between audit tranches. See §17.3. -/
def Ctrancheseconds : Nat := 8

/-- The additional minimum balance required per item of elective service state. See eq. (9.8). -/
def Citemdeposit : Nat := 10

/-- The additional minimum balance required per octet of elective service state. See eq. (9.8). -/
def Cbytedeposit : Nat := 1

/-- The basic minimum balance which all services require. See eq. (9.8). -/
def Cbasedeposit : Nat := 100

/-- The total number of cores. -/
def Ccorecount : Nat := 341

/-- The period in timeslots after which an unreferenced preimage may be expunged. See `forget` definition in §B.5.3. -/
def Cexpungeperiod : Nat := 19200

/-- The length of an epoch in timeslots. See §4.8. -/
def Cepochlen : Nat := 600

/-- The audit bias factor, the expected number of additional validators who will audit a work-report in the following tranche for each no-show in the previous. See eq. (17.13). -/
def Cauditbiasfactor : Nat := 2

/-- The gas allocated to invoke a work-report's Accumulation logic. Equivalent to 10 ms on the reference hardware clocked at 4.7 GHz. -/
def Creportaccgas : Nat := 47000000

/-- The gas allocated to invoke a work-package's Is-Authorized logic. Equivalent to 50 ms on the reference hardware clocked at 4.7 GHz. -/
def Cpackageauthgas : Nat := 235000000

/-- The gas allocated to invoke a work-package's Refine logic. Equivalent to 5 s on the reference hardware clocked at 4.7 GHz. -/
def Cpackagerefgas : Nat := 23500000000

/-- The total gas allocated across for all Accumulation. Should be no smaller than $\Creportaccgas\cdot\Ccorecount + \sum_{g \in \values{\alwaysaccers}}(g)$. Equivalent to 3.5 s on the reference hardware clocked at 4.7 GHz. -/
def Cblockaccgas : Nat := 16450000000

/-- The size of recent history, in blocks. See eq. (7.8). -/
def Crecenthistorylen : Nat := 8

/-- The maximum amount of work items in a package. See eqs. (11.2) and (14.2). -/
def Cmaxpackageitems : Nat := 16

/-- The maximum sum of dependency items in a work-report. See eq. (11.3). -/
def Cmaxreportdeps : Nat := 8

/-- The maximum number of tickets which may be submitted in a single extrinsic. See eq. (6.32). -/
def Cmaxblocktickets : Nat := 16

/-- The maximum age in timeslots of the lookup anchor. See eq. (11.37). -/
def Cmaxlookupanchorage : Nat := 14400

/-- The maximum number of verdicts which may be included in a single extrinsic. See eq. (10.2). -/
def Cmaxextrinsicverdicts : Nat := 16

/-- The maximum number each of culprits or faults which may be included in a single extrinsic. See eq. (10.2). -/
def Cmaxextrinsicoffenses : Nat := 16

/-- The maximum length of the preimages component of the extrinsic ($\xtpreimages$). See eq. (12.35). -/
def Cmaxxtpreimageslen : Nat := 256

/-- The maximum number of data octets in the preimages component of the extrinsic ($\xtpreimages$). See eq. (12.38). -/
def Cmaxxtpreimagesdatasize : Nat := 33554432

/-- The maximum number of items in the authorizations pool. See eq. (8.1). -/
def Cauthpoolsize : Nat := 8

/-- The slot period, in seconds. See §4.8. -/
def Cslotseconds : Nat := 6

/-- The number of items in the authorizations queue. See eq. (8.1). -/
def Cauthqueuesize : Nat := 80

/-- The rotation period of validator-core assignments, in timeslots. See §11.3 and §11.4. -/
def Crotationperiod : Nat := 10

/-- The minimum public service index. Services of indices below these may only be created by the Registrar. See eq. (B.13). -/
def Cminpublicindex : Nat := 65536

/-- The maximum number of extrinsics in a work-package. See eq. (14.5). -/
def Cmaxpackagexts : Nat := 128

/-- The period in timeslots after which reported but unavailable work is cleared. See eq. (11.17). -/
def Cassurancetimeoutperiod : Nat := 5

/-- The maximum size of is-authorized code in octets. See eq. (B.1). -/
def Cmaxauthcodesize : Nat := 196608

/-- The maximum size of a work-package bundle in octets. See eq. (14.9). -/
def Cmaxbundlesize : Nat := 13904950

/-- The maximum size of service code in octets. See eqs. (B.5) \& (B.9). -/
def Cmaxservicecodesize : Nat := 4000000

/-- The size of a segment in octets. See §14.2.1. -/
def Csegmentsize : Nat := 4104

/-- The additional footprint in the Audits DA of a single imported segment. See eq. (14.7). -/
def Csegmentfootprint : Nat := 4488

/-- The maximum size of the input data of a work-package, in octets: its concatenated variable-size blobs, extrinsics and imported segments. See eq. (14.6). -/
def Cmaxinputsize : Nat := 13791360

/-- The maximum number of imports in a work-package. See eq. (14.5). -/
def Cmaxpackageimports : Nat := 3072

/-- The maximum total size of all unbounded blobs in a work-report, in octets. See eq. (11.8). -/
def Cmaxreportvarsize : Nat := 49152

/-- The size of a transfer memo in octets. See eq. (12.14). -/
def Cmemosize : Nat := 128

/-- The maximum number of exports in a work-package. See eq. (14.5). -/
def Cmaxpackageexports : Nat := 3072

/-- The number of slots into an epoch at which ticket-submission ends. See §6.5, §6.6 and §6.7. -/
def Cepochtailstart : Nat := 500

/-- The \textsc{pvm} dynamic address alignment factor. See eq. (A.22). -/
def Cpvmdynaddralign : Nat := 2

/-- The maximum size of the instruction data of a \textsc{pvm} program blob, in octets. See eq. (A.2). -/
def Cpvmmaxcodesize : Nat := 33554432

/-- The standard \textsc{pvm} program initialization input data size. See §A.7. -/
def Cpvminitinputsize : Nat := 16777216

/-- The maximum number of entries in the dynamic jump table of a \textsc{pvm} program blob. See eq. (A.2). -/
def Cpvmmaxjumptableentries : Nat := 16777216

/-- The \textsc{pvm} memory page size. See eq. (4.24). -/
def Cpvmpagesize : Nat := 4096

/-- The standard \textsc{pvm} program initialization zone size. See §A.7. -/
def Cpvminitzonesize : Nat := 65536

/-- Gas cost charged for an unknown host-call. -/
def Cgasunknown : Nat := 1000

/-- $\Omega_A$ (`assign`) base gas cost. -/
def CgasA : Nat := 1818

/-- $\Omega_B$ (`bless`) base gas cost. -/
def CgasBconst : Nat := 422

/-- $\Omega_B$ (`bless`) gas per record. -/
def CgasBlinear : Nat := 20

/-- $\Omega_C$ (`checkpoint`) base gas cost. -/
def CgasC : Nat := 103

/-- $\Omega_D$ (`designate`) base gas cost. -/
def CgasDconst : Nat := 1100

/-- $\Omega_D$ (`designate`) gas per validator. -/
def CgasDlinear : Nat := 302

/-- $\Omega_E$ (`export`) base gas cost. -/
def CgasE : Nat := 3521

/-- $\Omega_F$ (`forget`) base gas cost. -/
def CgasF : Nat := 3250

/-- $\Omega_G$ (`gas`) base gas cost. -/
def CgasG : Nat := 48

/-- $\Omega_H$ (`historical\_lookup`) base gas cost. -/
def CgasHconst : Nat := 1125

/-- $\Omega_H$ (`historical\_lookup`) gas per 1024 octets ($\fnmemgas(\CgasHlinear, \ell)$). -/
def CgasHlinear : Nat := 264

/-- $\Omega_I$ (`info`) base gas cost. -/
def CgasI : Nat := 703

/-- $\Omega_J$ (`eject`) base gas cost. -/
def CgasJ : Nat := 458

/-- $\Omega_K$ (`invoke`) base gas cost. -/
def CgasK : Nat := 968

/-- $\Omega_L$ (`lookup`) base gas cost. -/
def CgasLconst : Nat := 600

/-- $\Omega_L$ (`lookup`) gas per 1024 octets ($\fnmemgas(\CgasLlinear, \ell)$). -/
def CgasLlinear : Nat := 248

/-- $\Omega_M$ (`machine`) gas cost. -/
def CgasM : Nat := 1862

/-- $\Omega_N$ (`new`) base gas cost. -/
def CgasN : Nat := 3855

/-- $\Omega_O$ (`poke`) base gas cost. -/
def CgasOconst : Nat := 297

/-- $\Omega_O$ (`poke`) gas per 1024 octets ($\fnmemgas(\CgasOlinear, \ell)$). -/
def CgasOlinear : Nat := 224

/-- $\Omega_P$ (`peek`) base gas cost. -/
def CgasPconst : Nat := 377

/-- $\Omega_P$ (`peek`) gas per 1024 octets ($\fnmemgas(\CgasPlinear, \ell)$). -/
def CgasPlinear : Nat := 336

/-- $\Omega_Q$ (`query`) base gas cost. -/
def CgasQ : Nat := 643

/-- $\Omega_R$ (`read`) base gas cost. -/
def CgasRconst : Nat := 2407

/-- $\Omega_R$ (`read`) key gas per 1024 octets ($\fnmemgas(\CgasRkeylinear, \ell)$). -/
def CgasRkeylinear : Nat := 1736

/-- $\Omega_R$ (`read`) value gas per 1024 octets ($\fnmemgas(\CgasRvallinear, \ell)$). -/
def CgasRvallinear : Nat := 248

/-- $\Omega_S$ (`solicit`) base gas cost. -/
def CgasS : Nat := 2193

/-- $\Omega_T$ (`transfer`) base gas cost. -/
def CgasT : Nat := 575

/-- $\Omega_U$ (`upgrade`) base gas cost. -/
def CgasU : Nat := 1028

/-- $\Omega_V$ (`supervisor`) base gas cost. -/
def CgasV : Nat := 1000

/-- $\Omega_W$ (`write`) base gas cost. -/
def CgasWconst : Nat := 2442

/-- $\Omega_W$ (`write`) gas per 1024 octets ($\fnmemgas(\CgasWvallinear, \ell)$). -/
def CgasWvallinear : Nat := 216

/-- $\Omega_W$ (`write`) key gas per 1024 octets ($\fnmemgas(\CgasWkeylinear, \ell)$). -/
def CgasWkeylinear : Nat := 3358

/-- $\Omega_X$ (`expunge`) base gas cost. -/
def CgasX : Nat := 335

/-- $\Omega_Y$ (`fetch`) otherwise: nothing. -/
def CgasYunknown : Nat := 80

/-- $\Omega_Z$ (`pages`) alloc base gas cost. -/
def CgasZallocconst : Nat := 275

/-- $\Omega_Z$ (`pages`) alloc gas per page. -/
def CgasZalloclinear : Nat := 121

/-- $\Omega_Z$ (`pages`) free base gas cost. -/
def CgasZfreeconst : Nat := 212

/-- $\Omega_Z$ (`pages`) free gas per page. -/
def CgasZfreelinear : Nat := 118

/-- $\Omega_Z$ (`pages`) setmode base gas cost. -/
def CgasZsetmodeconst : Nat := 130

/-- $\Omega_Z$ (`pages`) setmode gas per page. -/
def CgasZsetmodelinear : Nat := 29

/-- $\Omega_Z$ (`pages`) invalid-$r$ base gas cost. -/
def CgasZinvalid : Nat := 80

/-- $\Omega_\Taurus$ (`yield`) base gas cost. -/
def CgasTaurus : Nat := 98

/-- $\Omega_\Aries$ (`provide`) base gas cost. -/
def CgasAriesconst : Nat := 3980

/-- $\Omega_\Aries$ (`provide`) gas per 1024 octets ($\fnmemgas(\CgasArieslinear, \ell)$). -/
def CgasArieslinear : Nat := 2264

/-- $\Omega_\Gemini$ (`grow\_heap`) base gas cost. -/
def CgasGeminiconst : Nat := 275

/-- $\Omega_\Gemini$ (`grow\_heap`) gas per additional page. -/
def CgasGeminilinear : Nat := 121

/-- $\Omega_\Gamma$ (`compile`) base gas cost when compiling from memory. -/
def CgasGammamemconst : Nat := 1862

/-- $\Omega_\Gamma$ (`compile`) base gas cost when compiling from the database. -/
def CgasGammadbconst : Nat := 1862

/-- $\Omega_\Gamma$ (`compile`) in-memory read gas per 1024 octets ($\fnmemgas(\CgasGammamemlinear, \ell)$). -/
def CgasGammamemlinear : Nat := 264

/-- $\Omega_\Gamma$ (`compile`) database lookup read gas per 1024 octets ($\fnmemgas(\CgasGammadblinear, \ell)$). -/
def CgasGammadblinear : Nat := 366

/-- 𝖬_{Y,c,c} and 𝖬_{Y,c,ℓ}: the constant and per-1024-octet gas of `fetch` case `c`
    (`none` for an unknown case). -/
def CgasY : Option Nat → Nat × Nat
  | some 0 => (390, 0)
  | some 1 => (103, 0)
  | some 2 => (80, 96)
  | some 3 => (85, 96)
  | some 4 => (85, 96)
  | some 5 => (171, 0)
  | some 6 => (171, 0)
  | some 7 => (85, 96)
  | some 8 => (84, 0)
  | some 9 => (88, 0)
  | some 10 => (111, 0)
  | some 11 => (317, 0)
  | some 12 => (250, 0)
  | some 13 => (95, 96)
  | some 14 => (287, 400)
  | some 15 => (355, 344)
  | _ => (80, 0)

end JAM.Constants
