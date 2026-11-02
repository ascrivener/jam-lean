/-
  GENERATED FILE: do not edit by hand.
  Produced by `scripts/gen_constants.py` from the Gray Paper v0.8.0, `text/definitions.tex`.
  CI regenerates it from the pinned paper and fails on any difference.
-/

namespace JAM.Constants

/-- The period, in seconds, between audit tranches. See section \ref{sec:auditselection}. -/
def Ctrancheseconds : Nat := 8

/-- The additional minimum balance required per item of elective service state. See equation \ref{eq:deposits}. -/
def Citemdeposit : Nat := 10

/-- The additional minimum balance required per octet of elective service state. See equation \ref{eq:deposits}. -/
def Cbytedeposit : Nat := 1

/-- The basic minimum balance which all services require. See equation \ref{eq:deposits}. -/
def Cbasedeposit : Nat := 100

/-- The total number of cores. -/
def Ccorecount : Nat := 341

/-- The period in timeslots after which an unreferenced preimage may be expunged. See \texttt{eject} definition in section \ref{sec:accumulatefunctions}. -/
def Cexpungeperiod : Nat := 19200

/-- The length of an epoch in timeslots. See section \ref{sec:epochsandslots}. -/
def Cepochlen : Nat := 600

/-- The audit bias factor, the expected number of additional validators who will audit a work-report in the following tranche for each no-show in the previous. See equation \ref{eq:latertranches}. -/
def Cauditbiasfactor : Nat := 2

/-- The gas allocated to invoke a work-report's Accumulation logic. -/
def Creportaccgas : Nat := 10000000

/-- The gas allocated to invoke a work-package's Is-Authorized logic. -/
def Cpackageauthgas : Nat := 50000000

/-- The gas allocated to invoke a work-package's Refine logic. -/
def Cpackagerefgas : Nat := 5000000000

/-- The total gas allocated across for all Accumulation. Should be no smaller than $\Creportaccgas\cdot\Ccorecount + \sum_{g \in \values{\alwaysaccers}}(g)$. -/
def Cblockaccgas : Nat := 3500000000

/-- The size of recent history, in blocks. See equation \ref{eq:recenthistorydef}. -/
def Crecenthistorylen : Nat := 8

/-- The maximum amount of work items in a package. See equations \ref{eq:workreport} and \ref{eq:workpackage}. -/
def Cmaxpackageitems : Nat := 16

/-- The maximum sum of dependency items in a work-report. See equation \ref{eq:limitreportdeps}. -/
def Cmaxreportdeps : Nat := 8

/-- The maximum number of tickets which may be submitted in a single extrinsic. See equation \ref{eq:enforceticketlimit}. -/
def Cmaxblocktickets : Nat := 16

/-- The maximum age in timeslots of the lookup anchor. See equation \ref{eq:limitlookupanchorage}. -/
def Cmaxlookupanchorage : Nat := 14400

/-- The maximum number of verdicts which may be included in a single extrinsic. See equation \ref{eq:disputesextrinsics}. -/
def Cmaxextrinsicverdicts : Nat := 16

/-- The maximum number each of culprits or faults which may be included in a single extrinsic. See equation \ref{eq:disputesextrinsics}. -/
def Cmaxextrinsicoffenses : Nat := 16

/-- The maximum number of items in the authorizations pool. See equation \ref{eq:authstatecomposition}. -/
def Cauthpoolsize : Nat := 8

/-- The slot period, in seconds. See equation \ref{sec:epochsandslots}. -/
def Cslotseconds : Nat := 6

/-- The number of items in the authorizations queue. See equation \ref{eq:authstatecomposition}. -/
def Cauthqueuesize : Nat := 80

/-- The rotation period of validator-core assignments, in timeslots. See sections \ref{sec:coresandvalidators} and \ref{sec:workreportguarantees}. -/
def Crotationperiod : Nat := 10

/-- The minimum public service index. Services of indices below these may only be created by the Registrar. See equation \ref{eq:newserviceindex}. -/
def Cminpublicindex : Nat := 65536

/-- The maximum number of extrinsics in a work-package. See equation \ref{eq:limitworkpackagebandwidth}. -/
def Cmaxpackagexts : Nat := 128

/-- The period in timeslots after which reported but unavailable work is cleared. See equation \ref{eq:availassignmentspostassurancesdef}. -/
def Cassurancetimeoutperiod : Nat := 5

/-- The maximum size of is-authorized code in octets. See equation \ref{eq:isauthinvocation}. -/
def Cmaxauthcodesize : Nat := 64000

/-- The maximum size of the concatenated variable-size blobs, extrinsics and imported segments of a work-package, in octets. See equation \ref{eq:checkextractsize}. -/
def Cmaxbundlesize : Nat := 13791360

/-- The maximum size of service code in octets. See equations \ref{eq:refinvocation}, \ref{eq:accinvocation} \& \ref{eq:onxferinvocation}. -/
def Cmaxservicecodesize : Nat := 4000000

/-- The size of a segment in octets. See section \ref{sec:segments}. -/
def Csegmentsize : Nat := 4104

/-- The additional footprint in the Audits DA of a single imported segment. See equation \ref{eq:segmentfootprint}. -/
def Csegmentfootprint : Nat := 4488

/-- The maximum number of imports in a work-package. See equation \ref{eq:limitworkpackagebandwidth}. -/
def Cmaxpackageimports : Nat := 3072

/-- The maximum total size of all unbounded blobs in a work-report, in octets. See equation \ref{eq:limitworkreportsize}. -/
def Cmaxreportvarsize : Nat := 49152

/-- The size of a transfer memo in octets. See equation \ref{eq:defxfer}. -/
def Cmemosize : Nat := 128

/-- The maximum number of exports in a work-package. See equation \ref{eq:limitworkpackagebandwidth}. -/
def Cmaxpackageexports : Nat := 3072

/-- The number of slots into an epoch at which ticket-submission ends. See sections \ref{sec:slotkeysequence}, \ref{sec:epochmarker} and \ref{sec:safrolextandtickets}. -/
def Cepochtailstart : Nat := 500

/-- The \textsc{pvm} dynamic address alignment factor. See equation \ref{eq:jumptablealignment}. -/
def Cpvmdynaddralign : Nat := 2

/-- The standard \textsc{pvm} program initialization input data size. See equation \ref{sec:standardprograminit}. -/
def Cpvminitinputsize : Nat := 16777216

/-- The \textsc{pvm} memory page size. See equation \ref{eq:pvmmemory}. -/
def Cpvmpagesize : Nat := 4096

/-- The standard \textsc{pvm} program initialization zone size. See section \ref{sec:standardprograminit}. -/
def Cpvminitzonesize : Nat := 65536

/-- Gas cost charged for an unknown host-call. -/
def Cgasunknown : Nat := 1000

/-- $\Omega_A$ (\texttt{assign}) base gas cost. -/
def CgasA : Nat := 1818

/-- $\Omega_B$ (\texttt{bless}) base gas cost. -/
def CgasBconst : Nat := 422

/-- $\Omega_B$ (\texttt{bless}) gas per item. -/
def CgasBlinear : Nat := 20

/-- $\Omega_C$ (\texttt{checkpoint}) base gas cost. -/
def CgasC : Nat := 103

/-- $\Omega_D$ (\texttt{designate}) base gas cost. -/
def CgasDconst : Nat := 1100

/-- $\Omega_D$ (\texttt{designate}) gas per validator. -/
def CgasDlinear : Nat := 302

/-- $\Omega_E$ (\texttt{export}) base gas cost. -/
def CgasE : Nat := 3521

/-- $\Omega_F$ (\texttt{forget}) base gas cost. -/
def CgasF : Nat := 3250

/-- $\Omega_G$ (\texttt{gas}) base gas cost. -/
def CgasG : Nat := 48

/-- $\Omega_H$ (\texttt{historical\_lookup}) base gas cost. -/
def CgasHconst : Nat := 1125

/-- $\Omega_H$ (\texttt{historical\_lookup}) gas per 1024 octets ($\fnmemgas(\CgasHlinear, \ell)$). -/
def CgasHlinear : Nat := 264

/-- $\Omega_I$ (\texttt{info}) base gas cost. -/
def CgasI : Nat := 703

/-- $\Omega_J$ (\texttt{eject}) base gas cost. -/
def CgasJ : Nat := 458

/-- $\Omega_K$ (\texttt{invoke}) base gas cost. -/
def CgasK : Nat := 968

/-- $\Omega_L$ (\texttt{lookup}) base gas cost. -/
def CgasLconst : Nat := 600

/-- $\Omega_L$ (\texttt{lookup}) gas per 1024 octets ($\fnmemgas(\CgasLlinear, \ell)$). -/
def CgasLlinear : Nat := 248

/-- $\Omega_M$ (\texttt{machine}) base gas cost. -/
def CgasMconst : Nat := 1862

/-- $\Omega_M$ (\texttt{machine}) gas per 1024 octets, program size ($\fnmemgas(\CgasMlinear, \ell)$). -/
def CgasMlinear : Nat := 112

/-- $\Omega_N$ (\texttt{new}) base gas cost. -/
def CgasN : Nat := 3855

/-- $\Omega_O$ (\texttt{poke}) base gas cost. -/
def CgasOconst : Nat := 297

/-- $\Omega_O$ (\texttt{poke}) gas per 1024 octets ($\fnmemgas(\CgasOlinear, \ell)$). -/
def CgasOlinear : Nat := 224

/-- $\Omega_P$ (\texttt{peek}) base gas cost. -/
def CgasPconst : Nat := 377

/-- $\Omega_P$ (\texttt{peek}) gas per 1024 octets ($\fnmemgas(\CgasPlinear, \ell)$). -/
def CgasPlinear : Nat := 336

/-- $\Omega_Q$ (\texttt{query}) base gas cost. -/
def CgasQ : Nat := 643

/-- $\Omega_R$ (\texttt{read}) base gas cost. -/
def CgasRconst : Nat := 2407

/-- $\Omega_R$ (\texttt{read}) key gas per 1024 octets ($\fnmemgas(\CgasRkeylinear, \ell)$). -/
def CgasRkeylinear : Nat := 1736

/-- $\Omega_R$ (\texttt{read}) value gas per 1024 octets ($\fnmemgas(\CgasRvallinear, \ell)$). -/
def CgasRvallinear : Nat := 248

/-- $\Omega_S$ (\texttt{solicit}) base gas cost. -/
def CgasS : Nat := 2193

/-- $\Omega_T$ (\texttt{transfer}) base gas cost. -/
def CgasT : Nat := 575

/-- $\Omega_U$ (\texttt{upgrade}) base gas cost. -/
def CgasU : Nat := 1028

/-- $\Omega_W$ (\texttt{write}) base gas cost. -/
def CgasWconst : Nat := 2442

/-- $\Omega_W$ (\texttt{write}) gas per 1024 octets ($\fnmemgas(\CgasWvallinear, \ell)$). -/
def CgasWvallinear : Nat := 216

/-- $\Omega_W$ (\texttt{write}) key gas per 1024 octets ($\fnmemgas(\CgasWkeylinear, \ell)$). -/
def CgasWkeylinear : Nat := 3358

/-- $\Omega_X$ (\texttt{expunge}) base gas cost. -/
def CgasX : Nat := 335

/-- $\Omega_Z$ (\texttt{pages}) alloc base gas cost. -/
def CgasZallocconst : Nat := 275

/-- $\Omega_Z$ (\texttt{pages}) alloc gas per page. -/
def CgasZalloclinear : Nat := 121

/-- $\Omega_Z$ (\texttt{pages}) free base gas cost. -/
def CgasZfreeconst : Nat := 212

/-- $\Omega_Z$ (\texttt{pages}) free gas per page. -/
def CgasZfreelinear : Nat := 118

/-- $\Omega_Z$ (\texttt{pages}) setmode base gas cost. -/
def CgasZsetmodeconst : Nat := 130

/-- $\Omega_Z$ (\texttt{pages}) setmode gas per page. -/
def CgasZsetmodelinear : Nat := 29

/-- $\Omega_Z$ (\texttt{pages}) invalid-$r$ base gas cost. -/
def CgasZinvalid : Nat := 80

/-- $\Omega_\Taurus$ (\texttt{yield}) base gas cost. -/
def CgasTaurus : Nat := 98

/-- $\Omega_\Aries$ (\texttt{provide}) base gas cost. -/
def CgasAriesconst : Nat := 3980

/-- $\Omega_\Aries$ (\texttt{provide}) gas per 1024 octets ($\fnmemgas(\CgasArieslinear, \ell)$). -/
def CgasArieslinear : Nat := 2264

/-- $\Omega_\Gemini$ (\texttt{grow\_heap}) base gas cost. -/
def CgasGeminiconst : Nat := 275

/-- $\Omega_\Gemini$ (\texttt{grow\_heap}) gas per additional page. -/
def CgasGeminilinear : Nat := 121

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
