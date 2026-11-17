import Services.Bootstrap.Acc.ItemsLoop.Op
import Services.Bootstrap.Acc.Final.LogLineK
import Services.Bootstrap.Acc.Final.Lifts
import Services.Bootstrap.Bridge
import Services.Bootstrap.Prefix

/-!
# T2's named hypotheses

The hypotheses `accumulate_spec` (`Final/Spec.lean`) carries besides the run's shape, each a fact about
the binary or about the input, to be proved later (CLAUDE.md, standing decisions: named hypotheses until
they land, each listed in the theorem's docstring and in `docs/whats-proven.md`):

- **`InfoFits e s`**: the service's own code hash is shorter than 2⁶⁴ − 73 octets, so its `info`
  record (the code hash and 64 more octets) is shorter than 2⁶⁴ − 9, which the SDK's `info` wrapper
  reads as an error code from on (49017). The paper's c ∈ ℍ has 32 octets.
- **`AccLogFail`**: the first log line's failure tail (decision 12's `ExhaustsP` for 6501 … 6630):
  if its run reaches a failed allocation, the run then ends ☇ keeping the context. Its success branch is
  proved (`acc_log_lineK`).
- **`AccVendoredFacts`**: the read-only slices accumulate reads in the vendored blob (step 10 of
  `docs/bootstrap-target.md`, as `VendoredFacts`).
- **`AccHypsAt`**: the items loop's hypotheses (`items_loop_full`): `Utf8Call`, `LogFmt`, `KeyFmt`,
  `ItemLogFmt`, `OutDecH`, `InstrLogH`, `ResultLogH`, `HandlerH`, `PushH`, `ExtendH`, `OkEncH`,
  `DropInstrsH`, with `AccLogFail`, for a program with bootstrap's code facts.

(`InputsGlob`, that the inputs decode 6630 … 6674 keeps the statics `Glob`, was a named hypothesis
here; it is now a conclusion of `inputs_decode`.)
-/

namespace Services.Bootstrap.Acc.Final

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.CodeF Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Picoalloc
  Services.Bootstrap.Acc Services.Bootstrap.Fmt Services.Bootstrap.Bridge
  Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Acc.Handlers.InstrLoop

/-- **The service's own code hash fits `info`'s length word** (a named hypothesis): in the state e
    before the transfers are credited, service s's code hash is shorter than 2⁶⁴ − 73 octets, so its
    `info` record (`infoValue`: the code hash and 64 more octets) is shorter than 2⁶⁴ − 9. The SDK's
    `info` wrapper reads a length from 2⁶⁴ − 9 on as a host error code (49017). The paper's c ∈ ℍ has
    32 octets. -/
def InfoFits (e : PartialState) (s : Nat) : Prop :=
  ∀ a, e.accounts.get? s = some a → a.codeHash.length < 18446744073709551543

/-- **The first log line's failure tail** (a named hypothesis; decision 12's `ExhaustsP` for
    6501 … 6630): from accumulate's first log line's start (sp = 4278057152, the premises of
    `acc_log_line`: the allocator's context, the template and the `String` vtable), if the run reaches
    a failed allocation keeping the context, then from there it ends ☇ keeping the context. -/
def AccLogFail (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s : State) (N : Nat),
    HeapCtxC env.code pb S0 S1 μ s → s.base % 8 = 0 →
    ω[1] = UInt64.ofNat 4278057152 → ω[7] = UInt64.ofNat (4278057152 + 1568) →
    RoW μ → μ.readN 66464 42 = accTmplBytes → (∀ a, 66464 ≤ a → a < 66506 → μ.readable a = true) →
    Exhausts p (KeepCtx (accContractS env)) pb 6501 ω μ (c, f) N →
    ExhaustsP p env pb 6501 ω μ c f

/-- **The read-only slices accumulate reads, in the vendored blob** (a named hypothesis, for step 10 of
    `docs/bootstrap-target.md`, like `VendoredFacts`): a closed statement about `Bridge.vendored`. Its
    layout is as deployed, and its read-only data holds, at their offsets from 65536: the first log
    line's template (66464), the `String` vtable's words (77040), the key "transfer-count" (65956),
    `set`'s error table (69056), the key-size words (68680) and the instruction jump table (65736). -/
def AccVendoredFacts : Prop :=
  ∃ vb : JamBlob, vendored = some vb ∧ Services.Bootstrap.Prefix.layoutOk vb = true ∧
    (vb.ro.toList.drop 928).take 42 = accTmplBytes ∧
    (vb.ro.toList.drop 11504).take 16 = [36, 10, 0, 0, 0, 0, 0, 0, 32, 10, 0, 0, 0, 0, 0, 0] ∧
    (vb.ro.toList.drop 420).take 14 = [116, 114, 97, 110, 115, 102, 101, 114, 45, 99, 111, 117, 110, 116] ∧
    (vb.ro.toList.drop 3520).take 20 =
      [178, 250, 254, 255, 180, 250, 254, 255, 176, 250, 254, 255, 182, 250, 254, 255, 184, 250, 254, 255] ∧
    (vb.ro.toList.drop 3144).take 24 = [1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0] ∧
    (vb.ro.toList.drop 200).take 100 = Handlers.jumpTab

/-- **The code is bootstrap's** (as `Bridge.IsBootstrap`, for the code Ψ_A finds, after the metadata):
    within 𝖶_C; a JAM blob whose data sections and layout are the vendored blob's, with its heap bounds,
    and whose PVM code passes the code-fact checks accumulate's proofs use. -/
def IsBootstrapCode (code : ByteArray) : Prop :=
  code.size ≤ Constants.Cmaxservicecodesize ∧
  ∃ (jb vb : JamBlob), JamBlob.parse? code = some jb ∧
    vendored = some vb ∧ jb.ro = vb.ro ∧ jb.rw = vb.rw ∧ jb.heapPages = vb.heapPages ∧
    jb.stackSize = vb.stackSize ∧ heapBounds code = (48, 1044430) ∧
    checkCode jb.code Code.facts = true ∧ checkCode jb.code CodeX.facts = true ∧
    checkCode jb.code CodeA.facts = true ∧ checkCode jb.code CodeF.facts = true

/-- **The items loop's and the start-up's named hypotheses**, for program p (code facts P) and
    environment env, with the representation `B` of instructions, constants `C` and timeslot `now`:
    `AccLogFail` and `items_loop_full`'s twelve. All at the heap bound 1044430 and the
    stack 4278050816 … 4278059008. -/
structure AccHypsAt (B : InstrRep) (C : Spec.Consts) (now : Nat) (p : ByteArray) (P : Program)
    (env : AccEnv) : Prop where
  logFail : AccLogFail p env 1044430 4278050816 4278059008
  utf8 : Utf8Call p env 1044430 4278050816 4278059008
  logFmt : LogFmt p env 1044430 4278050816 4278059008
  keyFmt : KeyFmt p env 1044430 4278050816 4278059008
  itemLog : ItemLogFmt p env 1044430 4278050816 4278059008
  outDec : OutDecH B C p env 1044430 4278050816 4278059008
  instrLog : InstrLogH B p env 1044430 4278050816 4278059008
  resultLog : ResultLogH p env 1044430 4278050816 4278059008
  handler : HandlerH B p env C now 1044430 4278050816 4278059008 AccAbort
  push : PushH p env 1044430 4278050816 4278059008
  extend : Handlers.Results.ExtendH p P env 1044430 4278050816 4278059008
  okEnc : Handlers.Results.OkEncH p P env 1044430 4278050816 4278059008
  drop : DropInstrsH B p P env.code 1044430 4278050816 4278059008

/-- **T2's named hypotheses on the binary**, for every code that is bootstrap's (`IsBootstrapCode`):
    `AccHypsAt` for its PVM code with the code facts, any environment with that code and the full
    parameters, any timeslot. -/
def AccHyps (B : InstrRep) (C : Spec.Consts) : Prop :=
  ∀ (code : ByteArray) (jb : JamBlob), IsBootstrapCode code → JamBlob.parse? code = some jb →
    ∀ (P : Program), HasCode jb.code P → HasCodeX jb.code P → HasCodeA jb.code P → HasCodeF jb.code P →
    ∀ (env : AccEnv) (now : Nat), env.code = code → env.params = Params.full →
      AccHypsAt B C now jb.code P env

end Services.Bootstrap.Acc.Final
