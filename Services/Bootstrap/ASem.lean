import Services.Bootstrap.Spec
import JAM.Accumulate

/-!
# `ASem`: accumulate's host operations under the GP accumulate host functions

The semantics T2 (`docs/bootstrap-target.md`, §3) states bootstrap's accumulate against.
- Each `Spec.AOp` is the model's host function `JAM.AccHost.dispatch` (GP v0.8.0 Appendix B, F of
  eq. `accinvocation`), applied to registers and a memory holding its arguments, as the SDK passes
  them.
- Its reply is read back as the SDK reads it.
- `ASem.run n` runs a `Spec.Prog` for at most n operations on the context (x, y) ∈ 𝕃². Running out of
  operations (`stopped`) is how running out of gas appears.
- `ASem.outcome` is what Ψ_A reports (GP eq. `accinvocation`): x after `done`, else y (the last
  checkpoint). It returns no hash: bootstrap halts with (ω₇, ω₈) = (0, 0).

**The memory an operation sees.**
- Every page from 16 on is writable.
- The arguments are laid out consecutively from `argBase` = 2¹⁶.
- Replies are written from `outBase` = 2³¹.
- Arguments too large for the space panic, as in the binary.
- Operations are made with `opGas` = 2⁶³ gas, so none runs out.

**Replies.** The SDK forgets the error code (`Except Unit`), except where a code is a value:
- `read`, `lookup` and `fetch` return NONE for "absent";
- `query`'s reply is present iff ω₇ mod 2³² ≤ 3: the request's state, else NONE or HUH, as the
  binary tests it at 11623 … 11628 and 13163.
`new`'s id is 2³² − 1 when none is given, as the binary sets it at 9016 … 9026.
-/

namespace Services.Bootstrap.ASem

open PVM JAM JAM.Result Services.Bootstrap.Spec

/-- Where an operation's arguments start. -/
def argBase : Nat := 2 ^ 16

/-- Where an operation's reply is written. -/
def outBase : Nat := 2 ^ 31

/-- The gas each operation is made with: enough that none runs out. -/
def opGas : Nat := 2 ^ 63

/-- The memory of an operation: every page from 16 on writable, `args` laid out from `argBase`. -/
def argMem (args : List Bytes) : Memory :=
  (Memory.empty.setPages 16 (2 ^ 20 - 16) (some .write)).writeN argBase args.flatten

/-- The address of argument k in `argMem args`. -/
def argAt (args : List Bytes) (k : Nat) : Nat := argBase + ((args.take k).map List.length).sum

/-- Registers holding `vals` at ω₇, ω₈, …; the others 0. -/
def argRegs (vals : List Nat) : Regs :=
  Vector.ofFn fun k => if 7 ≤ k.val then UInt64.ofNat (vals.getD (k.val - 7) 0) else 0

/-- One host call: id `n`, registers `vals` from ω₇ on, the memory `argMem args`. `none` if it does
    not continue (☇). -/
def call (env : AccEnv) (n : Nat) (args : List Bytes) (vals : List Nat) (c : AccCtx) :
    Option (HostOut AccCtx) :=
  let o := AccHost.dispatch env n opGas (argRegs vals) (argMem args) c
  if o.status = .cont then some o else none

/-- ω₇ of a host call's reply. -/
def r7 (o : HostOut AccCtx) : Nat := reg o.regs 7

/-- `Ok` iff the call returned OK. -/
def okUnit (o : HostOut AccCtx) : Except Unit Unit := if r7 o = OK then .ok () else .error ()

/-- A value the host wrote at `outBase`: NONE is absent; else ω₇ octets. -/
def outValue (o : HostOut AccCtx) : Option Bytes :=
  if r7 o = NONE then none else some (o.mem.readN outBase (r7 o))

/-- A value fetched in two phases, as the SDK does: the length (an empty buffer), then the data
    (ω-registers `pre`, then the buffer `outBase`, offset 0 and the length, then `post`). -/
def twoPhase (env : AccEnv) (n : Nat) (args : List Bytes) (pre post : List Nat) (c : AccCtx) :
    Option (Option Bytes × AccCtx) := do
  let o ← call env n args (pre ++ [outBase, 0, 0] ++ post) c
  if r7 o = NONE then pure (none, o.ctx)
  else
    let o' ← call env n args (pre ++ [outBase, 0, r7 o] ++ post) o.ctx
    pure (outValue o', o'.ctx)

/-- The `Info` the SDK reads from `info`'s ℰ(c, ℰ_8(b, t, g, m, o), ℰ_4(i), …): the code hash, the
    octets o and the items i. -/
def infoOf (v : Bytes) : Info :=
  { codeHash := v.take 32, bytes := Num.decodeLE ((v.drop 64).take 8),
    items := Num.decodeLE ((v.drop 72).take 4) }

/-- **One operation** (the reply and the new context), or `none`: the call panicked. -/
def step (env : AccEnv) : {β : Type} → AOp β → AccCtx → Option (β × AccCtx)
  | _, .fetchItems, c => do
    -- `fetch` (2), kind 14: ℰ(↕**i**). The kind is ω₁₀; the buffer is ω₇ … ω₉.
    let o ← call env 2 [] [outBase, 0, 0, 14, 0, 0] c
    if r7 o = NONE then pure (none, o.ctx)
    else
      let o' ← call env 2 [] [outBase, 0, r7 o, 14, 0, 0] o.ctx
      pure (outValue o', o'.ctx)
  | _, .myInfo, c => do
    let o ← call env 6 [] [NONE, outBase, 0, 96] c
    pure (infoOf ((outValue o).getD []), o.ctx)
  | _, .read key, c => twoPhase env 4 [key] [NONE, argAt [key] 0, key.length] [] c
  | _, .write key value, c => do
    let o ← call env 5 [key, value] [argAt [key, value] 0, key.length, argAt [key, value] 1, value.length] c
    pure (if r7 o = FULL then .error () else .ok (), o.ctx)
  | _, .remove key, c => do
    let o ← call env 5 [key] [argAt [key] 0, key.length, 0, 0] c
    pure ((), o.ctx)
  | _, .checkpoint, c => do
    let o ← call env 18 [] [] c
    pure ((), o.ctx)
  | _, .lookup service hash, c =>
    twoPhase env 3 [hash] [service.getD NONE, argAt [hash] 0] [] c
  | _, .new codeHash codeLen minItemGas minMemoGas depositOffset id, c => do
    let o ← call env 19 [codeHash]
      [argAt [codeHash] 0, codeLen, minItemGas, minMemoGas, depositOffset, id.getD (2 ^ 32 - 1)] c
    pure (if r7 o ≥ HUH then .error () else .ok (r7 o), o.ctx)
  | _, .upgrade codeHash minItemGas minMemoGas, c => do
    let o ← call env 20 [codeHash] [argAt [codeHash] 0, minItemGas, minMemoGas] c
    pure (okUnit o, o.ctx)
  | _, .transfer dest amount gasLimit memo, c => do
    let o ← call env 21 [memo] [dest, amount, gasLimit, argAt [memo] 0] c
    pure (okUnit o, o.ctx)
  | _, .eject target codeHash, c => do
    let o ← call env 22 [codeHash] [target, argAt [codeHash] 0] c
    pure (okUnit o, o.ctx)
  | _, .query hash len, c => do
    let o ← call env 23 [hash] [argAt [hash] 0, len] c
    pure (decide (r7 o % 2 ^ 32 ≤ 3), o.ctx)
  | _, .solicit hash len, c => do
    let o ← call env 24 [hash] [argAt [hash] 0, len] c
    pure (okUnit o, o.ctx)
  | _, .forget hash len, c => do
    let o ← call env 25 [hash] [argAt [hash] 0, len] c
    pure (okUnit o, o.ctx)
  | _, .yield hash, c => do
    let o ← call env 26 [hash] [argAt [hash] 0] c
    pure (okUnit o, o.ctx)
  | _, .provide service preimage, c => do
    let o ← call env 27 [preimage] [service, argAt [preimage] 0, preimage.length] c
    pure (okUnit o, o.ctx)
  | _, .bless manager assigner designator registrar alwaysAcc, c => do
    let as := (List.replicate env.params.coreCount (Codec.fixed 4 assigner)).flatten
    let zs := (alwaysAcc.map fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g).flatten
    let o ← call env 15 [as, zs]
      [manager, argAt [as, zs] 0, designator, registrar, argAt [as, zs] 1, alwaysAcc.length] c
    pure (okUnit o, o.ctx)
  | _, .assign core queue assigner, c => do
    let o ← call env 16 [queue] [core, argAt [queue] 0, assigner] c
    pure (okUnit o, o.ctx)
  | _, .designate keys, c => do
    let o ← call env 17 [keys.flatten] [argAt [keys.flatten] 0, keys.length] c
    pure (okUnit o, o.ctx)

/-- How a run of `Spec.accumulate` ends: it returned, it panicked, or it ran out of operations. -/
inductive Stop
  | done
  | panicked
  | stopped
  deriving DecidableEq, Repr

/-- **Run a program for at most n operations** on the context (x, y). A panicking operation, like
    `Prog.panic`, ends the run `panicked`, with the context the call left. -/
def run : Nat → Prog AOp Unit → AccEnv → AccCtx → Stop × AccCtx
  | _, .pure _, _, c => (.done, c)
  | _, .panic, _, c => (.panicked, c)
  | 0, .call _ _, _, c => (.stopped, c)
  | n + 1, .call o k, env, c =>
    match step env o c with
    | some (b, c') => run n (k b) env c'
    | none => (.panicked, c)

/-- **What Ψ_A reports**, without the gas (GP eq. `accinvocation`, no hash returned): the state,
    transfers, yield and provisions of x after `done`, else of y. -/
def outcome : Stop × AccCtx → PartialState × List DeferredTransfer × Option (List UInt8) × Provisions
  | (.done, (x, _)) => (x.state, x.xfers, x.yield, x.provisions)
  | (_, (_, y)) => (y.state, y.xfers, y.yield, y.provisions)

/-- **The environment of bootstrap's accumulate**: full parameters, the entropy η'₀, the timeslot,
    the inputs and the code. -/
def accEnv (η : List UInt8) (t : Nat) (inputs : List AccumulateInput) (code : ByteArray) : AccEnv :=
  { params := Params.full, slot := t, entropy := η, inputs, code }

/-- **e′: the incoming transfers credited to s** (GP eq. `accinvocation`, as `psiA` forms it). -/
def credit (e : PartialState) (s : Nat) (inputs : List AccumulateInput) : PartialState :=
  let incoming := (inputs.filterMap fun | .transfer x => some x.amount | _ => none).sum
  match e.accounts.get? s with
  | some a => { e with accounts := e.accounts.insert s { a with balance := a.balance + incoming } }
  | none => e

/-- The code of service s in a state, as Ψ_A finds it. -/
def codeOf (e : PartialState) (s : Nat) : Option ByteArray := (e.accounts.get? s).bind (·.code)

/-- `psiA` is `psiARun` on the credited state. -/
theorem psiA_eq (params : Params) (η : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) :
    psiA params η e t s g inputs = psiARun params η (credit e s inputs) t s g inputs := rfl

end Services.Bootstrap.ASem
