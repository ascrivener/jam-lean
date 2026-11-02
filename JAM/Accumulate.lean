import JAM.Host.General
import JAM.Blake2b

/-!
# The accumulate invocation Ψ_A and its host functions (GP v0.8.0 Appendix B)

* the partial state 𝕊 (eq. `partialstate`) and the implications 𝕃 (eq. `implications`);
* the accumulate host functions `bless`, `assign`, `designate`, `checkpoint`, `new`, `upgrade`,
  `transfer`, `eject`, `query`, `solicit`, `forget`, `yield`, `provide` (`sec:accumulatefunctions`);
* the mutator F, the wrapper G, the initializer I, the collapse C and Ψ_A itself
  (eq. `accinvocation`).
-/

namespace JAM

open PVM

instance : Inhabited ServiceAccount := ⟨{ codeHash := [], balance := 0, minAccGas := 0, minMemoGas := 0 }⟩

/-- The partial state 𝕊 (GP eq. `partialstate`): accounts **d**, staging keys **i**, authorizer
    queue **q**, manager m, assigners **a**, delegator v, registrar r, always-accumulate **z**. -/
structure PartialState where
  accounts : Accounts
  staging : List (List UInt8)
  authQueue : List (List (List UInt8))
  manager : Nat
  assigners : List Nat
  delegator : Nat
  registrar : Nat
  alwaysAcc : Std.ExtTreeMap Nat Nat

/-- (service, blob) pairs, ordered lexicographically. -/
instance : Ord (Nat × List UInt8) := lexOrd

/-- A set of provisions ⟦(ℕ_S, 𝔹)⟧ (GP eq. `implications`). Extensional, so the order in which
    `provide` calls are made is unobservable. -/
abbrev Provisions := Std.ExtTreeSet (Nat × List UInt8)

/-- The implications 𝕃 (GP eq. `implications`): service s, state **e**, next free id i, transfers
    **t**, yield y and provisions **p**. -/
structure Implications where
  id : Nat
  state : PartialState
  nextFree : Nat
  xfers : List DeferredTransfer := []
  yield : Option (List UInt8) := none
  provisions : Provisions := ∅

namespace Implications
/-- x_s ≡ (x_e)_d[x_s], the accumulating service's account. -/
def self (x : Implications) : ServiceAccount := x.state.accounts.getD x.id default
/-- x with x_s replaced. -/
def setSelf (x : Implications) (a : ServiceAccount) : Implications :=
  { x with state := { x.state with accounts := x.state.accounts.insert x.id a } }
end Implications

/-- The accumulation context: the regular and exceptional dimensions (x, y) ∈ 𝕃². -/
abbrev AccCtx := Implications × Implications

/-- The fixed part of an accumulate invocation's environment: chain parameters, the timeslot H_t,
    the entropy η'_0, the inputs **i** and the service code (for `grow_heap`). -/
structure AccEnv where
  params : Params
  slot : Nat
  entropy : List UInt8
  inputs : List AccumulateInput
  code : ByteArray

/-- check(i) (GP eq. `newserviceindex`): the first index in the sequence from i that is not an
    account. `fuel` bounds the search; |**d**| + 1 steps always suffice. -/
def checkId (d : Accounts) : Nat → Nat → Nat
  | 0, i => i
  | fuel + 1, i =>
    if d.contains i then checkId d fuel ((i - Constants.Cminpublicindex + 1) % (2 ^ 32 - 2 ^ 8 - Constants.Cminpublicindex) + Constants.Cminpublicindex)
    else i

namespace AccHost

open Result

/-- μ_{o…+n} if readable. -/
def readMem (μ : Memory) (o n : Nat) : Option (List UInt8) :=
  if μ.rangeReadable o n then some (μ.readN o n) else none

/-- Split a list into chunks of `k`. -/
def chunks (k : Nat) (xs : List UInt8) (n : Nat) : List (List UInt8) :=
  (List.range n).map fun i => (xs.drop (k * i)).take k

/-- Charge g and run the body on the regular dimension x (the common rules). -/
def charge (g gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (body : HostOut AccCtx → HostOut AccCtx) : HostOut AccCtx := charged g gas ω μ c body

def r7 (out : HostOut AccCtx) (v : Nat) : HostOut AccCtx := { out with regs := setR7 out.regs v }
def panic (out : HostOut AccCtx) : HostOut AccCtx := { out with status := .panic }
def updX (out : HostOut AccCtx) (x : Implications) : HostOut AccCtx := { out with ctx := (x, out.ctx.2) }

/-- Ω_B, `bless` = 15. -/
def bless (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let m := reg ω 7; let a := reg ω 8; let v := reg ω 9; let r := reg ω 10; let o := reg ω 11
  let n := reg ω 12
  let C := env.params.coreCount
  charge (Constants.CgasBconst + n * Constants.CgasBlinear) gas ω μ c fun out =>
    let x := c.1
    let as := (readMem μ a (4 * C)).map fun b => (chunks 4 b C).map Num.decodeLE
    let zs := (readMem μ o (12 * n)).map fun b =>
      (chunks 12 b n).map fun e => (Num.decodeLE (e.take 4), Num.decodeLE (e.drop 4))
    match as, zs with
    | some as, some zs =>
      if x.id ≠ x.state.manager then r7 out HUH
      else if ¬ (m < 2 ^ 32 ∧ v < 2 ^ 32 ∧ r < 2 ^ 32) then r7 out WHO
      else
        let st := { x.state with manager := m, assigners := as, delegator := v, registrar := r,
                                 alwaysAcc := Std.ExtTreeMap.ofList zs }
        r7 (updX out { x with state := st }) OK
    | _, _ => panic out

/-- Ω_A, `assign` = 16. -/
def assign (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let core := reg ω 7; let o := reg ω 8; let a := reg ω 9
  let Q := env.params.authQueueSize
  charge Constants.CgasA gas ω μ c fun out =>
    let x := c.1
    match readMem μ o (32 * Q) with
    | none => panic out
    | some q =>
      if core ≥ env.params.coreCount then r7 out CORE
      else if x.id ≠ x.state.assigners.getD core 0 then r7 out HUH
      else if a ≥ 2 ^ 32 then r7 out WHO
      else
        let st := { x.state with authQueue := x.state.authQueue.set core (chunks 32 q Q),
                                 assigners := x.state.assigners.set core a }
        r7 (updX out { x with state := st }) OK

/-- 𝕍 = {3c | c ∈ ℕ_{2…C+1}}, the valid validator key-set sizes (GP eq. `valcount`). -/
def validKeyCount (C z : Nat) : Bool := z % 3 == 0 && 2 ≤ z / 3 && z / 3 ≤ C

/-- Ω_D, `designate` = 17. -/
def designate (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let z := reg ω 8
  charge (Constants.CgasDconst + z * Constants.CgasDlinear) gas ω μ c fun out =>
    let x := c.1
    match readMem μ o (336 * z) with
    | none => panic out
    | some v =>
      if !validKeyCount env.params.coreCount z || x.id ≠ x.state.delegator then r7 out HUH
      else r7 (updX out { x with state := { x.state with staging := chunks 336 v z } }) OK

/-- Ω_C, `checkpoint` = 18: y' ≡ x, ω'_7 ≡ ϱ'. -/
def checkpoint (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  charge Constants.CgasC gas ω μ c fun out =>
    { out with ctx := (c.1, c.1), regs := setR7 ω out.gas.toNat }

/-- Ω_N, `new` = 19. -/
def new (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let l := reg ω 8; let g := reg ω 9; let m := reg ω 10; let f := reg ω 11
  let i := reg ω 12
  let S := Constants.Cminpublicindex
  charge Constants.CgasN gas ω μ c fun out =>
    let x := c.1
    let codeHash := if l < 2 ^ 32 then readMem μ o 32 else none
    match codeHash with
    | none => panic out
    | some ch =>
      let a0 : ServiceAccount :=
        { codeHash := ch, requests := Std.ExtTreeMap.ofList [((ch, l), [])], balance := 0,
          minAccGas := g, minMemoGas := m, created := env.slot, gratis := f, lastAcc := 0,
          parent := x.id }
      let a := { a0 with balance := a0.minBalance }
      let sBal : Int := (x.self.balance : Int) - a.minBalance
      let s := { x.self with balance := sBal.toNat }
      let d := x.state.accounts
      if f ≠ 0 ∧ x.id ≠ x.state.manager then r7 out HUH
      else if sBal < x.self.minBalance then r7 out CASH
      else if x.id = x.state.registrar ∧ i < S ∧ d.contains i then r7 out FULL
      else if x.id = x.state.registrar ∧ i < S then
        let d' := (d.insert i a).insert x.id s
        r7 (updX out { x with state := { x.state with accounts := d' } }) i
      else
        let iStar := checkId d (d.size + 1) (S + (x.nextFree - S + 42) % (2 ^ 32 - S - 2 ^ 8))
        let d' := (d.insert x.nextFree a).insert x.id s
        r7 (updX out { x with state := { x.state with accounts := d' }, nextFree := iStar }) x.nextFree

/-- Ω_U, `upgrade` = 20. -/
def upgrade (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let g := reg ω 8; let m := reg ω 9
  charge Constants.CgasU gas ω μ c fun out =>
    match readMem μ o 32 with
    | none => panic out
    | some h => r7 (updX out (c.1.setSelf { c.1.self with codeHash := h, minAccGas := g, minMemoGas := m })) OK

/-- Ω_T, `transfer` = 21, with g = 𝖬_T + t where t = l on success and 0 otherwise. -/
def transfer (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let dest := reg ω 7; let amount := reg ω 8; let l := reg ω 9; let o := reg ω 10
  let x := c.1
  let d := x.state.accounts
  let t := (readMem μ o env.params.memoSize).map fun memo =>
    ({ source := x.id, dest, amount, memo := ⟨memo.toArray⟩, gas := l } : DeferredTransfer)
  let b : Int := (x.self.balance : Int) - amount
  -- (c, t)
  let (code, tg) : Option Nat × Nat :=
    match t with
    | none => (none, 0)
    | some _ =>
      if !d.contains dest then (some WHO, 0)
      else if l < (d.getD dest default).minMemoGas then (some LOW, 0)
      else if b < x.self.minBalance then (some CASH, 0)
      else (some OK, l)
  charge (Constants.CgasT + tg) gas ω μ c fun out =>
    match code, t with
    | none, _ => panic out
    | some c', some t =>
      if c' ≠ OK then r7 out c'
      else
        let x' := { x with xfers := x.xfers ++ [t] }.setSelf { x.self with balance := b.toNat }
        r7 (updX out x') OK
    | some c', none => r7 out c'

/-- Ω_J, `eject` = 22. -/
def eject (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let dId := reg ω 7; let o := reg ω 8
  charge Constants.CgasJ gas ω μ c fun out =>
    let x := c.1
    let accts := x.state.accounts
    match readMem μ o 32 with
    | none => panic out
    | some h =>
      let dAcc := if dId ≠ x.id ∧ accts.contains dId then accts.get? dId else none
      match dAcc with
      | none => r7 out WHO
      | some da =>
        if da.codeHash ≠ Codec.fixed 32 x.id then r7 out WHO
        else
          let l := max 81 da.octets - 81
          if da.items ≠ 2 ∨ !da.requests.contains (h, l) then r7 out HUH
          else match da.requests.get? (h, l) with
            | some [_, y] =>
              if (y : Int) < (env.slot : Int) - env.params.expungePeriod then
                let s' := { x.self with balance := x.self.balance + da.balance }
                let d' := (accts.erase dId).insert x.id s'
                r7 (updX out { x with state := { x.state with accounts := d' } }) OK
              else r7 out HUH
            | _ => r7 out HUH

/-- Ω_Q, `query` = 23. -/
def query (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let z := reg ω 8
  charge Constants.CgasQ gas ω μ c fun out =>
    let set78 (a b : Nat) : HostOut AccCtx :=
      { out with regs := (out.regs.set 7 (UInt64.ofNat a)).set 8 (UInt64.ofNat b) }
    if z ≥ 2 ^ 32 then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        match c.1.self.requests.get? (h, z) with
        | none => set78 NONE 0
        | some [] => set78 0 0
        | some [x] => set78 (1 + 2 ^ 32 * x) 0
        | some [x, y] => set78 (2 + 2 ^ 32 * x) y
        | some [x, y, w] => set78 (3 + 2 ^ 32 * x) (y + 2 ^ 32 * w)
        | some _ => set78 NONE 0

/-- Ω_S, `solicit` = 24. -/
def solicit (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let z := reg ω 8
  charge Constants.CgasS gas ω μ c fun out =>
    let self := c.1.self
    if z ≥ 2 ^ 32 then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        let a : Option ServiceAccount :=
          match self.requests.get? (h, z) with
          | none => some { self with requests := self.requests.insert (h, z) [] }
          | some [x, y] => some { self with requests := self.requests.insert (h, z) [x, y, env.slot] }
          | some _ => none
        match a with
        | none => r7 out HUH
        | some a =>
          if a.balance < a.minBalance then r7 out FULL
          else r7 (updX out (c.1.setSelf a)) OK

/-- Ω_F, `forget` = 25. -/
def forget (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let z := reg ω 8
  charge Constants.CgasF gas ω μ c fun out =>
    let self := c.1.self
    let old (y : Nat) : Bool := (y : Int) < (env.slot : Int) - env.params.expungePeriod
    if z ≥ 2 ^ 32 then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        let drop := { self with requests := self.requests.erase (h, z), preimages := self.preimages.erase h }
        let a : Option ServiceAccount :=
          match self.requests.get? (h, z) with
          | some [] => some drop
          | some [_, y] => if old y then some drop else none
          | some [x] => some { self with requests := self.requests.insert (h, z) [x, env.slot] }
          | some [_, y, w] => if old y then some { self with requests := self.requests.insert (h, z) [w, env.slot] } else none
          | _ => none
        match a with
        | none => r7 out HUH
        | some a => r7 (updX out (c.1.setSelf a)) OK

/-- Ω_♉, `yield` = 26. -/
def yield (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  charge Constants.CgasTaurus gas ω μ c fun out =>
    match readMem μ (reg ω 7) 32 with
    | none => panic out
    | some h => r7 (updX out { c.1 with yield := some h }) OK

/-- Ω_♈, `provide` = 27. -/
def provide (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let z := reg ω 9
  charge (Constants.CgasAriesconst + memGas Constants.CgasArieslinear z) gas ω μ c fun out =>
    let x := c.1
    let s := if reg ω 7 = 2 ^ 64 - 1 then x.id else reg ω 7
    if z ≥ 2 ^ 32 then r7 out HUH
    else match readMem μ o z with
      | none => panic out
      | some i =>
        match x.state.accounts.get? s with
        | none => r7 out WHO
        | some a =>
          if a.requests.get? ((Blake2b.hash256 ⟨i.toArray⟩).toList, z) ≠ some [] then r7 out HUH
          else if x.provisions.contains (s, i) then r7 out HUH
          else r7 (updX out { x with provisions := x.provisions.insert (s, i) }) OK

/-- G: run a general function on x_s and write the account back into x (GP eq. `accinvocation`). -/
def onSelf (out : HostOut ServiceAccount) (c : AccCtx) : HostOut AccCtx :=
  ⟨out.status, out.gas, out.regs, out.mem, (c.1.setSelf out.ctx, c.2)⟩

/-- F ∈ 𝔉_{𝕃²} (GP eq. `accinvocation`): dispatch on the host-call id. An unknown id charges
    𝖬_∅ and returns WHAT (∞ if that exhausts the gas). -/
def dispatch (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let x := c.1
  let d := x.state.accounts
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ env.code c
  | 2 => hostFetch gas ω μ { params := env.params, entropy := some env.entropy, accInputs := some env.inputs } c
  | 3 => let o := hostLookup gas ω μ x.self x.id d (); ⟨o.status, o.gas, o.regs, o.mem, c⟩
  | 4 => let o := hostRead gas ω μ x.self x.id d (); ⟨o.status, o.gas, o.regs, o.mem, c⟩
  | 5 => onSelf (hostWrite gas ω μ x.self) c
  | 6 => let o := hostInfo gas ω μ x.id d (); ⟨o.status, o.gas, o.regs, o.mem, c⟩
  | 15 => bless env gas ω μ c
  | 16 => assign env gas ω μ c
  | 17 => designate env gas ω μ c
  | 18 => checkpoint gas ω μ c
  | 19 => new env gas ω μ c
  | 20 => upgrade gas ω μ c
  | 21 => transfer env gas ω μ c
  | 22 => eject env gas ω μ c
  | 23 => query gas ω μ c
  | 24 => solicit env gas ω μ c
  | 25 => forget env gas ω μ c
  | 26 => yield gas ω μ c
  | 27 => provide gas ω μ c
  | _ =>
    let g' : Int := (gas : Int) - Constants.Cgasunknown
    ⟨if g' < 0 then .oog else .cont, g', setR7 ω WHAT, μ, c⟩

end AccHost

/-- F as a host-call handler for Ψ_H (`PVM.HostFn`): ℤ_G gas is clamped at 0, which only happens
    together with ∞ (see the note on 𝔉_X in the README). -/
def accHostFn (env : AccEnv) : HostFn AccCtx := fun n gas ω μ c =>
  let o := AccHost.dispatch env n gas.toNat ω μ c
  ⟨o.status, UInt64.ofNat o.gas.toNat, o.regs, o.mem, o.ctx⟩

/-- The code of a service account: **c** where **p**[c_h] = ℰ(↕m, **c**) (GP §9, "Code and Gas"). -/
def ServiceAccount.code (a : ServiceAccount) : Option ByteArray := do
  let p ← a.preimages.get? a.codeHash
  let b : ByteArray := ⟨p.toArray⟩
  let (mLen, pos) ← Blob.decodeNat? b 0
  if pos + mLen > b.size then none
  some (b.extract (pos + mLen) b.size)

/-- The result of Ψ_A / Δ_1 (GP eq. `acconeout`): post-state, transfers, yield, gas used, provisions. -/
structure AccOut where
  state : PartialState
  xfers : List DeferredTransfer
  yield : Option (List UInt8)
  gasUsed : Nat
  provisions : Provisions

/-- I(**e**, s) (GP eq. `accinvocation`): the initial implications, with the next free id
    check((ℰ_4⁻¹(ℋ(ℰ(s, η'_0, H_t))) mod (2^32 − 𝖲 − 2^8)) + 𝖲). -/
def initImplications (e : PartialState) (s slot : Nat) (entropy : List UInt8) : Implications :=
  let S := Constants.Cminpublicindex
  let h := Blake2b.hash256 ⟨(Codec.nat s ++ entropy ++ Codec.nat slot).toArray⟩
  let i := Num.decodeLE (h.toList.take 4) % (2 ^ 32 - S - 2 ^ 8) + S
  { id := s, state := e, nextFree := checkId e.accounts (e.accounts.size + 1) i }

/-- Ψ_A(**e**, t, s, g, **i**) (GP eq. `accinvocation`). -/
def psiA (params : Params) (entropy : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) : AccOut :=
  let incoming := (inputs.filterMap fun | .transfer x => some x.amount | _ => none).sum
  let st : PartialState :=
    match e.accounts.get? s with
    | some a => { e with accounts := e.accounts.insert s { a with balance := a.balance + incoming } }
    | none => e
  let code := (st.accounts.get? s).bind (·.code)
  match code with
  | none => ⟨st, [], none, 0, ∅⟩
  | some c =>
    if c.size > Constants.Cmaxservicecodesize then ⟨st, [], none, 0, ∅⟩
    else
      let env : AccEnv := { params, slot := t, entropy, inputs, code := c }
      let x := initImplications st s t entropy
      let args : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
      let (u, o, (x, y)) := psiM c 5 (UInt64.ofNat g) args (accHostFn env) (x, x)
      match o with
      | .oog | .panic => ⟨y.state, y.xfers, y.yield, u, y.provisions⟩
      | .ok out =>
        if out.size = 32 then ⟨x.state, x.xfers, some out.toList, u, x.provisions⟩
        else ⟨x.state, x.xfers, x.yield, u, x.provisions⟩

end JAM
