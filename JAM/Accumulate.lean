import JAM.Host.General
import JAM.Blake2b
import PVM.FastHost

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
  /-- x_m: the services whose accounts this accumulation modified (GP v0.8.1 eq. `implications`) -/
  modified : Std.ExtTreeSet Nat := ∅

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

/-- TEMPORARY until JAM/Constants.lean is regenerated from GP v0.8.1: 𝖬_V = 1000 (GP v0.8.1
    definitions.tex). Remove when `Constants.CgasV` exists. -/
def Constants.CgasV : Nat := 1000

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

/-- s for ω = 2^64 − 1, otherwise ω (the "own service" sentinel of GP v0.8.1 Appendix B). -/
def tgt (w s : Nat) : Nat := if w = 2 ^ 64 - 1 then s else w

/-- x_s ∈ {d, E(**d**, d)}: the accumulating service may make non-privileged changes to d
    (GP v0.8.1 §9 "Supervisors"). -/
def mayModify (x : Implications) (d : Nat) : Bool :=
  x.id == d || x.id == effectiveSupervisor x.state.accounts d

/-- x with **d**[d] set to `a` and d added to the modified set x_m (GP v0.8.1). -/
def putAcct (x : Implications) (d : Nat) (a : ServiceAccount) : Implications :=
  { x with state := { x.state with accounts := x.state.accounts.insert d a },
           modified := x.modified.insert d }

/-- The account would exceed GP v0.8.1's footprint bounds: a_t > a_b + a_b', a_i ∉ ℕ_{2^32} or
    a_o ∉ ℕ_{2^64} (Ω_W and Ω_S, GP #581). -/
def overFull (a : ServiceAccount) : Bool :=
  a.minBalance > a.balance + a.supervisorBalance || a.items ≥ 2 ^ 32 || a.octets ≥ 2 ^ 64

/-- Ω_W(ϱ, ω, μ, (x, y)), `write` = 5 (GP v0.8.1): set (or, for v_Z = 0, delete) the storage value
    of service d = ω_7 (x_s for 2^64 − 1) under the key at ω_8 (length ω_9) to the octets at ω_10
    (length ω_11). WHO if d is not a service; HUH unless x_s ∈ {d, E(**d**, d)}; FULL if the result
    is `overFull`; otherwise ω'_7 is the previous value's length (NONE if none) and d joins x_m.
    g = 𝖬_{W,c} + 𝔊(𝖬_{W,k,ℓ}, k_Z) + 𝔊(𝖬_{W,v,ℓ}, v_Z). -/
def write (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let kO := reg ω 8; let kZ := reg ω 9; let vO := reg ω 10; let vZ := reg ω 11
  let g := Constants.CgasWconst + memGas Constants.CgasWkeylinear kZ +
    memGas Constants.CgasWvallinear vZ
  charge g gas ω μ c fun out =>
    let x := c.1
    let d := tgt (reg ω 7) x.id
    match readMem μ kO kZ, readMem μ vO vZ with
    | some k, some v =>
      match x.state.accounts.get? d with
      | none => r7 out WHO
      | some a =>
        if !mayModify x d then r7 out HUH
        else
          let a' := a.storageWrite k v
          if overFull a' then r7 out FULL
          else
            let l := match a.storageGet k with
              | some old => old.length
              | none => NONE
            r7 (updX out (putAcct x d a')) l
    | _, _ => panic out

/-- Ω_B, `bless` = 16 (GP v0.8.1, GP #558): set the privileges. Each of m, v, r is kept for
    2^64 − 1; **a** is kept for a = 2^64 − 1 and each of its entries for 2^32 − 1; **z** is kept for
    o = 2^64 − 1. The manager may set anything; another service only hands over the roles it holds
    (delegator, registrar, the assigner of a core) and changes nothing else. -/
def bless (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let m := reg ω 7; let a := reg ω 8; let v := reg ω 9; let r := reg ω 10; let o := reg ω 11
  let n := reg ω 12
  let C := env.params.coreCount
  charge (Constants.CgasBconst + n * Constants.CgasBlinear) gas ω μ c fun out =>
    let x := c.1
    let p := x.state
    let D (w y : Nat) : Nat := if w = 2 ^ 64 - 1 then y else w
    let D32 (w y : Nat) : Nat := if w = 2 ^ 32 - 1 then y else w
    let (m', v', r') := (D m p.manager, D v p.delegator, D r p.registrar)
    let as : Option (List Nat) :=
      if a = 2 ^ 64 - 1 then some p.assigners
      else (readMem μ a (4 * C)).map fun b =>
        (List.range C).map fun i => D32 (Num.decodeLE ((b.drop (4 * i)).take 4)) (p.assigners.getD i 0)
    let zs : Option (List (Nat × Nat)) :=
      if o = 2 ^ 64 - 1 then some p.alwaysAcc.toList
      else (readMem μ o (12 * n)).map fun b =>
        (chunks 12 b n).map fun e => (Num.decodeLE (e.take 4), Num.decodeLE (e.drop 4))
    match as, zs with
    | some as, some zs =>
      let z : Std.ExtTreeMap Nat Nat := Std.ExtTreeMap.ofList zs
      let allowed : Bool := x.id == p.manager ||
        (m' == p.manager &&
         (List.range C).all (fun i => as.getD i 0 == p.assigners.getD i 0 || x.id == p.assigners.getD i 0) &&
         (v' == p.delegator || x.id == p.delegator) && (r' == p.registrar || x.id == p.registrar) &&
         z == p.alwaysAcc)
      if !allowed || (o ≠ 2 ^ 64 - 1 && z.size ≠ n) then r7 out HUH
      else if ¬ (m' < 2 ^ 32 ∧ v' < 2 ^ 32 ∧ r' < 2 ^ 32) then r7 out WHO
      else
        let st := { p with manager := m', assigners := as, delegator := v', registrar := r',
                           alwaysAcc := z }
        r7 (updX out { x with state := st }) OK
    | _, _ => panic out

/-- Ω_A, `assign` = 17 (GP v0.8.1; unchanged apart from its number). -/
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

/-- Ω_D, `designate` = 18 (GP v0.8.1; unchanged apart from its number). -/
def designate (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 7; let z := reg ω 8
  charge (Constants.CgasDconst + z * Constants.CgasDlinear) gas ω μ c fun out =>
    let x := c.1
    match readMem μ o (336 * z) with
    | none => panic out
    | some v =>
      if !validKeyCount env.params.coreCount z || x.id ≠ x.state.delegator then r7 out HUH
      else r7 (updX out { x with state := { x.state with staging := chunks 336 v z } }) OK

/-- Ω_C, `checkpoint` = 19: y' ≡ x, ω'_7 ≡ ϱ*. -/
def checkpoint (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  charge Constants.CgasC gas ω μ c fun out =>
    { out with ctx := (c.1, c.1), regs := setR7 ω out.gas.toNat }

/-- Ω_N, `new` = 20 (GP v0.8.1, junior services GP #539). Service s = ω_7 (x_s for 2^64 − 1)
    funds a new account whose code hash c, request length l, gas limits g, m and gratis offset f are
    the 60 octets at ω_10, with the desired id i = ω_8 and the mode x = ω_9:
    the new account's threshold a_t is paid from s's balance (x ∈ {0, 2}) or supervisor balance
    (x ∈ {1, 3}) and lands in the new account's balance (x ∈ {0, 1}) or supervisor balance
    (x ∈ {2, 3}). The new account's supervisor is x_s, recorded with x_s's creation slot. -/
def new (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let i := reg ω 8; let mode := reg ω 9; let o := reg ω 10
  let S := Constants.Cminpublicindex
  charge Constants.CgasN gas ω μ c fun out =>
    let x := c.1
    let s := tgt (reg ω 7) x.id
    let p := x.state
    let d := p.accounts
    match readMem μ o 60 with
    | none => panic out
    | some e =>
      let ch := e.take 32
      let l := Num.decodeLE ((e.drop 32).take 4)
      let g := Num.decodeLE ((e.drop 36).take 8)
      let m := Num.decodeLE ((e.drop 44).take 8)
      let f := Num.decodeLE ((e.drop 52).take 8)
      let a0 : ServiceAccount := ServiceAccount.requestSet
        { codeHash := ch, balance := 0, supervisor := x.id, supervisorCreated := x.self.created,
          minAccGas := g, minMemoGas := m, created := env.slot, gratis := f, lastAcc := 0,
          parent := x.id } ch l []
      let t := a0.minBalance
      let b := if mode = 0 ∨ mode = 1 then t else 0
      let a := { a0 with balance := b, supervisorBalance := t - b }
      let (i', iStar) :=
        if x.id = p.registrar ∧ i < S then (i, x.nextFree)
        else (x.nextFree, checkId d (d.size + 1) (S + (x.nextFree - S + 42) % (2 ^ 32 - S - 2 ^ 8)))
      if l ≥ ServiceAccount.requestLenBound then r7 out HUH
      else match d.get? s with
      | none => r7 out WHO
      | some sa =>
        let fromBal := mode = 0 ∨ mode = 2
        let allowed : Bool :=
          if fromBal then mayModify x s else x.id == effectiveSupervisor d s
        if mode > 3 || !allowed || (f ≠ 0 && x.id ≠ p.manager) then r7 out HUH
        else
          let bal : Int := if fromBal then (sa.balance : Int) - t else sa.balance
          let sbal : Int := if fromBal then sa.supervisorBalance else (sa.supervisorBalance : Int) - t
          if bal < 0 ∨ sbal < 0 ∨ bal + sbal < sa.minBalance then r7 out CASH
          else if x.id = p.registrar ∧ i < S ∧ d.contains i then r7 out FULL
          else
            let sa' := { sa with balance := bal.toNat, supervisorBalance := sbal.toNat }
            let x' := putAcct { x with state := { p with accounts := d.insert i' a },
                                        nextFree := iStar } s sa'
            r7 (updX out x') i'

/-- Ω_V, `supervisor` = 29 (GP v0.8.1, GP #539): service d = ω_7's supervisor becomes u = ω_8
    (each x_s for 2^64 − 1), recorded with u's creation slot. WHO unless both are services; HUH
    unless x_s = E(**d**, d). -/
def supervisor (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  charge Constants.CgasV gas ω μ c fun out =>
    let x := c.1
    let dd := tgt (reg ω 7) x.id
    let u := tgt (reg ω 8) x.id
    let accts := x.state.accounts
    match accts.get? dd, accts.get? u with
    | some a, some ua =>
      if x.id ≠ effectiveSupervisor accts dd then r7 out HUH
      else r7 (updX out (putAcct x dd { a with supervisor := u, supervisorCreated := ua.created })) OK
    | _, _ => r7 out WHO

/-- Ω_U, `upgrade` = 21 (GP v0.8.1): set service d = ω_7's code hash (at ω_8) and gas limits
    (ω_9, ω_10). WHO if d is not a service; HUH unless x_s ∈ {d, E(**d**, d)}. -/
def upgrade (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let g := reg ω 9; let m := reg ω 10
  charge Constants.CgasU gas ω μ c fun out =>
    let x := c.1
    let d := tgt (reg ω 7) x.id
    match readMem μ o 32 with
    | none => panic out
    | some h =>
      match x.state.accounts.get? d with
      | none => r7 out WHO
      | some a =>
        if !mayModify x d then r7 out HUH
        else r7 (updX out (putAcct x d { a with codeHash := h, minAccGas := g, minMemoGas := m })) OK

/-- Ω_T, `transfer` = 22 (GP v0.8.1, GP #539), with g = 𝖬_T + t where t = l for a deferred transfer
    that succeeds and 0 otherwise. Source s = ω_7 and destination d = ω_8 (each x_s for 2^64 − 1),
    mode x = ω_9, amount ω_10, gas limit l = ω_11, memo at o = ω_12: x ∈ {0, 2} debits s's balance
    and {1, 3} its supervisor balance; x ∈ {0, 1} credits d's balance and {2, 3} its supervisor
    balance. With o = 0 the credit is immediate; otherwise a deferred transfer carries it. -/
def transfer (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let mode := reg ω 9; let amount := reg ω 10; let l := reg ω 11; let o := reg ω 12
  let x := c.1
  let src := tgt (reg ω 7) x.id
  let dst := tgt (reg ω 8) x.id
  let d := x.state.accounts
  let toSup := mode = 2 ∨ mode = 3
  let fromBal := mode = 0 ∨ mode = 2
  let t : Option (List DeferredTransfer) :=
    if o = 0 then some []
    else (readMem μ o env.params.memoSize).map fun memo =>
      [({ source := src, dest := dst, destSupervisor := toSup, amount, memo := ⟨memo.toArray⟩,
          gas := l } : DeferredTransfer)]
  -- d' after the debit, and after the immediate credit when o = 0
  let d1 : Accounts := match d.get? src with
    | some sa => d.insert src
        (if fromBal then { sa with balance := sa.balance - amount }
         else { sa with supervisorBalance := sa.supervisorBalance - amount })
    | none => d
  let d2 : Accounts := if o ≠ 0 then d1 else match d1.get? dst with
    | some da => d1.insert dst
        (if toSup then { da with supervisorBalance := da.supervisorBalance + amount }
         else { da with balance := da.balance + amount })
    | none => d1
  let ps : Bool := if fromBal then mayModify x src else x.id == effectiveSupervisor d src
  let pd : Bool := o ≠ 0 || (mayModify x dst && ((mode = 1 ∨ mode = 2) || src ≠ dst))
  -- the debited balances, as integers (the source's other balance is unchanged)
  let (sb, ssb, smin) : Int × Int × Nat := match d.get? src with
    | some sa =>
      if fromBal then ((sa.balance : Int) - amount, sa.supervisorBalance, sa.minBalance)
      else (sa.balance, (sa.supervisorBalance : Int) - amount, sa.minBalance)
    | none => (0, 0, 0)
  let (code, tg) : Option Nat × Nat :=
    match t with
    | none => (none, 0)
    | some _ =>
      if !d.contains src || !d.contains dst then (some WHO, 0)
      else if mode > 3 || !ps || !pd then (some HUH, 0)
      else if o ≠ 0 && l < (d.getD dst default).minMemoGas then (some LOW, 0)
      else if sb < 0 ∨ ssb < 0 ∨ sb + ssb < smin then (some CASH, 0)
      else if o = 0 then (some OK, 0)
      else (some OK, l)
  charge (Constants.CgasT + tg) gas ω μ c fun out =>
    match code, t with
    | none, _ => panic out
    | some c', some t =>
      if c' ≠ OK then r7 out c'
      else
        let w : List Nat := if o = 0 then [src, dst] else [src]
        let x' := { x with state := { x.state with accounts := d2 }, xfers := x.xfers ++ t,
                           modified := w.foldl (fun s i => s.insert i) x.modified }
        r7 (updX out x') OK
    | some c', none => r7 out c'

/-- Ω_J, `eject` = 23 (GP v0.8.1): remove service d = ω_7 and credit its balance and supervisor
    balance to x_s. WHO if d is not a service; HUH if d = x_s, x_s ≠ E(**d**, d), d was created in
    this slot, or d still has items. -/
def eject (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let dId := reg ω 7
  charge Constants.CgasJ gas ω μ c fun out =>
    let x := c.1
    let accts := x.state.accounts
    match accts.get? dId with
    | none => r7 out WHO
    | some da =>
      if dId = x.id ∨ x.id ≠ effectiveSupervisor accts dId ∨ da.created = env.slot ∨ da.items ≠ 0 then
        r7 out HUH
      else
        let s' := { x.self with balance := x.self.balance + da.balance + da.supervisorBalance }
        let d' := (accts.erase dId).insert x.id s'
        r7 (updX out { x with state := { x.state with accounts := d' },
                               modified := (x.modified.insert dId).insert x.id }) OK

/-- Ω_Q, `query` = 24 (GP v0.8.1): the request (h, z) of service ω_7 (x_s for 2^64 − 1), with h
    at ω_8 and z = ω_9. HUH if z ∉ ℕ_L; WHO if ω_7 names no service. -/
def query (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let z := reg ω 9
  charge Constants.CgasQ gas ω μ c fun out =>
    let set78 (a b : Nat) : HostOut AccCtx :=
      { out with regs := (out.regs.set 7 (UInt64.ofNat a)).set 8 (UInt64.ofNat b) }
    if z ≥ ServiceAccount.requestLenBound then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        match namedAccount c.1.self c.1.state.accounts (reg ω 7) with
        | none => r7 out WHO
        | some s =>
          match s.requestGet h z with
          | none => set78 NONE 0
          | some [] => set78 0 0
          | some [x] => set78 (1 + 2 ^ 32 * x) 0
          | some [x, y] => set78 (2 + 2 ^ 32 * x) y
          | some [x, y, w] => set78 (3 + 2 ^ 32 * x) (y + 2 ^ 32 * w)
          | some _ => set78 NONE 0

/-- Ω_S, `solicit` = 25 (GP v0.8.1): solicit (h, z) for service d = ω_7 (x_s for 2^64 − 1), h at
    ω_8, z = ω_9. HUH if z ∉ ℕ_L; WHO if d is not a service; HUH unless x_s ∈ {d, E(**d**, d)} or
    if the request cannot be (re-)solicited; FULL if the result is `overFull` (GP #581). -/
def solicit (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let z := reg ω 9
  charge Constants.CgasS gas ω μ c fun out =>
    let x := c.1
    let d := tgt (reg ω 7) x.id
    if z ≥ ServiceAccount.requestLenBound then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        match x.state.accounts.get? d with
        | none => r7 out WHO
        | some a =>
          let a' : Option ServiceAccount :=
            match a.requestGet h z with
            | none => some (a.requestSet h z [])
            | some [p, q] => some (a.requestSet h z [p, q, env.slot])
            | some _ => none
          match a' with
          | none => r7 out HUH
          | some a' =>
            if !mayModify x d then r7 out HUH
            else if overFull a' then r7 out FULL
            else r7 (updX out (putAcct x d a')) OK

/-- Ω_F, `forget` = 26 (GP v0.8.1): forget (h, z) for service d = ω_7 (x_s for 2^64 − 1), h at
    ω_8, z = ω_9. HUH if z ∉ ℕ_L; WHO if d is not a service; HUH unless x_s ∈ {d, E(**d**, d)} or
    if the request cannot be forgotten now. -/
def forget (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let z := reg ω 9
  charge Constants.CgasF gas ω μ c fun out =>
    let x := c.1
    let d := tgt (reg ω 7) x.id
    let old (y : Nat) : Bool := (y : Int) < (env.slot : Int) - env.params.expungePeriod
    if z ≥ ServiceAccount.requestLenBound then r7 out HUH
    else match readMem μ o 32 with
      | none => panic out
      | some h =>
        match x.state.accounts.get? d with
        | none => r7 out WHO
        | some a =>
          let drop := { a.requestErase h z with preimages := a.preimages.erase h }
          let a' : Option ServiceAccount :=
            match a.requestGet h z with
            | some [] => some (a.requestErase h z)
            | some [_, y] => if old y then some drop else none
            | some [p] => some (a.requestSet h z [p, env.slot])
            | some [_, y, w] => if old y then some (a.requestSet h z [w, env.slot]) else none
            | _ => none
          match a' with
          | some a' => if !mayModify x d then r7 out HUH else r7 (updX out (putAcct x d a')) OK
          | none => r7 out HUH

/-- Ω_♉, `yield` = 27. -/
def yield (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  charge Constants.CgasTaurus gas ω μ c fun out =>
    match readMem μ (reg ω 7) 32 with
    | none => panic out
    | some h => r7 (updX out { c.1 with yield := some h }) OK

/-- Ω_♈, `provide` = 28 (GP v0.8.1): HUH first if z ∉ ℕ_L. -/
def provide (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let o := reg ω 8; let z := reg ω 9
  charge (Constants.CgasAriesconst + memGas Constants.CgasArieslinear z) gas ω μ c fun out =>
    let x := c.1
    let s := tgt (reg ω 7) x.id
    if z ≥ ServiceAccount.requestLenBound then r7 out HUH
    else match readMem μ o z with
      | none => panic out
      | some i =>
        match x.state.accounts.get? s with
        | none => r7 out WHO
        | some a =>
          if a.requestGet (Blake2b.hash256 ⟨i.toArray⟩).toList z ≠ some [] then r7 out HUH
          else if x.provisions.contains (s, i) then r7 out HUH
          else r7 (updX out { x with provisions := x.provisions.insert (s, i) }) OK

/-- F ∈ 𝔉_{𝕃²} (GP v0.8.1 eq. `accinvocation`): dispatch on the host-call id. An unknown id
    charges 𝖬_∅ and returns WHAT (∞ if that exhausts the gas). -/
def dispatch (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx) : HostOut AccCtx :=
  let x := c.1
  let d := x.state.accounts
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ env.code c
  | 2 => hostFetch gas ω μ { params := env.params, entropy := some env.entropy, accInputs := some env.inputs } c
  | 3 => hostLookup gas ω μ x.self d c
  | 4 => hostRead gas ω μ x.self d c
  | 5 => write gas ω μ c
  | 6 => hostInfo gas ω μ x.self d c
  | 16 => bless env gas ω μ c
  | 17 => assign env gas ω μ c
  | 18 => designate env gas ω μ c
  | 19 => checkpoint gas ω μ c
  | 20 => new env gas ω μ c
  | 21 => upgrade gas ω μ c
  | 22 => transfer env gas ω μ c
  | 23 => eject env gas ω μ c
  | 24 => query gas ω μ c
  | 25 => solicit env gas ω μ c
  | 26 => forget env gas ω μ c
  | 27 => yield gas ω μ c
  | 28 => provide gas ω μ c
  | 29 => supervisor gas ω μ c
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

/-- The result of Ψ_A / Δ_1 (GP v0.8.1 eq. `acconeout`): post-state, the modified services, transfers,
    yield, gas used, provisions. -/
structure AccOut where
  state : PartialState
  /-- the services whose accounts this accumulation modified (GP v0.8.1) -/
  modified : Std.ExtTreeSet Nat := ∅
  xfers : List DeferredTransfer
  yield : Option (List UInt8)
  gasUsed : Nat
  provisions : Provisions

/-- I(**e**, **m**, s) (GP v0.8.1 eq. `accinvocation`): the initial implications, with the
    modified set **m** and the next free id check((ℰ_4⁻¹(ℋ(ℰ(s, η'_0, H_t))) mod (2^32 − 𝖲 − 2^8)) + 𝖲). -/
def initImplications (e : PartialState) (s slot : Nat) (entropy : List UInt8)
    (m : Std.ExtTreeSet Nat := ∅) : Implications :=
  let S := Constants.Cminpublicindex
  let h := Blake2b.hash256 ⟨(Codec.nat s ++ entropy ++ Codec.nat slot).toArray⟩
  let i := Num.decodeLE (h.toList.take 4) % (2 ^ 32 - S - 2 ^ 8) + S
  { id := s, state := e, nextFree := checkId e.accounts (e.accounts.size + 1) i, modified := m }

/-- Ψ_A from the state **e**' with the incoming transfers already credited and the modified set
    **m**: look up s's code and run it (GP v0.8.1 eq. `accinvocation`, the cases after **e**' is
    formed). -/
def psiARun (params : Params) (entropy : List UInt8) (st : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) (m : Std.ExtTreeSet Nat := ∅) : AccOut :=
  let code := (st.accounts.get? s).bind (·.code)
  match code with
  | none => ⟨st, m, [], none, 0, ∅⟩
  | some c =>
    if c.size > Constants.Cmaxservicecodesize then ⟨st, m, [], none, 0, ∅⟩
    else
      let env : AccEnv := { params, slot := t, entropy, inputs, code := c }
      let x := initImplications st s t entropy m
      let args : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
      let (u, o, (x, y)) := psiM c 5 (UInt64.ofNat g) args (accHostFn env) (x, x)
      match o with
      | .oog | .panic => ⟨y.state, y.modified, y.xfers, y.yield, u, y.provisions⟩
      | .ok out =>
        if out.size = 32 then ⟨x.state, x.modified, x.xfers, some out.toList, u, x.provisions⟩
        else ⟨x.state, x.modified, x.xfers, x.yield, u, x.provisions⟩

/-- Ψ_A(**e**, t, s, g, **i**) (GP v0.8.1 eq. `accinvocation`): nothing if s is not a service;
    otherwise credit the incoming transfers to s's balance or, for those with the destination-
    supervisor flag, its supervisor balance, mark s modified if any transfer came in, then run s's
    code (`psiARun`). -/
def psiA (params : Params) (entropy : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) : AccOut :=
  match e.accounts.get? s with
  | none => ⟨e, ∅, [], none, 0, ∅⟩
  | some a =>
    let xs := inputs.filterMap fun | .transfer x => some x | _ => none
    let toBal := ((xs.filter (!·.destSupervisor)).map (·.amount)).sum
    let toSup := ((xs.filter (·.destSupervisor)).map (·.amount)).sum
    let st : PartialState :=
      let a' := { a with balance := a.balance + toBal, supervisorBalance := a.supervisorBalance + toSup }
      { e with accounts := e.accounts.insert s a' }
    let m : Std.ExtTreeSet Nat := if xs.isEmpty then ∅ else (∅ : Std.ExtTreeSet Nat).insert s
    psiARun params entropy st t s g inputs m

end JAM
