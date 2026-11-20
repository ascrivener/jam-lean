import Services.Bootstrap.Acc.Final.Hyps

/-!
# `AccLogFail` as a bounty statement

`AccLogFailGoal` is T2's named hypothesis `AccLogFail` (`Final/Hyps.lean`), quantified exactly as
`AccHyps` quantifies its `logFail` field: for every code that is bootstrap's (`IsBootstrapCode`), its
PVM code with the code facts, and every environment with that code and the full parameters.

It is the statement of a witness bounty on the JAM Toaster: a proof of
`theorem Services.Bootstrap.Acc.Final.accLogFail_bounty : AccLogFailGoal`, checked by witness-lean's
Lean check. `AccLogFailGoal.logFail` shows that such a proof discharges `AccHypsAt.logFail` for every
code, program and environment `AccHyps` asks it of. Nothing here is assumed or proved about the
binary itself.
-/

namespace Services.Bootstrap.Acc.Final

open PVM JAM Services.Bootstrap

/-- **`AccLogFail` for bootstrap's code** (the statement of the `AccLogFail` bounty): `AccLogFail`
    at the heap bound 1044430 and the stack 4278050816 … 4278059008, for every code that is
    bootstrap's, its PVM code with the code facts, and every environment with that code and the
    full parameters, the premises under which `AccHyps` asks for `AccHypsAt.logFail`. -/
def AccLogFailGoal : Prop :=
  ∀ (code : ByteArray) (jb : JamBlob), IsBootstrapCode code → JamBlob.parse? code = some jb →
    ∀ (P : Program), Code.HasCode jb.code P → CodeX.HasCodeX jb.code P → CodeA.HasCodeA jb.code P →
      CodeF.HasCodeF jb.code P →
    ∀ (env : AccEnv), env.code = code → env.params = Params.full →
      AccLogFail jb.code env 1044430 4278050816 4278059008

/-- A proof of `AccLogFailGoal` gives `AccHypsAt.logFail` wherever `AccHyps` asks for it: for every
    code and blob, program with the code facts, environment and timeslot that `AccHyps` quantifies
    over. -/
theorem AccLogFailGoal.logFail (h : AccLogFailGoal) (code : ByteArray) (jb : JamBlob)
    (hb : IsBootstrapCode code) (hp : JamBlob.parse? code = some jb) (P : Program)
    (h1 : Code.HasCode jb.code P) (h2 : CodeX.HasCodeX jb.code P) (h3 : CodeA.HasCodeA jb.code P)
    (h4 : CodeF.HasCodeF jb.code P) (env : AccEnv) (hc : env.code = code)
    (hpar : env.params = Params.full) :
    AccLogFail jb.code env 1044430 4278050816 4278059008 :=
  h code jb hb hp P h1 h2 h3 h4 env hc hpar

/-- `AccLogFailGoal` is exactly `AccHyps`'s `logFail` obligation: it holds iff `AccLogFail` holds
    for every code, blob, program, environment and timeslot under `AccHyps`'s premises. -/
theorem accLogFailGoal_iff : AccLogFailGoal ↔
    ∀ (code : ByteArray) (jb : JamBlob), IsBootstrapCode code → JamBlob.parse? code = some jb →
      ∀ (P : Program), Code.HasCode jb.code P → CodeX.HasCodeX jb.code P → CodeA.HasCodeA jb.code P →
        CodeF.HasCodeF jb.code P →
      ∀ (env : AccEnv) (_now : Nat), env.code = code → env.params = Params.full →
        AccLogFail jb.code env 1044430 4278050816 4278059008 :=
  ⟨fun h code jb hb hp P h1 h2 h3 h4 env _ hc hpar => h code jb hb hp P h1 h2 h3 h4 env hc hpar,
   fun h code jb hb hp P h1 h2 h3 h4 env hc hpar => h code jb hb hp P h1 h2 h3 h4 env 0 hc hpar⟩

/-- `AccHyps` gives `AccLogFailGoal`: the bounty asks for no more than T2's hypotheses already
    assume. -/
theorem AccLogFailGoal.of_accHyps {B : Handlers.InstrRep.InstrRep} {C : Spec.Consts} (h : AccHyps B C) :
    AccLogFailGoal :=
  fun code jb hb hp P h1 h2 h3 h4 env hc hpar =>
    (h code jb hb hp P h1 h2 h3 h4 env 0 hc hpar).logFail

end Services.Bootstrap.Acc.Final
