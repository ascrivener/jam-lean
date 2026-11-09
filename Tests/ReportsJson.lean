import Tests.BlockJson
import Tests.StfRunner
import JAM.Disputes

/-!
# JSON readers shared by the disputes, assurances and reports vectors

Availability assignments ρ and validator keys, with the field names of davxy/jam-test-vectors
`v0.8.0`.
-/

namespace JAM.Tests.Json

open Lean (Json)
open PVM.Tests (field natField die)
open JAM.Tests.Stf (hexS)

def assignment (j : Json) : Except String AvailAssignment := do
  return { guarantee := ← guarantee (← field j "guarantee"), time := ← natField j "registered_slot" }

/-- ρ: one entry per core, `null` for none. -/
def rho (j : Json) : Except String AvailAssignments := do
  items j fun e => match e with
    | .null => pure none
    | v => do return some (← assignment v)

/-- The Ed25519 keys of a validator set. -/
def edKeys (j : Json) (k : String) : Except String (List (List UInt8)) :=
  list j k fun v => do return (← hexField v "ed25519").toList

/-- ρ for comparison: each entry's encoded guarantee and timeslot. -/
def showRho (ρ : AvailAssignments) : List String :=
  ρ.map fun
    | none => "none"
    | some a => s!"{hexS a.guarantee.encode}@{a.time}"

/-- The expected error of a vector, if any. -/
def expectedErr (j : Json) : Except String (Option String) := do
  let out ← field j "output"
  match out.getObjVal? "err" with
  | .ok e => return some (← e.getStr?)
  | .error _ => return none

/-- The signature oracle of the STF runners: every signature is rejected exactly when the vector
    expects `bad_signature`, and accepted otherwise (README note 29). -/
def sigOracle (expErr : Option String) : Crypto :=
  { edVerify := fun _ _ _ => expErr != some "bad_signature" }

end JAM.Tests.Json
