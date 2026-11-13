import Services.Bootstrap.ASem
import PVM.Theorems.InitMem
import PVM.Logic.Steps
import Services.Witness.Lift
import Services.Bootstrap.Acc.Inputs.FetchStep

/-!
# Evaluating `ASem`'s operations

The memory and registers an `ASem` operation hands the model's host function:
- every octet from 2¹⁶ below 2³² is writable (`argMem_writable`);
- argument k reads back at `argAt args k` (`argMem_readN`), when the arguments fit below `outBase`;
- ω₇, ω₈, … hold the given values (`reg_argRegs`).
-/

namespace Services.Bootstrap.ASem

open PVM JAM Services.Bootstrap.Spec

theorem argMem_writable (args : List Bytes) {a : Nat} (h1 : argBase ≤ a) (h2 : a < 2 ^ 32) :
    (argMem args).writable a = true := by
  unfold argMem argBase at *
  rw [Memory.writable_writeN, Memory.writable_setPages,
    if_pos (by simp only [pageSize]; constructor <;> omega)]
  rfl

theorem argMem_readable (args : List Bytes) {a : Nat} (h1 : argBase ≤ a) (h2 : a < 2 ^ 32) :
    (argMem args).readable a = true :=
  Memory.readable_of_writable (argMem_writable args h1 h2)

/-- The octets of a flattened list from one element's offset are that element. -/
theorem flatten_drop_take (args : List Bytes) (k : Nat) (hk : k < args.length) :
    ((args.flatten.drop ((args.take k).map List.length).sum).take (args[k]).length) = args[k] := by
  induction args generalizing k with
  | nil => simp at hk
  | cons b bs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have e : List.drop (b.length + ((bs.take k).map List.length).sum) (b ++ bs.flatten) =
          List.drop ((bs.take k).map List.length).sum bs.flatten := by simp
      simp only [List.map_take] at e ih ⊢
      rw [e]
      have := ih k (by simp at hk; omega)
      simpa [List.map_take] using this

/-- **Argument k reads back** at `argAt args k`, when all the arguments fit below `outBase`. -/
theorem argMem_readN (args : List Bytes) (k : Nat) (hk : k < args.length)
    (hfit : argBase + args.flatten.length ≤ outBase) :
    (argMem args).readN (argAt args k) (args[k]).length = args[k] := by
  unfold argMem argAt
  have hsum : ((args.take k).map List.length).sum + (args[k]).length ≤ args.flatten.length := by
    rw [List.length_flatten]
    have e1 : (args.map List.length).sum =
        ((args.take k).map List.length).sum + ((args.drop k).map List.length).sum := by
      rw [← List.sum_append, ← List.map_append, List.take_append_drop]
    rw [List.drop_eq_getElem_cons hk] at e1
    simp only [List.map_cons, List.sum_cons] at e1
    omega
  apply List.ext_getElem
  · simp [Memory.readN]
  · intro j hj1 hj2
    simp only [Memory.readN, List.getElem_map, List.getElem_range]
    unfold outBase argBase at hfit
    rw [show argBase + ((args.take k).map List.length).sum + j = argBase + (((args.take k).map List.length).sum + j)
      by omega]
    have := PVM.Memory.read_writeN_at (Memory.empty.setPages 16 (2 ^ 20 - 16) (some .write)) argBase
      args.flatten (by unfold two32; omega) (((args.take k).map List.length).sum + j) (by simp at hj1; omega)
    rw [this]
    have e := flatten_drop_take args k hk
    have g := List.getElem_of_eq e.symm hj2
    simp only [List.getElem_take, List.getElem_drop] at g
    exact g.symm

/-- The registers `argRegs vals`: ω₇, ω₈, … are `vals`. -/
theorem reg_argRegs (vals : List Nat) (k : Fin 13) (hk : 7 ≤ k.val) (hv : vals.getD (k.val - 7) 0 < 2 ^ 64) :
    reg (argRegs vals) k = vals.getD (k.val - 7) 0 := by
  unfold reg argRegs Regs.get
  have e : (Vector.ofFn (fun k : Fin 13 => if 7 ≤ k.val then UInt64.ofNat (vals.getD (k.val - 7) 0) else 0))[k] =
      UInt64.ofNat (vals.getD (k.val - 7) 0) := by
    simp [hk]
  rw [e]
  exact UInt64.toNat_ofNat_of_lt' hv

/-- **Ω_R on this service, evaluated**: the key at kO (kZ octets) readable, enough gas, and the
    output range writable. The call continues; ω₇ is the value's length (NONE if absent) and the first
    z octets of the value (from offset 0) are written at o. -/
theorem hostRead_self {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount) (sid : Nat)
    (d : Accounts) (x : X) (kO kZ o z : Nat) (key : List UInt8)
    (h7 : reg ω 7 = 2 ^ 64 - 1) (h8 : reg ω 8 = kO) (h9 : reg ω 9 = kZ) (h10 : reg ω 10 = o)
    (h11 : reg ω 11 = 0) (h12 : reg ω 12 = z)
    (hg : Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ + memGas Constants.CgasRvallinear z ≤ gas)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (hw : μ.rangeWritable o (min z ((self.storage.get? key).map List.length |>.getD 0)) = true) :
    hostRead gas ω μ self sid d x =
      match self.storage.get? key with
      | none => ⟨.cont, (gas : Int) - (Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ +
          memGas Constants.CgasRvallinear z), setR7 ω Result.NONE, μ, x⟩
      | some v => ⟨.cont, (gas : Int) - (Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ +
          memGas Constants.CgasRvallinear z), setR7 ω v.length, μ.writeN o (v.take z), x⟩ := by
  unfold hostRead charged
  simp only [h7, h8, h9, h10, h11, h12, show ¬ gas < Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ +
    memGas Constants.CgasRvallinear z by omega, ite_false, ite_true, hk, Bool.not_true, hkey]
  unfold writeValue
  have e : self.storage.get? key = self.storage[key]? := rfl
  rw [e] at hw ⊢
  cases hv : self.storage[key]? with
  | none => simp_all
  | some v =>
    simp_all
    congr 1
    rcases Nat.le_total z v.length with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

/-- **`read`**: the value stored under `key` in this service's storage (the context kept), for a
    key and a value that fit the operation's memory. -/
theorem step_read (env : AccEnv) (key : Bytes) (c : AccCtx) (hk : argBase + key.length ≤ outBase)
    (hv : ∀ v, c.1.self.storage.get? key = some v → v.length < 2 ^ 31) :
    step env (.read key) c = some (c.1.self.storage.get? key, c) := by
  sorry

end Services.Bootstrap.ASem
