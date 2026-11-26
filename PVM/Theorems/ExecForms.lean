import PVM.Machine
import PVM.Theorems.GasFuel
import PVM.Logic.Words

/-!
# Equal forms and unreachable defaults in Ψ₁ and 𝔛 (GP v0.8.1 §A.5, §A.9)

* `Sim.readyToStart` and `Sim.startStep` index the reorder buffer with proved-in-bounds indices;
  they agree with the earlier forms that read `rob[k]!` (`Sim.readyToStart_val`,
  `Sim.startStep_eq_getElem!`).
* The sign-extending loads: §A.5.6 writes ω'_A = 𝒳_n(…) (`load_i8`, …) and §A.5.10 writes
  ω'_A = 𝒵⁻¹_8(𝒵_n(…)) (`load_ind_i8`, …). The model keeps each as the paper writes it; the two
  forms agree on every loaded value (`Exec.u64_signed_eq_sext`, `Program.exec_loadIndI`,
  `Program.exec_loadI`).
* `twoRegImmAlu` is `none` exactly for the loads and stores, which `Program.exec` handles before
  it, so `exec`'s `.getD 0` never applies (`Exec.twoRegImmAlu_eq_none_iff`).
* Ψ₁ reads an undecodable octet as `trap`; at every step Ψ takes, the instruction decodes
  (`Program.decode_isSome_of_deblob`, `Program.step_decode`).
-/

namespace PVM

open Num Exec

namespace Sim

theorem depDone_eq_getElem! (x : SimState) (k : Nat) : depDone x k = (x.rob[k]!.cycles == 0) := by
  unfold depDone
  split
  · rename_i h; rw [getElem!_pos x.rob k h]
  · rename_i h; rw [getElem!_neg x.rob k h]; rfl

theorem zipIdx_eq_finRange (l : List RobEntry) :
    l.zipIdx = (List.finRange l.length).map fun k => (l[k], k.val) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx, List.getElem_finRange]

/-- 𝔖 with proved-in-bounds indices agrees with the form that reads `rob[k]!`. -/
theorem readyToStart_val (x : SimState) :
    (readyToStart x).map Fin.val =
      (x.rob.zipIdx.find? fun (e, _) =>
        e.state == .wait && e.units.le x.units && e.deps.all fun k => x.rob[k]!.cycles == 0).map
        (·.2) := by
  rw [zipIdx_eq_finRange, List.find?_map, Option.map_map]
  unfold readyToStart
  congr 1
  congr 1
  funext k
  rw [show depDone x = fun k => x.rob[k]!.cycles == 0 from funext (depDone_eq_getElem! x)]
  simp only [Function.comp_def, Fin.getElem_fin]

/-- 𝔛'' with a proved-in-bounds index agrees with the form that reads `rob[n]!`. -/
theorem startStep_eq_getElem! (x : SimState) (n : Fin x.rob.length) :
    startStep x n =
      { x with
        startSlots := x.startSlots - 1
        units := x.units - x.rob[n.val]!.units
        rob := x.rob.modify n fun e => { e with state := .exe } } := by
  simp only [startStep, Fin.getElem_fin, getElem!_pos x.rob n.val n.isLt]

end Sim

namespace Exec

/-- 𝒵⁻¹_8(𝒵_n(v)) = 𝒳_n(v) for an n-octet value v (n = 1, 2, 4): the two forms of the
    sign-extending loads (§A.5.6, §A.5.10) agree. -/
theorem u64_signed_eq_sext (n v : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) (hv : v < 2 ^ (8 * n)) :
    u64 (signed n v) = sext n v := by
  refine Eq.symm ?_
  rcases hn with rfl | rfl | rfl <;>
  · simp only [sext, u64, unsigned, signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at *
    rw [Nat.mod_eq_of_lt hv]
    split <;> omega

/-- `twoRegImmAlu` is `none` exactly for the loads and stores of §A.5.10, which `Program.exec`
    handles before reaching it: its `.getD 0` is never used. -/
theorem twoRegImmAlu_eq_none_iff (op : TwoRegImmOp) (a b x : Nat) :
    twoRegImmAlu op a b x = none ↔
      op ∈ [.storeIndU8, .storeIndU16, .storeIndU32, .storeIndU64, .loadIndU8, .loadIndI8,
        .loadIndU16, .loadIndI16, .loadIndU32, .loadIndI32, .loadIndU64] := by
  cases op <;> simp [twoRegImmAlu]

end Exec

namespace Program

theorem readN_lt (μ : Memory) (a n : Nat) : decodeLE (μ.readN a n) < 2 ^ (8 * n) := by
  have := decodeLE_lt (μ.readN a n)
  rw [Memory.length_readN] at this
  rw [Nat.pow_mul]; exact this

/-- `load_ind_i8`, `load_ind_i16`, `load_ind_i32` (§A.5.10, ω'_A = 𝒵⁻¹_8(𝒵_n(…))) in the 𝒳_n
    form of §A.5.6. -/
theorem exec_loadIndI (P : Program) (i : Nat) (a b : RegIdx) (x : UInt64) (ω : Regs) (μ : Memory) :
    (P.exec i (.twoRegImm .loadIndI8 a b x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 1 (decodeLE (μ.readN ((ω.get b).toNat + x.toNat) 1)))) ∧
    (P.exec i (.twoRegImm .loadIndI16 a b x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 2 (decodeLE (μ.readN ((ω.get b).toNat + x.toNat) 2)))) ∧
    (P.exec i (.twoRegImm .loadIndI32 a b x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 4 (decodeLE (μ.readN ((ω.get b).toNat + x.toNat) 4)))) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [exec] <;>
    rw [Exec.u64_signed_eq_sext _ _ (by decide) (readN_lt _ _ _)]

/-- `load_i8`, `load_i16`, `load_i32` (§A.5.6, ω'_A = 𝒳_n(…)), for comparison with
    `exec_loadIndI`. -/
theorem exec_loadI (P : Program) (i : Nat) (a : RegIdx) (x : UInt64) (ω : Regs) (μ : Memory) :
    (P.exec i (.regImm .loadI8 a x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 1 (decodeLE (μ.readN x.toNat 1)))) ∧
    (P.exec i (.regImm .loadI16 a x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 2 (decodeLE (μ.readN x.toNat 2)))) ∧
    (P.exec i (.regImm .loadI32 a x) ω μ).regs =
      ω.set a (UInt64.ofNat (sext 4 (decodeLE (μ.readN x.toNat 4)))) := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- At every step Ψ takes (deblob succeeds, so 𝔳_inst holds at ı), the instruction decodes. -/
theorem decode_isSome_of_deblob {p : ByteArray} {i : Nat} {P : Program}
    (h : deblob p i = some P) : (P.decode i).isSome := by
  unfold deblob at h
  cases hp : Blob.parse? p with
  | none => simp [hp] at h
  | some Q =>
    simp only [hp, bind, Option.bind] at h
    split at h
    · rename_i hv
      cases h
      simp only [Bool.and_eq_true] at hv
      exact decode_isSome (vInst_isValidOpcode hv.2)
    · cases h

/-- Ψ₁'s fallback `trap` is never used at a step Ψ takes: the instruction it executes is the
    decoded one. -/
theorem step_decode {p : ByteArray} {i : Nat} {P : Program} (h : deblob p i = some P) :
    ∃ ins, P.decode i = some ins ∧ (P.decode i).getD (.noArgs .trap) = ins := by
  obtain ⟨ins, hd⟩ := Option.isSome_iff_exists.1 (decode_isSome_of_deblob h)
  exact ⟨ins, hd, by rw [hd]; rfl⟩

end Program

end PVM
