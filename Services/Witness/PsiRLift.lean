import Services.Witness.Lift
import Services.Witness.Prefix

/-!
# Ψ_R of witness from a gas-free run

Ψ_R (GP eq. `refinvocation`) looks up the item's code, builds the arguments
ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ↕y ⌢ ℋ(p) and runs Ψ_M. Given a gas-free run of that code from Y's state to
the halt with output [12, 0], Ψ_R's result is [12, 0] or ∞.
-/

namespace Services.Witness

open PVM JAM Services.Witness.Code Services.Witness.Prefix

theorem psiR_of_run (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage) (r : List UInt8)
    (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem)
    (hw : p.items[i]? = some w) (l : List UInt8)
    (hl : (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot
      w.codeHash.toList) = some l)
    (hsize : l.length ≤ Constants.Cmaxservicecodesize) (code : ByteArray)
    (hcode : splitMetadata l = some code) (jb : JamBlob) (hjb : JamBlob.parse? code = some jb)
    (hlay : layoutOk jb = true) (hcc : checkCode jb.code facts = true)
    (hrun : ∀ (P : Program) [HasCode jb.code P] (env : RefineHost.Env), env.code = code →
      env.fetch.params = params →
      let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
        (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩
      a.size ≤ inputSize ∧
      ∃ ω' μ' x', FreeStepsH jb.code (refineContract env) 0 (initialRegs a) (initialMemory jb a)
        ((∅, []) : RefineCtx) 43609 ω' μ' x' ∧ ω'[0] = UInt64.ofNat 4294901760 ∧
        ω'[7] = UInt64.ofNat 206816 ∧ ω'[8] = UInt64.ofNat 2 ∧ μ'.read 206816 = 12 ∧
        μ'.read 206817 = 0 ∧ μ'.readable 206816 = true ∧ μ'.readable 206817 = true) :
    (psiR params d c i p r imports extrinsics off).result = .ok ⟨#[12, 0]⟩ ∨
      (psiR params d c i p r imports extrinsics off).result = .err .outOfGas := by
  obtain ⟨P, hP⟩ := checkCode_sound hcc
  haveI : HasCode jb.code P := ⟨hP⟩
  simp only [psiR, hw, hl]
  rw [ite_eq_right (by omega)]
  simp only [hcode]
  generalize hE : RefineHost.Env.mk params w.service d p.context.lookupAnchorSlot code off
    (FetchContext.mk params (some p) (some (List.replicate 32 0)) (some r) (some i) (some imports)
      (some extrinsics) none) = env
  have hrun' := hrun P env (by rw [← hE]) (by rw [← hE])
  generalize hA : (⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
    (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩ : ByteArray) = a at hrun' ⊢
  obtain ⟨ha, ω', μ', x', hsteps, h0, h7, h8, hb0, hb1, hr0, hr1⟩ := hrun'
  have hY : standardInit code a = some (jb.code, initialRegs a, initialMemory jb a) := by
    simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hlay
    obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheap⟩, hstack⟩, _⟩, _⟩ := hlay
    have hfit : ¬(5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32) := by
      rw [hro, hrw, hheap, hstack]; decide
    unfold standardInit validJamBlob?
    rw [ite_eq_right (by omega), hjb, Option.bind_some, ite_eq_right hfit]
    rfl
  have hres := psiM_of_run (P := P) code a (UInt64.ofNat w.refineGasLimit) env hY 206816 [12, 0]
    ⟨ω', μ', x', hsteps, h0, h7, by simpa using h8, by decide, by decide,
      by simp only [Memory.readN, List.length_cons, List.length_nil, Nat.reduceAdd,
        show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, Nat.add_zero, hb0, hb1],
      fun j h1 h2 => by
        rcases (show j = 206816 ∨ j = 206817 by simp at h2; omega) with rfl | rfl
        · exact hr0
        · exact hr1⟩
  rcases hres with h | h
  · left; rw [h]
  · right; rw [h]; rfl

end Services.Witness
