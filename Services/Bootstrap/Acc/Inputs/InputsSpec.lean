import Services.Bootstrap.Acc.Inputs.LoopInd
import Services.Bootstrap.Acc.Inputs.FetchStep
import PVM.Theorems.InitMem

/-!
# The accumulation inputs as loop items

The model's accumulation inputs (GP v0.8.0 §12: an operand tuple 𝕌 or a deferred transfer 𝕏) as the
(encoding, slot) pairs the item loop takes (`ItemOk`): `itemOf i` pairs i's encoding (GP Appendix C,
`AccumulateInput.encode`) with what its 184-octet slot holds. Within the temporary bounds (a work
output and an auth trace of at most 16384 octets, fewer than 128 inputs) each is an `ItemOk` item, and
ℰ(↕**i**) is the one-octet count followed by the items' encodings.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

/-- An `ItemOk` item within a larger step bound is one within any larger bound. -/
theorem ItemOk.mono {X : Type} {env : HeapHost X} {cap pb : Nat} {p : ByteArray} {P : Program} {N N' : Nat}
    {enc : List UInt8} {Rep : List UInt8 → Memory → Prop} (h : ItemOk env cap pb p P N enc Rep) (hN : N ≤ N') :
    ItemOk env cap pb p P N' enc Rep := by
  intro x ω μ hb s sp rd ip rlen S0 S1 H h0 h1 h7 h8 hsp hsp8 hSTk hrdsp hrdS hR0 hR8 hrl hrl32 henc hsrc
  rcases h x ω μ hb s sp rd ip rlen S0 S1 H h0 h1 h7 h8 hsp hsp8 hSTk hrdsp hrdS hR0 hR8 hrl hrl32 henc hsrc with
    ⟨s', ω', μ', r, rest⟩ | ⟨ω', μ', r⟩
  · exact Or.inl ⟨s', ω', μ', r.mono hN, rest⟩
  · exact Or.inr ⟨ω', μ', r.mono hN⟩

/-- A work error's code in O (GP Appendix C): ∞ 1, ☇ 2, ⊚ 3, ⊖ 4, BAD 5, BIG 6. -/
def errCode : WorkError → Nat
  | .outOfGas => 1
  | .panic => 2
  | .badExports => 3
  | .oversize => 4
  | .bad => 5
  | .big => 6

/-- The four hashes p, e, a, y of an operand tuple, in order. -/
def opHashes (o : OperandTuple) : List UInt8 :=
  o.packageHash.toList ++ o.segmentRoot.toList ++ o.authorizer.toList ++ o.payloadHash.toList

/-- **An accumulation input as a loop item**: its encoding and what its slot holds. -/
def itemOf : AccumulateInput → List UInt8 × (List UInt8 → Memory → Prop)
  | .operand o =>
    match o.result with
    | .ok b => (encOpOk (opHashes o) o.gasLimit b.toList o.authTrace.toList,
        RepOpOk (opHashes o) o.gasLimit b.toList o.authTrace.toList)
    | .err e => (encOpErr (opHashes o) o.gasLimit (errCode e) o.authTrace.toList,
        RepOpErr (opHashes o) o.gasLimit (errCode e) o.authTrace.toList)
  | .transfer x => (encTr x.source x.dest x.amount x.gas x.memo.toList,
      RepTr x.source x.dest x.amount x.gas x.memo.toList)

/-- ℰ(n) for n < 128 is the single octet n (GP (C)). -/
theorem encodeNat_small (n : Nat) (hn : n < 128) : Blob.encodeNat n = [UInt8.ofNat n] := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · rfl
  · rw [encodeNat_of_lt n 0 (by decide) h0 (by simp; omega) (by simpa using hn)]
    simp [Num.encodeLE]

/-- **The item's encoding is the model's** ℰ (GP Appendix C, `AccumulateInput.encode`). -/
theorem itemOf_enc (i : AccumulateInput) : (itemOf i).1 = i.encode := by
  cases i with
  | operand o =>
    cases hr : o.result with
    | ok b =>
      simp only [itemOf, hr, AccumulateInput.encode, OperandTuple.encode, WorkResult.encode, encOpOk,
        opHashes, Codec.nat, Codec.blob, Codec.var, ByteArray.length_toList', List.append_assoc,
        encodeNat_small 0 (by decide), List.cons_append, List.singleton_append, List.nil_append]
      rfl
    | err e =>
      cases e <;>
      simp only [itemOf, hr, AccumulateInput.encode, OperandTuple.encode, WorkResult.encode, encOpErr,
        opHashes, Codec.nat, Codec.blob, Codec.var, errCode, List.append_assoc, ByteArray.length_toList',
        encodeNat_small 0 (by decide), List.cons_append, List.singleton_append, List.nil_append] <;> rfl
  | transfer x =>
    simp only [itemOf, AccumulateInput.encode, DeferredTransfer.encode, encTr, Codec.nat, Codec.fixed,
      Codec.blob, List.append_assoc, encodeNat_small 1 (by decide), List.cons_append, List.singleton_append,
      List.nil_append]
    rfl

/-- **The sizes the item decode covers**: 32-octet hashes, a gas below 2⁶⁴, a work output and an auth
    trace of at most 16384 octets (the temporary bound); a transfer's ids below 2³², amount and gas
    below 2⁶⁴ and a 128-octet memo (GP's 𝖶_T). -/
def InputSized : AccumulateInput → Prop
  | .operand o => o.packageHash.size = 32 ∧ o.segmentRoot.size = 32 ∧ o.authorizer.size = 32 ∧
      o.payloadHash.size = 32 ∧ o.gasLimit < 18446744073709551616 ∧ o.authTrace.size ≤ 16384 ∧
      (∀ b, o.result = .ok b → b.size ≤ 16384)
  | .transfer x => x.source < 4294967296 ∧ x.dest < 4294967296 ∧ x.amount < 18446744073709551616 ∧
      x.gas < 18446744073709551616 ∧ x.memo.size = 128

/-- The loop's step bound per item. -/
def itemSteps : Nat := 7 * 16384 + 7 * 16384 + 7101

/-- **Each sized accumulation input is an `ItemOk` item** (`itemOk_tr`, `itemOk_opok`, `itemOk_operr`). -/
theorem itemOf_ok {X : Type} (env : HeapHost X) (cap pb : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (i : AccumulateInput) (hi : InputSized i) :
    ItemOk env cap pb p P itemSteps (itemOf i).1 (itemOf i).2 := by
  cases i with
  | operand o =>
    obtain ⟨h1, h2, h3, h4, hg, ht, ho⟩ := hi
    have hh : (opHashes o).length = 128 := by
      simp only [opHashes, List.length_append, ByteArray.length_toList', h1, h2, h3, h4]
    cases hr : o.result with
    | ok b =>
      simp only [itemOf, hr]
      exact itemOk_opok env cap pb hcap1 hcap _ _ _ _ hh hg (by rw [ByteArray.length_toList']; exact ho b hr)
        (by rw [ByteArray.length_toList']; exact ht)
    | err e =>
      simp only [itemOf, hr]
      exact (itemOk_operr env cap pb hcap1 hcap (opHashes o) o.gasLimit (errCode e) o.authTrace.toList hh hg
        (by cases e <;> decide) (by rw [ByteArray.length_toList']; exact ht)).mono (by unfold itemSteps; omega)
  | transfer x =>
    obtain ⟨hs, hd, ha, hg, hm⟩ := hi
    exact (itemOk_tr env cap pb _ _ _ _ _ hs hd ha hg (by rw [ByteArray.length_toList']; exact hm)).mono
      (by unfold itemSteps; omega)

/-- **ℰ(↕i) as the loop reads it**: fewer than 128 inputs, the one-octet count (GP (C)) and then the
    items' encodings. -/
theorem inputsEnc_items (env : AccEnv) (hn : env.inputs.length < 128) :
    inputsEnc env = [UInt8.ofNat env.inputs.length] ++ encs (env.inputs.map itemOf) := by
  have e1 := encodeNat_small env.inputs.length hn
  have e2 : encs (env.inputs.map itemOf) = (env.inputs.map AccumulateInput.encode).flatten := by
    unfold encs
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun i _ => itemOf_enc i
  rw [inputsEnc, Codec.varSeq, Codec.nat, e1, e2]

end Services.Bootstrap.Acc
