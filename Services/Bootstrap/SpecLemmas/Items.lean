import Services.Bootstrap.SpecLemmas.Codec
import Services.Bootstrap.Acc.Inputs.CompactU64Call
import JAM.Accumulate

/-!
# The accumulate inputs, as `Spec.accumulate` decodes them

`Spec.accumulate` decodes the fetched ℰ(↕**i**) (GP v0.8.0 §12, the accumulation inputs **i**;
Appendix C, their encoding) with `Dec.vec Dec.item`. For well-sized inputs it reads back each input
as the `Spec.Item` it stands for:
- an operand's package hash and its work output (`none` for a work error);
- a transfer's source, amount and memo.

See `decode_items`. `compact_run64` extends `compact_run` to every natural below 2⁶⁴, for the
operand's gas limit.
-/

namespace Services.Bootstrap.Spec

open JAM
open JAM.Codec (nat fixed)

namespace Dec

/-- `compact` inverts GP's ℰ on every natural below 2⁶⁴. -/
theorem compact_run64 (x : Nat) (hx : x < 2 ^ 64) (s : Bytes) :
    compact.run (nat x ++ s) = some (x, s) := by
  rcases Nat.lt_or_ge x (2 ^ 28) with h | h
  · exact compact_run x (by omega) s
  have : x < 34359738368 ∨ (34359738368 ≤ x ∧ x < 4398046511104) ∨
      (4398046511104 ≤ x ∧ x < 562949953421312) ∨ (562949953421312 ≤ x ∧ x < 72057594037927936) ∨
      72057594037927936 ≤ x := by omega
  rcases this with h1 | h1 | h1 | h1 | h1
  · rw [show nat x = _ from Acc.encodeNat_of_lt8 x 4 (by decide) (by omega) (by simp; omega) (by simp; omega)]
    refine compact_aux 4 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
      Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from Acc.encodeNat_of_lt8 x 5 (by decide) (by omega) (by simp; omega) (by simp; omega)]
    refine compact_aux 5 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
      Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from Acc.encodeNat_of_lt8 x 6 (by decide) (by omega) (by simp; omega) (by simp; omega)]
    refine compact_aux 6 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
      Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from Acc.encodeNat_of_lt8 x 7 (by decide) (by omega) (by simp; omega) (by simp; omega)]
    refine compact_aux 7 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv,
      Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from Acc.encodeNat_big x h1]
    simp only [compact, List.cons_append, bind_byte]
    have e : UInt8.toNat 255 = 255 := rfl
    rw [e, ite_pos' rfl, show PVM.Num.encodeLE 8 x = fixed 8 x from rfl, fixedN_run]
    simp [Nat.mod_eq_of_lt hx]

@[simp] theorem bind_compact64 {β : Type} (f : Nat → Dec β) (x : Nat) (hx : x < 2 ^ 64) (s : Bytes) :
    (compact >>= f).run (nat x ++ s) = (f x).run s := bind_of_run (compact_run64 x hx s)

end Dec

/-- **An accumulation input as `Spec.accumulate` sees it**: an operand's package hash and its work
    output (`none` for a work error), or a transfer's source, amount and memo. -/
def specItem : AccumulateInput → Item
  | .operand o => .work o.packageHash.toList
      (match o.result with | .ok b => some b.toList | .err _ => none)
  | .transfer x => .transfer x.source x.amount x.memo.toList

/-- **The sizes ℰ reads back**: 32-octet hashes, a gas limit below 2⁶⁴, an output and a trace shorter
    than 2³² octets; a transfer's ids below 2³², amount and gas below 2⁶⁴, and a 128-octet memo (GP's
    𝖶_T). -/
def InputWF : AccumulateInput → Prop
  | .operand o => o.packageHash.size = 32 ∧ o.segmentRoot.size = 32 ∧ o.authorizer.size = 32 ∧
      o.payloadHash.size = 32 ∧ o.gasLimit < 2 ^ 64 ∧ o.authTrace.size < 2 ^ 32 ∧
      (∀ b, o.result = .ok b → b.size < 2 ^ 32)
  | .transfer x => x.source < 2 ^ 32 ∧ x.dest < 2 ^ 32 ∧ x.amount < 2 ^ 64 ∧ x.gas < 2 ^ 64 ∧
      x.memo.size = 128

theorem length_toList (b : ByteArray) : b.toList.length = b.size := ByteArray.length_toList' b

/-- **`Dec.item` reads back one well-sized input** (GP Appendix C), as `specItem`. -/
theorem item_run (i : AccumulateInput) (hi : InputWF i) (s : Bytes) :
    Dec.item.run (i.encode ++ s) = some (specItem i, s) := by
  cases i with
  | operand o =>
    obtain ⟨h1, h2, h3, h4, hg, ht, ho⟩ := hi
    have hn0 : nat 0 = [0] := rfl
    simp only [AccumulateInput.encode, OperandTuple.encode, Codec.blob, Codec.var, hn0, List.append_assoc,
      List.cons_append, List.nil_append, Dec.item, Dec.bind_byte]
    have e0 : (0 : UInt8).toNat = 0 := rfl
    rw [e0]
    simp only [show (0 : Nat) = 0 from rfl, ite_true]
    rw [Dec.bind_take 32 _ o.packageHash.toList _ (by rw [length_toList, h1])]
    rw [show o.segmentRoot.toList ++ (o.authorizer.toList ++ (o.payloadHash.toList ++ (nat o.gasLimit ++
        (o.result.encode ++ (nat o.authTrace.size ++ (o.authTrace.toList ++ s)))))) =
        (o.segmentRoot.toList ++ o.authorizer.toList ++ o.payloadHash.toList) ++ (nat o.gasLimit ++
        (o.result.encode ++ (nat o.authTrace.size ++ (o.authTrace.toList ++ s)))) by simp]
    rw [Dec.bind_take 96 _ _ _ (by simp [length_toList, h2, h3, h4])]
    rw [Dec.bind_compact64 _ _ hg]
    cases hr : o.result with
    | ok b =>
      have hb := ho b hr
      simp only [WorkResult.encode, Codec.var, List.cons_append, Dec.bind_byte, e0]
      simp only [show (0 : Nat) = 0 from rfl, ite_true, List.append_assoc]
      rw [show nat b.size ++ (b.toList ++ (nat o.authTrace.size ++ (o.authTrace.toList ++ s))) =
          Spec.bytes b.toList ++ (Spec.bytes o.authTrace.toList ++ s) by
        simp [Spec.bytes, length_toList]]
      simp only [map_eq_pure_bind, bind_assoc, pure_bind]
      rw [Dec.bind_bytes _ _ (by unfold short; rw [length_toList]; exact hb),
        Dec.bind_bytes _ _ (by unfold short; rw [length_toList]; exact ht)]
      simp [specItem, hr]
    | err e =>
      cases e <;>
      · simp only [WorkResult.encode, List.cons_append, List.nil_append, Dec.bind_byte, List.append_assoc]
        rw [show nat o.authTrace.size ++ (o.authTrace.toList ++ s) = Spec.bytes o.authTrace.toList ++ s by
          simp [Spec.bytes, length_toList]]
        simp (disch := decide) only [Dec.ite_pos', Dec.ite_neg']
        simp only [map_eq_pure_bind, bind_assoc, pure_bind]
        rw [Dec.bind_bytes _ _ (by unfold short; rw [length_toList]; exact ht)]
        simp [specItem, hr]
  | transfer x =>
    obtain ⟨hs, hd, ha, hg, hm⟩ := hi
    have hn1 : nat 1 = [1] := rfl
    simp only [AccumulateInput.encode, DeferredTransfer.encode, Codec.blob, hn1, List.append_assoc,
      List.cons_append, List.nil_append, Dec.item, Dec.bind_byte]
    have e1 : UInt8.toNat 1 = 1 := rfl
    rw [e1]
    simp only [Dec.bind_fixedN]
    rw [Dec.bind_take 128 _ x.memo.toList _ (by rw [length_toList, hm])]
    simp only [Dec.bind_fixedN]
    simp [specItem, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ha]

/-- **`Spec.accumulate`'s decode of ℰ(↕**i**)** (GP v0.8.0 §12, Appendix C): for fewer than 2³²
    well-sized inputs, `Dec.vec Dec.item` reads back the inputs as `specItem`s. -/
theorem decode_items (inputs : List AccumulateInput) (hn : inputs.length < 2 ^ 32)
    (hwf : ∀ i ∈ inputs, InputWF i) :
    decode (Dec.vec Dec.item) (Codec.varSeq AccumulateInput.encode inputs) = some (inputs.map specItem) := by
  have hc : ∀ (xs : List AccumulateInput), (∀ i ∈ xs, InputWF i) → ∀ s,
      (Dec.count Dec.item xs.length).run ((xs.map AccumulateInput.encode).flatten ++ s) =
        some (xs.map specItem, s) := by
    intro xs
    induction xs with
    | nil => intro _ s; rfl
    | cons x xs ih =>
      intro h s
      simp only [Dec.count, List.map_cons, List.flatten_cons, List.append_assoc, List.length_cons]
      rw [Dec.bind_of_run (item_run x (h x (by simp)) _), Dec.bind_of_run (ih (fun y hy => h y (by simp [hy])) s)]
      rfl
  unfold decode Dec.vec
  rw [Codec.varSeq, show nat inputs.length ++ (inputs.map AccumulateInput.encode).flatten =
    nat inputs.length ++ ((inputs.map AccumulateInput.encode).flatten ++ []) by simp]
  rw [Dec.bind_len _ _ hn, hc inputs hwf []]
  rfl

end Services.Bootstrap.Spec
