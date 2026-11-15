import Services.Bootstrap.Acc.Inputs.LoopInd
import Services.Bootstrap.Acc.Inputs.FetchStep
import PVM.Theorems.InitMem
import Services.Bootstrap.Acc.Inputs.GlueCall
import Services.Bootstrap.Acc.HeapHost

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

/-- **The inputs' decode, 44495 → 44674, for the model's inputs** (GP v0.8.0 §12; at most 89, each
    within `InputSized`): with ℰ(↕**i**) (`inputsEnc env`) at `ptr`, the data of the allocated chunk F
    (the fetched `Vec` at sp + 56 … + 72, its capacity fc ≠ 0), either `Vec { n, q, n }` is stored at the
    output o, slot j of the buffer at q satisfying `itemOf` of input j for any memory agreeing on the final
    state's allocated data, F freed, the context holding for the final state, every other allocated
    chunk and its data kept, the stack above sp + 144 kept off o, and ω₀, ω₅, ω₆ restored at the return;
    or the allocator is exhausted (45975, 45642). -/
theorem g_inputs (aenv : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : AccCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s0 : State) (sp o fc ptr len S0 S1 : Nat) (F : Chunk)
    (hn : aenv.inputs.length ≤ 89) (hsz : ∀ i ∈ aenv.inputs, InputSized i)
    (H : HeapCtxC aenv.code pb S0 S1 μ s0) (h1 : ω[1] = UInt64.ofNat sp)
    (m8 : rdN μ (sp + 8) 8 = o) (m56 : rdN μ (sp + 56) 8 = fc) (m64 : rdN μ (sp + 64) 8 = ptr)
    (m72 : rdN μ (sp + 72) 8 = len) (hfc : 0 < fc ∧ fc ≠ 18446744073709551615)
    (hF : F ∈ chunks s0) (hFu : F.used = true) (hFa : F.addr + 32 = ptr)
    (hFe : ptr + (inputsEnc aenv).length ≤ F.addr + 32 * F.size)
    (hlen : (inputsEnc aenv).length ≤ len ∧ len < 4294967296)
    (henc : μ.readN ptr (inputsEnc aenv).length = inputsEnc aenv)
    (hsp : 2147483960 + 424 + 480 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 864 + 480 ≤ sp)
    (ho : sp + 144 ≤ o ∧ o + 24 ≤ S1) :
    (∃ q st' ω' μ', FreeStepsH p (accGrowK cap aenv) 44495 ω μ x 44674 ω' μ' x
        ((itemSteps + 2100) * aenv.inputs.length + 1900) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 136) 8) ∧ ω'[1] = UInt64.ofNat (sp + 144) ∧
      ω'[5] = UInt64.ofNat (rdN μ (sp + 128) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (sp + 120) 8) ∧
      rdN μ' o 8 = aenv.inputs.length ∧ rdN μ' (o + 8) 8 = q ∧ rdN μ' (o + 16) 8 = aenv.inputs.length ∧
      HeapCtxC aenv.code pb S0 S1 μ' st' ∧
      (∀ c ∈ chunks s0, c.used = true → c ≠ F → c ∈ chunks st' ∧ ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∀ (j : Nat) (i : AccumulateInput), aenv.inputs[j]? = some i →
        ∀ μ'' : Memory, (∀ c ∈ chunks st', c.used = true → ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          (itemOf i).2 (μ''.readN (q + 184 * j) 184) μ'') ∧
      (∀ a, a < 4294967296 → sp + 144 ≤ a → (a < o ∨ o + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ j ω' μ', (j = 45975 ∨ j = 45642) ∧
      FreeStepsH p (accGrowK cap aenv) 44495 ω μ x j ω' μ' x ((itemSteps + 2100) * aenv.inputs.length + 1900)) := by
  have hE := inputsEnc_items aenv (by omega)
  rcases Nat.eq_zero_or_pos aenv.inputs.length with h0 | hpos
  · -- no inputs
    have hnil : aenv.inputs = [] := List.eq_nil_of_length_eq_zero h0
    have hE0 : inputsEnc aenv = [UInt8.ofNat 0] := by rw [hE, hnil]; rfl
    rw [hE0] at hFe hlen henc
    have hr : μ.read ptr = UInt8.ofNat 0 := by simpa [Memory.readN] using henc
    obtain ⟨ω', μ', r, z0, z1, z5, z6, o0, o8, o16, H', kd, fr⟩ :=
      g_call0 (R := accGrowK cap aenv) (p := p) (P := P) aenv.code pb x ω μ s0 sp o fc ptr len S0 S1 F H h1 m8 m56
        m64 m72 hfc hF hFu hFa (by simpa using hFe) ⟨by simpa using hlen.1, hlen.2⟩ hr (by omega) (by omega) ho
    refine Or.inl ⟨8, free s0 ptr, ω', μ', r.mono (by omega), z0, z1, z5, z6, by rw [o0, h0], o8,
      by rw [o16, h0], H', kd, fun j i hj => ?_, fr⟩
    rw [hnil] at hj; simp at hj
  · -- the items
    have hrest : (aenv.inputs.map itemOf).length = aenv.inputs.length := List.length_map _
    rw [hE] at hFe hlen henc
    simp only [List.length_append, List.length_singleton] at hFe hlen henc
    rcases g_call (p := p) (P := P) (hb := hb) (accHeapHost aenv) cap pb itemSteps hcap1 hcap x ω μ s0 sp o fc ptr len S0 S1 F
        (aenv.inputs.map itemOf)
        (fun e he => by
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
          exact itemOf_ok (p := p) (P := P) (accHeapHost aenv) cap pb hcap1 hcap i (hsz i hi))
        ⟨by omega, by omega⟩ H h1 m8 m56 m64 m72 hfc hF hFu hFa (by omega) ⟨by omega, hlen.2⟩
        (by rw [hrest]; exact henc) hsp hSTk ho with
      ⟨q, st', ω', μ', r, z0, z1, z5, z6, o0, o8, o16, H', kd, -, -, reps, fr⟩ | ⟨j, ω', μ', hj, r⟩
    · refine Or.inl ⟨q, st', ω', μ', by simpa [hrest, accHeapHost] using r, z0, z1, z5, z6, by rw [o0, hrest],
        o8, by rw [o16, hrest], H', kd, fun j i hj μ'' hag => reps j (itemOf i) (by simp [hj]) μ'' hag, fr⟩
    · exact Or.inr ⟨j, ω', μ', hj, by simpa [hrest, accHeapHost] using r⟩

end Services.Bootstrap.Acc
