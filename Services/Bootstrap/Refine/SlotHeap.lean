import Services.Bootstrap.Refine.SlotT
import Services.Bootstrap.Refine.ElemsSmallC
import Services.Bootstrap.Encode.ArmsHVecDesignate
import Services.Bootstrap.Encode.ArmsHVecGas

/-!
# T1c's output slots of the heap kinds passed through

For each variable-width kind refine passes through, its decoded slot (the decode side's representation and the
buffer's chunk, `ElemsBigC.OwnsBuf`) is `SlotT.SlotOK` for the kind's encoding, owning the decode's chunks: the encoder
arm `…H_232` with its `…RepAt q` (q the slot's buffer word) and heap octets `SrcAtP q m`, the `Debug` predicate, and the
drop (`DropVecW.BufEl` / `DropVecH.VVAt`). The template is `RandomStorageAccumulate(Ok)` (`slotOK_rsaOk`).
GP v0.8.0 Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotHeap

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW
  Services.Bootstrap.Refine.ElemsBigC

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem readN_mod64 (μ : Memory) (q m : Nat) : μ.readN (q % 18446744073709551616) m = μ.readN q m := by
  unfold Memory.readN Memory.read
  congr 1; funext k
  rw [show (q % 18446744073709551616 + k) % two32 = (q + k) % two32 by unfold two32; omega]

theorem flatten_len (w : Nat) (ks : List (List UInt8)) (h : ∀ k ∈ ks, k.length = w) :
    ks.flatten.length = w * ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h k List.mem_cons_self, ih (fun k' hk => h k' (List.mem_cons_of_mem _ hk))]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem flatten_len32 (ks : List (List UInt8)) (h : ∀ k ∈ ks, k.length = 32) : ks.flatten.length = 32 * ks.length :=
  flatten_len 32 ks h

/-- The heap octets (q, m) of a `…RepAt q` slot: equal reads of them keep `μ.readN q m = v`. -/
theorem src_keep {q m : Nat} {v : List UInt8} {μ μ' : Memory} (hk : ∀ q' m', SrcAtP q m q' m' → μ'.readN q' m' = μ.readN q' m')
    (h : μ.readN q m = v) : μ'.readN q m = v := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; simpa [Memory.readN] using h
  · rw [hk q m ⟨h0, rfl, rfl⟩]; exact h

/-- **`RandomStorageAccumulate(Ok(ks))`'s decoded slot is good**: 1 ≤ n = |ks| < 2^32 hashes, the slot
    `RandomStorageOkRep` with its buffer (word 16) a chunk of cs holding the 32 n octets, in every memory keeping cs as
    μr. -/
theorem slotOK_rsaOk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (ks : List (List UInt8)) (hw : (Spec.Instr.randomStorageAccumulate (some ks)).WF C)
    (hn1 : 1 ≤ ks.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.RandomStorage.RandomStorageOkRep ks.length ks.flatten bs μ ∧ OwnsBuf cs bs 16 (32 * ks.length)) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.randomStorageAccumulate (some ks)).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  have hw' : Spec.short ks ∧ ∀ k ∈ ks, k.length = 32 := hw ks rfl
  have hnb : ks.length < 4294967296 := hw'.1
  have hfl := flatten_len32 ks hw'.2
  obtain ⟨⟨h0, q, h8, h16, h24, hq⟩, co, hco, hcou, hb16, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hqa : q % 18446744073709551616 = co.addr + 32 := by
    have := congrArg Num.decodeLE (h16.symm.trans hb16)
    simp only [Num.decodeLE_encodeLE] at this; omega
  have hq' : μ.readN (co.addr + 32) (32 * ks.length) = ks.flatten := by rw [← hqa, readN_mod64]; exact hq
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) (32 * ks.length) q m →
      μ'.readN q m = μ.readN q m) → EncRSA.RSAOkRepAt (co.addr + 32) ks.length ks.flatten bs μ →
      EncRSA.RSAOkRepAt (co.addr + 32) ks.length ks.flatten bs μ' :=
    fun bs μ μ' hk ⟨e0, e8, e16, e24, e⟩ => ⟨e0, e8, e16, e24, src_keep hk e⟩
  have hrep : EncRSA.RSAOkRepAt (co.addr + 32) ks.length ks.flatten (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact hb16, by rw [hel]; exact h24, hq'⟩
  have henc : (Spec.Instr.randomStorageAccumulate (some ks)).encode =
      22 :: 0 :: (Blob.encodeNat ks.length ++ ks.flatten) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨EncRSA.RSAOkRepAt (co.addr + 32) ks.length ks.flatten, EncRSA.RSAOkRepAt (co.addr + 32) ks.length ks.flatten,
    SrcAtP (co.addr + 32) (32 * ks.length),
    EncRSA.rsa_okH_232 env K pb hK1 hK (co.addr + 32) ks.length ks.flatten hfl hnb (by omega), hrep, hrep,
    fun bs μ h => ⟨.randomStorageAccumulate (some ks), hw, (EncRSA.rsaOkRep_iff ks.length ks.flatten bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inr (Or.inr ⟨ks.length, by omega, by rw [r0]; exact h0, by rw [r 8 8 (by omega)]; exact h8,
      by rw [r 16 8 (by omega)]; exact hb16, ?_⟩))
    simp only [true_iff]; omega

/-- The buffer word: a decoded slot's q (any natural, as the decode side states it) and the chunk's data address
    agree modulo 2^64, so the reads at q are the reads at the chunk. -/
theorem buf_of {bs : List UInt8} {q a m : Nat} {v : List UInt8} {μ : Memory}
    (h16 : (bs.drop 16).take 8 = Num.encodeLE 8 q) (hb16 : (bs.drop 16).take 8 = Num.encodeLE 8 a)
    (ha : a < 18446744073709551616) (hq : μ.readN q m = v) : μ.readN a m = v := by
  have := congrArg Num.decodeLE (h16.symm.trans hb16)
  simp only [Num.decodeLE_encodeLE] at this
  rw [show a = q % 18446744073709551616 by omega, readN_mod64]; exact hq

/-- **`Designate(ks)`'s decoded slot is good**: 1 ≤ n = |ks| keysets, the slot `DesignateRep` with its buffer (word 16)
    a chunk of cs holding the 336 n octets. -/
theorem slotOK_designate {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (ks : List (List UInt8)) (hw : (Spec.Instr.designate ks).WF C)
    (hn1 : 1 ≤ ks.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.Designate.DesignateRep ks.length ks.flatten bs μ ∧ OwnsBuf cs bs 16 (336 * ks.length)) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.designate ks).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  obtain ⟨hmax, hnb, hks⟩ := hw
  have hnb : ks.length < 4294967296 := hnb
  have hfl := flatten_len 336 ks hks
  obtain ⟨⟨h0, q, h8, h16, h24, hq⟩, co, hco, hcou, hb16, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hq' := buf_of h16 hb16 (by omega) hq
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) (336 * ks.length) q m →
      μ'.readN q m = μ.readN q m) → Encode.Enc.DesignateRepAt (co.addr + 32) ks.length ks.flatten bs μ →
      Encode.Enc.DesignateRepAt (co.addr + 32) ks.length ks.flatten bs μ' :=
    fun bs μ μ' hk ⟨e0, e8, e16, e24, e⟩ => ⟨e0, e8, e16, e24, src_keep hk e⟩
  have hrep : Encode.Enc.DesignateRepAt (co.addr + 32) ks.length ks.flatten (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact hb16, by rw [hel]; exact h24, hq'⟩
  have henc : (Spec.Instr.designate ks).encode = 13 :: (Blob.encodeNat ks.length ++ ks.flatten) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨Encode.Enc.DesignateRepAt (co.addr + 32) ks.length ks.flatten,
    Encode.Enc.DesignateRepAt (co.addr + 32) ks.length ks.flatten, SrcAtP (co.addr + 32) (336 * ks.length),
    designateH_232 env K pb hK1 hK (co.addr + 32) ks.length ks.flatten hfl hnb (by omega), hrep, hrep,
    fun bs μ h => ⟨.designate ks, ⟨hmax, hnb, hks⟩, (Encode.Enc.designateRep_iff ks.length ks.flatten bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inl ⟨13, ks.length, by omega, by omega, by rw [r0]; exact h0, by rw [r 8 8 (by omega)]; exact h8,
      by rw [r 16 8 (by omega)]; exact hb16, ?_⟩)
    simp only [true_iff]; omega

/-- **`AssignForGasCost(c, q, a)`'s decoded slot is good**: 1 ≤ n = |q| hashes, the slot `AssignGasRep` with its buffer
    (word 16) a chunk of cs holding the 32 n octets. -/
theorem slotOK_assignGas {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (c : Nat) (qs : List (List UInt8)) (a : Nat) (hw : (Spec.Instr.assignForGasCost c qs a).WF C)
    (hn1 : 1 ≤ qs.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.AssignGas.AssignGasRep (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a) bs μ ∧
        OwnsBuf cs bs 16 (32 * qs.length)) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.assignForGasCost c qs a).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  obtain ⟨hc2, hnb, hqs, ha4⟩ := hw
  have hnb : qs.length < 4294967296 := hnb
  have hfl := flatten_len 32 qs hqs
  obtain ⟨⟨h0, hg, hc, q, h8, h16, h24, hq⟩, co, hco, hcou, hb16, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hq' := buf_of h16 hb16 (by omega) hq
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) (32 * qs.length) q m →
      μ'.readN q m = μ.readN q m) →
      Encode.Enc.AssignGasRepAt (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a) bs μ →
      Encode.Enc.AssignGasRepAt (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a) bs μ' :=
    fun bs μ μ' hk ⟨e0, e1, e2, e8, e16, e24, e⟩ => ⟨e0, e1, e2, e8, e16, e24, src_keep hk e⟩
  have hrep : Encode.Enc.AssignGasRepAt (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a)
      (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact hg, by rw [hel]; exact hc, by rw [hel]; exact h8,
      by rw [hel]; exact hb16, by rw [hel]; exact h24, hq'⟩
  have henc : (Spec.Instr.assignForGasCost c qs a).encode =
      24 :: (Codec.fixed 2 c ++ Blob.encodeNat qs.length ++ qs.flatten ++ Codec.fixed 4 a) := by
    simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨Encode.Enc.AssignGasRepAt (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a),
    Encode.Enc.AssignGasRepAt (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a),
    SrcAtP (co.addr + 32) (32 * qs.length),
    assign_gasH_232 env K pb hK1 hK (co.addr + 32) (Codec.fixed 2 c) qs.length qs.flatten (Codec.fixed 4 a)
      (by simp [Codec.fixed]) hfl (by simp [Codec.fixed]) hnb (by omega), hrep, hrep,
    fun bs μ h => ⟨.assignForGasCost c qs a, ⟨hc2, hnb, hqs, ha4⟩,
      (Encode.Enc.assignGasRep_iff _ qs.length qs.flatten _ bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inl ⟨24, qs.length, by omega, by omega, by rw [r0]; exact h0, by rw [r 8 8 (by omega)]; exact h8,
      by rw [r 16 8 (by omega)]; exact hb16, ?_⟩)
    simp only [true_iff]; omega

end Services.Bootstrap.Refine.SlotHeap
