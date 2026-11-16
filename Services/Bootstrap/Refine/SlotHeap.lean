import Services.Bootstrap.Refine.SlotT
import Services.Bootstrap.Refine.ElemsSmallC
import Services.Bootstrap.Encode.ArmsHVecDesignate
import Services.Bootstrap.Encode.ArmsHVecGas
import Services.Bootstrap.Encode.ArmsHVecBless
import Services.Bootstrap.Encode.ArmsHVecAssign

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

theorem buf_ofO {bs : List UInt8} {o q a m : Nat} {v : List UInt8} {μ : Memory}
    (h16 : (bs.drop o).take 8 = Num.encodeLE 8 q) (hb16 : (bs.drop o).take 8 = Num.encodeLE 8 a)
    (ha : a < 18446744073709551616) (hq : μ.readN q m = v) : μ.readN a m = v := by
  have := congrArg Num.decodeLE (h16.symm.trans hb16)
  simp only [Num.decodeLE_encodeLE] at this
  rw [show a = q % 18446744073709551616 by omega, readN_mod64]; exact hq

/-- **`Provide(s, Inline(d))`'s decoded slot is good**: 1 ≤ n = |d| < 2^32 octets, the slot `ProvideInlineRep` with its
    buffer (word 24) a chunk of cs holding them. -/
theorem slotOK_provideInline {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (sv : Nat) (d : List UInt8) (hw : (Spec.Instr.provide sv (.inline d)).WF C)
    (hn1 : 1 ≤ d.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.LookupProvideElem.ProvideInlineRep (Codec.fixed 4 sv) d.length d bs μ ∧ OwnsBuf cs bs 24 d.length) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.provide sv (.inline d)).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  obtain ⟨hs4, hnb⟩ := hw
  have hnb : d.length < 4294967296 := hnb
  obtain ⟨⟨h0, h8, h48, q, h16, h24, h32, hq⟩, co, hco, hcou, hb24, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hq' := buf_ofO h24 hb24 (by omega) hq
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) d.length q m →
      μ'.readN q m = μ.readN q m) → EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) d.length (co.addr + 32) d bs μ →
      EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) d.length (co.addr + 32) d bs μ' :=
    fun bs μ μ' hk ⟨e0, e1, e2, e8, e16, e24, e⟩ => ⟨e0, e1, e2, e8, e16, e24, src_keep hk e⟩
  have hrep : EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) d.length (co.addr + 32) d (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact h48, by rw [hel]; exact h16,
      by rw [hel]; exact hb24, by rw [hel]; exact h32, hq'⟩
  have henc : (Spec.Instr.provide sv (.inline d)).encode =
      17 :: (Codec.fixed 4 sv ++ 1 :: (Blob.encodeNat d.length ++ d)) := by
    simp [Spec.Instr.encode, Spec.bytes, Codec.nat]
  have r := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := r 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) d.length (co.addr + 32) d,
    EncProvide.ProvideInlineRepAt (Codec.fixed 4 sv) d.length (co.addr + 32) d, SrcAtP (co.addr + 32) d.length,
    EncProvide.provide_inlineH env K pb hK1 hK (Codec.fixed 4 sv) d.length (co.addr + 32) d
      (by simp [Codec.fixed]) rfl hnb (by omega), hrep, hrep,
    fun bs μ h => ⟨.provide sv (.inline d), ⟨hs4, hnb⟩,
      (EncProvide.provideInlineRep_iff _ d.length d bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inr (Or.inl ⟨1, d.length, by omega, by omega, by rw [r0]; exact h0,
      by rw [r 8 1 (by omega)]; exact h8, by rw [r 16 8 (by omega)]; exact h16,
      by rw [r 24 8 (by omega)]; exact hb24, ?_⟩))
    simp only [true_iff]; omega

theorem readN_mod64o (μ : Memory) (q o m : Nat) :
    μ.readN (q % 18446744073709551616 + o) m = μ.readN (q + o) m := by
  unfold Memory.readN Memory.read
  congr 1; funext k
  rw [show (q % 18446744073709551616 + o + k) % two32 = (q + o + k) % two32 by unfold two32; omega]

/-- Equal reads of the heap octets (q, m) give equal reads of any stretch inside them. -/
theorem sub_keep {q m o l : Nat} {μ μ' : Memory} (hk : ∀ q' m', SrcAtP q m q' m' → μ'.readN q' m' = μ.readN q' m')
    (hol : o + l ≤ m) : μ'.readN (q + o) l = μ.readN (q + o) l := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · subst h0; rfl
  · rw [Decode.Loop.readN_sub μ' q m o l _ rfl hol, Decode.Loop.readN_sub μ q m o l _ rfl hol,
      hk q m ⟨by omega, rfl, rfl⟩]

/-- **`Bless(m, a, v, r, z)`'s decoded slot is good**: 1 ≤ n = |z| < 2^32 pairs, the slot `BlessRep` with its buffer
    (word 16) a chunk of cs holding the 16 n octets. -/
theorem slotOK_bless {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (m a v r : Nat) (z : List (Nat × Nat)) (hw : (Spec.Instr.bless m a v r z).WF C)
    (hn1 : 1 ≤ z.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.Bless.BlessRep (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v) (Codec.fixed 4 r) z.length
        (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g)).flatten bs μ ∧ OwnsBuf cs bs 16 (16 * z.length)) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.bless m a v r z).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  have hw0 := hw
  obtain ⟨hm4, ha4, hv4, hr4, hnb, hz⟩ := hw
  have hnb : z.length < 4294967296 := hnb
  generalize hit : (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g)).flatten = items at hR
  have hil : items.length = 12 * z.length := by
    rw [← hit]
    have := flatten_len 12 (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g))
      (fun k hk => by
        obtain ⟨⟨s, g⟩, -, rfl⟩ := List.mem_map.mp hk
        simp [Codec.fixed])
    simpa using this
  obtain ⟨⟨h0, hm, ha, hd, hr, q, h8, h16, h24, hq⟩, co, hco, hcou, hb16, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hqa : co.addr + 32 = q % 18446744073709551616 := by
    have := congrArg Num.decodeLE (h16.symm.trans hb16)
    simp only [Num.decodeLE_encodeLE] at this; omega
  have hq' : ∀ j, j < z.length → μ.readN (co.addr + 32 + 16 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ.readN (co.addr + 32 + 16 * j + 8) 8 = (items.drop (12 * j + 4)).take 8 := fun j hj => by
    rw [hqa, readN_mod64o, Nat.add_assoc, readN_mod64o, ← Nat.add_assoc]; exact hq j hj
  let R := Encode.Enc.BlessRepAt (co.addr + 32) (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v)
    (Codec.fixed 4 r) z.length items
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) (16 * z.length) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' hk ⟨e0, e1, e2, e3, e4, e8, e16, e24, e⟩ => ⟨e0, e1, e2, e3, e4, e8, e16, e24, fun j hj =>
      ⟨by rw [sub_keep hk (by omega)]; exact (e j hj).1,
       by rw [Nat.add_assoc, sub_keep hk (by omega), ← Nat.add_assoc]; exact (e j hj).2⟩⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact hm, by rw [hel]; exact ha, by rw [hel]; exact hd, by rw [hel]; exact hr,
      by rw [hel]; exact h8, by rw [hel]; exact hb16, by rw [hel]; exact h24, hq'⟩
  have henc : (Spec.Instr.bless m a v r z).encode = 11 :: (Codec.fixed 4 m ++ Codec.fixed 4 a ++ Codec.fixed 4 v ++
      Codec.fixed 4 r ++ Blob.encodeNat z.length ++ items) := by
    rw [← hit]; simp [Spec.Instr.encode, Spec.vec, Codec.nat]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP (co.addr + 32) (16 * z.length),
    blessH_232 env K pb hK1 hK (co.addr + 32) _ _ _ _ z.length items (by simp [Codec.fixed]) (by simp [Codec.fixed])
      (by simp [Codec.fixed]) (by simp [Codec.fixed]) hil hnb (by omega), hrep, hrep,
    fun bs μ h => ⟨.bless m a v r z, hw0, by
      show Decode.Bless.BlessRep _ _ _ _ _ _ bs μ
      rw [hit]; exact (Encode.Enc.blessRep_iff _ _ _ _ z.length items bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inl ⟨11, z.length, by omega, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
      by rw [rd 16 8 (by omega)]; exact hb16, ?_⟩)
    simp only [true_iff]; omega

/-- **`Assign(c, q, a)`'s decoded slot is good**: 1 ≤ n = |q| hashes, the slot `AssignRep` with its buffer (word 16) a
    chunk of cs holding the 32 n octets. -/
theorem slotOK_assign {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (C : Spec.Consts) (c : Nat) (qs : List (List UInt8)) (a : Nat) (hw : (Spec.Instr.assign c qs a).WF C)
    (hn1 : 1 ≤ qs.length) (cs : List Chunk) (bs : List UInt8) (μr : Memory)
    (hR : ∀ μ : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ.read a = μr.read a) →
      Decode.Assign.AssignRep qs.length (Codec.fixed 2 c) qs.flatten (Codec.fixed 4 a) bs μ ∧
        OwnsBuf cs bs 16 (32 * qs.length)) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.assign c qs a).encode bs (· ∈ cs) μr := by
  intro μ s el hel ho
  have hw0 := hw
  obtain ⟨hc2, -, hqs, ha4⟩ := hw
  have hfl := flatten_len 32 qs hqs
  obtain ⟨⟨h0, q, h8, h16, h24, h32, h36, hq⟩, co, hco, hcou, hb16, hcoS, hcoT⟩ :=
    hR μ (fun c hc a ha => (ho c hc).2.2 a ha)
  have hqa : co.addr + 32 = q % 18446744073709551616 := by
    have := congrArg Num.decodeLE (h16.symm.trans hb16)
    simp only [Num.decodeLE_encodeLE] at this; omega
  have hq' : ∀ k, k < qs.length → μ.readN (co.addr + 32 + 32 * k) 32 = (qs.flatten.drop (32 * k)).take 32 :=
    fun k hk => by rw [hqa, readN_mod64o]; exact hq k hk
  let R := Encode.Enc.AssignRepAt (co.addr + 32) qs.length (Codec.fixed 2 c) qs.flatten (Codec.fixed 4 a)
  have hloc : ∀ (bs : List UInt8) (μ μ' : Memory), (∀ q m, SrcAtP (co.addr + 32) (32 * qs.length) q m →
      μ'.readN q m = μ.readN q m) → R bs μ → R bs μ' :=
    fun bs μ μ' hk ⟨e0, e8, e16, e24, e32, e36, e⟩ => ⟨e0, e8, e16, e24, e32, e36, fun k hk' =>
      by rw [sub_keep hk (by omega)]; exact e k hk'⟩
  have hrep : R (μ.readN el 232) μ :=
    ⟨by rw [hel]; exact h0, by rw [hel]; exact h8, by rw [hel]; exact hb16, by rw [hel]; exact h24,
      by rw [hel]; exact h32, by rw [hel]; exact h36, hq'⟩
  have henc : (Spec.Instr.assign c qs a).encode = 12 :: (Codec.fixed 2 c ++ qs.flatten ++ Codec.fixed 4 a) := by
    simp [Spec.Instr.encode]
  have rd := fun o l (hol : o + l ≤ 232) => Decode.Loop.readN_sub μ el 232 o l _ hel hol
  have r0 := rd 0 8 (by omega)
  simp only [Nat.add_zero, List.drop_zero] at r0
  rw [henc]
  refine ⟨R, R, SrcAtP (co.addr + 32) (32 * qs.length),
    assignH_232 env K pb hK1 hK (co.addr + 32) qs.length _ _ _ (by simp [Codec.fixed]) hfl (by simp [Codec.fixed])
      (by omega), hrep, hrep,
    fun bs μ h => ⟨.assign c qs a, hw0, (Encode.Enc.assignRep_iff qs.length _ qs.flatten _ bs μ).mpr ⟨_, h⟩⟩,
    hloc, hloc, ?_, Or.inr (Or.inr ⟨true, co.addr + 32, co, ?_, by omega, fun _ => ⟨(ho co hco).1, hcou, rfl, hco⟩⟩)⟩
  · rintro q m ⟨-, rfl, rfl⟩
    exact ⟨co, hco, by omega, by omega⟩
  · refine Or.inr (Or.inl ⟨12, qs.length, by omega, by omega, by rw [r0]; exact h0, by rw [rd 8 8 (by omega)]; exact h8,
      by rw [rd 16 8 (by omega)]; exact hb16, ?_⟩)
    simp only [true_iff]; omega

end Services.Bootstrap.Refine.SlotHeap
