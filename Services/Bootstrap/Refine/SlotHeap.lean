import Services.Bootstrap.Refine.SlotT
import Services.Bootstrap.Refine.ElemsSmallC

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

theorem flatten_len32 (ks : List (List UInt8)) (h : ∀ k ∈ ks, k.length = 32) : ks.flatten.length = 32 * ks.length := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h k List.mem_cons_self, ih (fun k' hk => h k' (List.mem_cons_of_mem _ hk))]; omega

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

end Services.Bootstrap.Refine.SlotHeap
