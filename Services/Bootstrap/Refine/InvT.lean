import Services.Bootstrap.Refine.PkgAll
import Services.Bootstrap.Refine.SpecRunT

/-!
# T1c's loop invariant

`Inv` is the caller's invariant `LoopT.loop_t` carries from instruction k to k + 1 (step 2 of the plan in
`Refine/README.md`). Fixed: the memory μ1 right after the decode, the input buffer's chunk ce (its slots at E), the
payload's chunk cp, the chunks `csOf j` that instruction j's decoded slot owns, the instructions `xs j` and the
historical lookup lk. Before instruction k, for the snapshot μ0 and the chunks to keep `Kp`:

* μ0 is μ1 on ce's data and on [2^31, 2^32) (the stack and the frame);
* cp and the chunks of the instructions still to come are kept, those with their data as in μ1; kept chunks have
  distinct addresses;
* the output slots written so far, B j (j < k), are `SlotOK` for refine's output instruction `outT lk (xs j)`,
  owning chunks `own j` that are kept, not ce or cp, not any later instruction's, and pairwise apart.

`inv_pass`, `inv_export` and `inv_lookup` are the three steps (the obligations `PassOkT`, `ExportOkT`, `LookupOk`).
GP v0.8.0 Appendix B.4 (Ψ_R); `Spec.refine`'s `is.mapM (refineInstr C)`.
-/

namespace Services.Bootstrap.Refine.InvT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.SlotT Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.LoopAll
  Services.Bootstrap.Refine.LoopT Services.Bootstrap.Refine.PkgT Services.Bootstrap.Refine.SpecRunT
  Services.Bootstrap.Refine.ExportOkOf Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.LookupStep2

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **T1c's loop invariant before instruction k** (see the module doc). -/
def Inv (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program) (C : Spec.Consts)
    (lk : Nat → List UInt8 → Option (List UInt8)) (xs : Nat → Spec.Instr) (μ1 : Memory) (ce cp : Chunk)
    (csOf : Nat → List Chunk) (n k : Nat) (μ0 : Memory) (Kp : Chunk → Prop) (B : Nat → List UInt8) : Prop :=
  (∀ a, InData ce a → μ0.read a = μ1.read a) ∧
  (∀ a, 2147483648 ≤ a → a < 4294967296 → μ0.read a = μ1.read a) ∧
  Kp cp ∧
  (∀ c d, Kp c → Kp d → c.addr = d.addr → c = d) ∧
  (∀ c, Kp c → ∀ a, InData c a → a < 2147483648) ∧
  (∀ j, k ≤ j → j < n → ∀ c ∈ csOf j, Kp c ∧ ∀ a, InData c a → μ0.read a = μ1.read a) ∧
  ∃ own : Nat → Chunk → Prop,
    (∀ j, j < k → SlotOK env K pb p P (DRt C 0) (outT lk (xs j)).encode (B j) (own j) μ0 ∧
      (outT lk (xs j)).encode.length < 8589934592) ∧
    (∀ j c, j < k → own j c → Kp c ∧ c ≠ ce ∧ c ≠ cp ∧ ∀ j', k ≤ j' → j' < n → c ∉ csOf j') ∧
    (∀ j j' c, j < k → j' < k → j ≠ j' → own j c → own j' c → False)

/-- The decode's facts about the chunks, as `Inv`'s steps use them. -/
def CsOk (ce cp : Chunk) (csOf : Nat → List Chunk) (n : Nat) : Prop :=
  (∀ j c, j < n → c ∈ csOf j → c ≠ ce ∧ c ≠ cp) ∧
  (∀ j j', j < n → j' < n → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j')

/-- Instruction k's input slot, read in μ0, is its octets in μ1 (the slot lies in ce's data). -/
theorem in_slot {μ0 μ1 : Memory} {ce : Chunk} {E k : Nat}
    (hce : ∀ a, InData ce a → μ0.read a = μ1.read a)
    (hin : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a) :
    μ0.readN (E + 232 * k) 232 = μ1.readN (E + 232 * k) 232 :=
  Memory.readN_congr (fun j hj => hce _ (hin _ (by omega) (by omega)))

/-- **A pass-through step keeps `Inv`**: instruction k's package gives `PassSlot` for its decoded slot (in μ1, owning
    chunks of `csOf k`), and refine returns it unchanged. -/
theorem inv_pass {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {C : Spec.Consts}
    {lk : Nat → List UInt8 → Option (List UInt8)} {xs : Nat → Spec.Instr} {μ1 : Memory} {ce cp : Chunk}
    {csOf : Nat → List Chunk} {n E k : Nat} {μ0 : Memory} {Kp : Chunk → Prop} {B : Nat → List UInt8}
    {x : RefineCtx} (hcs : CsOk ce cp csOf n) (hk : k < n)
    (hin : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a)
    (hps : PassSlot env K pb p P C (xs k) (csOf k) (μ1.readN (E + 232 * k) 232) μ1)
    (hout : outT lk (xs k) = xs k) (hlen : (xs k).encode.length < 8589934592)
    (hI : Inv env K pb p P C lk xs μ1 ce cp csOf n k μ0 Kp B) :
    PassOkT μ0 E k Kp B x x (Inv env K pb p P C lk xs μ1 ce cp csOf n (k + 1)) := by
  obtain ⟨ice, ifr, icp, iaddr, ibnd, irest, own, iown, iownK, idisj⟩ := hI
  obtain ⟨D, own0, hW, h0, hS, hown0⟩ := hps
  have hsl := in_slot (k := k) ice hin
  refine ⟨Kp, fun bs => bs = μ1.readN (E + 232 * k) 232, ⟨D, ?_, ?_, ⟨fun h => absurd h (by omega), fun _ => hsl⟩,
    fun _ h => h, rfl⟩, fun B' hB' hQ => ?_⟩
  · unfold rdN
    rw [Decode.Loop.readN_sub μ0 _ 232 44 1 _ hsl (by omega)]; exact hW
  · rw [← PVM.readN_take μ0 _ 232 8 (by omega), hsl]; exact h0
  have kc : ∀ c, own0 c → Kp c ∧ ∀ a, InData c a → μ0.read a = μ1.read a := fun c hc =>
    irest k (Nat.le_refl _) hk c (hown0 c hc)
  refine ⟨ice, ifr, icp, iaddr, ibnd, fun j h1 h2 => irest j (by omega) h2, fun j => if j = k then own0 else own j,
    fun j hj => ?_, fun j c hj hc => ?_, fun j j' c hj hj' hne hc hc' => ?_⟩
  · by_cases e : j = k
    · subst e
      simp only [eq_self_iff_true, if_true]
      rw [hQ, hout]
      exact ⟨hS.congr (fun d hd a ha => ((kc d hd).2 a ha).symm), hlen⟩
    · simp only [e, if_false]
      rw [hB' j (by omega)]
      exact iown j (by omega)
  · by_cases e : j = k
    · subst e
      simp only [eq_self_iff_true, if_true] at hc
      have hm := hown0 c hc
      exact ⟨(kc c hc).1, (hcs.1 j c hk hm).1, (hcs.1 j c hk hm).2, fun j' h1 h2 hm' =>
        hcs.2 j j' hk h2 (by omega) c hm hm'⟩
    · simp only [e, if_false] at hc
      obtain ⟨a1, a2, a3, a4⟩ := iownK j c (by omega) hc
      exact ⟨a1, a2, a3, fun j' h1 h2 => a4 j' (by omega) h2⟩
  · by_cases e : j = k
    · subst e
      simp only [if_true, show j' ≠ j from fun h => hne h.symm, if_false] at hc hc'
      exact (iownK j' c (by omega) hc').2.2.2 j (Nat.le_refl _) hk (hown0 c hc)
    · by_cases e' : j' = k
      · subst e'
        simp only [e, if_true, if_false] at hc hc'
        exact (iownK j c (by omega) hc).2.2.2 j' (Nat.le_refl _) hk (hown0 c hc')
      · simp only [e, e', if_false] at hc hc'
        exact idisj j j' c (by omega) (by omega) hne hc hc'

/-- **A step whose output slot owns nothing keeps `Inv`**, with chunks to keep Kp' between Kp minus `csOf k` and
    Kp. -/
theorem inv_noown {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {C : Spec.Consts}
    {lk : Nat → List UInt8 → Option (List UInt8)} {xs : Nat → Spec.Instr} {μ1 : Memory} {ce cp : Chunk}
    {csOf : Nat → List Chunk} {n k : Nat} {μ0 : Memory} {Kp Kp' : Chunk → Prop} {B B' : Nat → List UInt8}
    (hcs : CsOk ce cp csOf n) (hk : k < n)
    (hK' : ∀ d, Kp' d → Kp d) (hK2 : ∀ d, Kp d → d ∉ csOf k → Kp' d) (hB' : ∀ j, j < k → B' j = B j)
    (hS : SlotOK env K pb p P (DRt C 0) (outT lk (xs k)).encode (B' k) (fun _ => False) μ0)
    (hlen : (outT lk (xs k)).encode.length < 8589934592)
    (hI : Inv env K pb p P C lk xs μ1 ce cp csOf n k μ0 Kp B) :
    Inv env K pb p P C lk xs μ1 ce cp csOf n (k + 1) μ0 Kp' B' := by
  obtain ⟨ice, ifr, icp, iaddr, ibnd, irest, own, iown, iownK, idisj⟩ := hI
  refine ⟨ice, ifr, hK2 cp icp (fun h => (hcs.1 k cp hk h).2 rfl),
    fun c d hc hd => iaddr c d (hK' c hc) (hK' d hd), fun c hc => ibnd c (hK' c hc),
    fun j h1 h2 c hc => ⟨hK2 c (irest j (by omega) h2 c hc).1 (fun h' => hcs.2 j k h2 hk (by omega) c hc h'),
      (irest j (by omega) h2 c hc).2⟩,
    fun j => if j = k then fun _ => False else own j, fun j hj => ?_, fun j c hj hc => ?_,
    fun j j' c hj hj' hne hc hc' => ?_⟩
  · by_cases e : j = k
    · subst e; simp only [eq_self_iff_true, if_true]; exact ⟨hS, hlen⟩
    · simp only [e, if_false]; rw [hB' j (by omega)]; exact iown j (by omega)
  · by_cases e : j = k
    · subst e; simp only [eq_self_iff_true, if_true] at hc
    · simp only [e, if_false] at hc
      obtain ⟨a1, a2, a3, a4⟩ := iownK j c (by omega) hc
      exact ⟨hK2 c a1 (a4 k (Nat.le_refl _) hk), a2, a3, fun j' h1 h2 => a4 j' (by omega) h2⟩
  · by_cases e : j = k
    · subst e; simp only [eq_self_iff_true, if_true] at hc
    · by_cases e' : j' = k
      · subst e'; simp only [eq_self_iff_true, if_true] at hc'
      · simp only [e, e', if_false] at hc hc'
        exact idisj j j' c (by omega) (by omega) hne hc hc'

/-- `Exported n`'s output slot owns nothing and is short. -/
theorem exported_slot {p : ByteArray} {P : Program} [HasCode p P] [CodeX.HasCodeX p P] [CodeA.HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (C : Spec.Consts)
    (m : Nat) (hm : m < 18446744073709551616) (bs : List UInt8) (hb : kindRep (.exported m) bs) (μ0 : Memory) :
    SlotOK env K pb p P (DRt C 0) (Spec.Instr.exported m).encode bs (fun _ => False) μ0 ∧
      (Spec.Instr.exported m).encode.length < 8589934592 :=
  ⟨SlotFixed.slotOK_fixed env K pb hK1 hK C _ trivial (show Spec.fits 8 m by unfold Spec.fits; omega) bs hb μ0,
    by simp [Spec.Instr.encode, Codec.fixed]⟩

/-- **An `ExportSegs ds` step (ds ≠ []) keeps `Inv`**: the decoded slot's segments are its chunks `csOf k`, which
    the step frees (Kp' = Kp minus `csOf k`); refine returns `Exported |ds|`. -/
theorem inv_export_big {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} [HasCode p P]
    [CodeX.HasCodeX p P] [CodeA.HasCodeA p P] (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    {C : Spec.Consts} {lk : Nat → List UInt8 → Option (List UInt8)} {xs : Nat → Spec.Instr} {μ1 : Memory}
    {ce cp : Chunk} {csOf : Nat → List Chunk} {n E k : Nat} {μ0 : Memory} {Kp : Chunk → Prop}
    {B : Nat → List UInt8} {x : RefineCtx} (hcs : CsOk ce cp csOf n) (hk : k < n)
    (hin : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a)
    {ds : List (List UInt8)} (hx : xs k = .exportSegs ds)
    (hrep : Decode.VecVecOwn.VecVecRepC (9223372036854775807 + 10) ds (csOf k) (μ1.readN (E + 232 * k) 232) μ0)
    (hb : 24 * ds.length < 1073741760) (hds : ∀ d ∈ ds, d.length < 1073741760)
    (hI : Inv env K pb p P C lk xs μ1 ce cp csOf n k μ0 Kp B) :
    ExportOkT env μ0 E k ce Kp B x (expDs env ds x) (Inv env K pb p P C lk xs μ1 ce cp csOf n (k + 1)) := by
  have hI' := hI
  obtain ⟨ice, -, -, iaddr, -, irest, -⟩ := hI'
  have hsl := in_slot (k := k) ice hin
  refine ⟨fun d => Kp d ∧ d ∉ csOf k, kindRep (.exported ds.length),
    export_ok_big (by rw [hsl]; exact hrep) hb hds
      (fun c hc => ⟨(irest k (Nat.le_refl _) hk c hc).1, (hcs.1 k c hk hc).1⟩)
      (fun d hd => ⟨hd.1, hd.2, fun c hc e => hd.2 ((iaddr d c hd.1 (irest k (Nat.le_refl _) hk c hc).1 e) ▸ hc)⟩)
      (fun bs h0 h8 => ⟨fun h => absurd h (by omega), fun _ => ⟨h0, h8⟩⟩) rfl, fun B' hB' hQ => ?_⟩
  have hS := exported_slot env K pb hK1 hK C ds.length (by omega) (B' k) hQ μ0
  refine inv_noown hcs hk (fun d hd => hd.1) (fun d hd hn => ⟨hd, hn⟩) hB' ?_ ?_ hI
  · rw [hx]; exact hS.1
  · rw [hx]; exact hS.2

/-- **An `ExportSegs []` step keeps `Inv`** (nothing exported; refine returns `Exported 0`). -/
theorem inv_export_empty {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} [HasCode p P]
    [CodeX.HasCodeX p P] [CodeA.HasCodeA p P] (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    {C : Spec.Consts} {lk : Nat → List UInt8 → Option (List UInt8)} {xs : Nat → Spec.Instr} {μ1 : Memory}
    {ce cp : Chunk} {csOf : Nat → List Chunk} {n E k : Nat} {μ0 : Memory} {Kp : Chunk → Prop}
    {B : Nat → List UInt8} {x : RefineCtx} (hcs : CsOk ce cp csOf n) (hk : k < n)
    (hin : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a)
    (hx : xs k = .exportSegs [])
    (hrep : let bs := μ1.readN (E + 232 * k) 232
      bs.take 8 = Num.encodeLE 8 9223372036854775817 ∧ (bs.drop 8).take 8 = Num.encodeLE 8 0 ∧
        (bs.drop 16).take 8 = Num.encodeLE 8 8 ∧ (bs.drop 24).take 8 = Num.encodeLE 8 0)
    (hI : Inv env K pb p P C lk xs μ1 ce cp csOf n k μ0 Kp B) :
    ExportOkT env μ0 E k ce Kp B x x (Inv env K pb p P C lk xs μ1 ce cp csOf n (k + 1)) := by
  have hI' := hI
  obtain ⟨ice, -⟩ := hI'
  have hsl := in_slot (k := k) ice hin
  refine ⟨Kp, kindRep (.exported 0), export_ok_empty (by rw [hsl]; exact hrep) (fun _ h => h)
      (fun bs h0 h8 => ⟨fun h => absurd h (by omega), fun _ => ⟨h0, h8⟩⟩) rfl, fun B' hB' hQ => ?_⟩
  have hS := exported_slot env K pb hK1 hK C 0 (by omega) (B' k) hQ μ0
  refine inv_noown hcs hk (fun d hd => hd) (fun d hd _ => hd) hB' ?_ ?_ hI
  · rw [hx]; exact hS.1
  · rw [hx]; exact hS.2

/-- `LookedUp(v)`'s encoding is short when its data is shorter than 2^31 octets. -/
theorem lu_len (v : Option (List UInt8)) (hv : ∀ d, v = some d → d.length < 2147483648) :
    (Spec.Instr.lookedUp v).encode.length < 8589934592 := by
  cases v with
  | none => simp [Spec.Instr.encode, Spec.opt]
  | some d =>
    have he : (Spec.Instr.lookedUp (some d)).encode = 18 :: 1 :: (Blob.encodeNat d.length ++ d) := by
      simp [Spec.Instr.encode, Spec.opt, Spec.bytes, Codec.nat]
    have := hv d rfl
    have h5 := PVM.encodeNat_len_le5 d.length (by omega)
    rw [he]; simp only [List.length_cons, List.length_append]; omega

/-- **An eager `Lookup` step keeps `Inv`**: instruction k is `Lookup(sv, h, true)` (its decoded slot `kindRep`), the
    historical lookup lk agrees with the host's (`lookupOf`); the output slot `LookedUp(lookupOf env sv h)` owns the
    preimage's chunk, if one is adopted. -/
theorem inv_lookup {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} [HasCode p P]
    [CodeX.HasCodeX p P] [CodeA.HasCodeA p P] (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    {C : Spec.Consts} {lk : Nat → List UInt8 → Option (List UInt8)} {xs : Nat → Spec.Instr} {μ1 : Memory}
    {ce cp : Chunk} {csOf : Nat → List Chunk} {n E k : Nat} {μ0 : Memory} {Kp : Chunk → Prop}
    {B : Nat → List UInt8} {x : RefineCtx} {cap0 : Nat} (hcs : CsOk ce cp csOf n) (hk : k < n)
    (hin : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → InData ce a)
    (hceB : ∀ a, InData ce a → a < 2147483648)
    {sv : Nat} {h : List UInt8} (hx : xs k = .lookup sv h true)
    (hrep : kindRep (.lookup sv h true) (μ1.readN (E + 232 * k) 232)) (hsv : sv < 4294967296)
    (hlk : lk sv h = LookupStep.lookupOf env sv h)
    (hlenL : ∀ d, LookupStep.lookupOf env sv h = some d → d.length < 9223372036854775808)
    (hgas : ∀ d, LookupStep.lookupOf env sv h = some d →
      Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap0)
    (hI : Inv env K pb p P C lk xs μ1 ce cp csOf n k μ0 Kp B) :
    LookupOk env cap0 μ0 E k ce Kp B x x (Inv env K pb p P C lk xs μ1 ce cp csOf n (k + 1)) := by
  have hI' := hI
  obtain ⟨ice, ifr, icp, iaddr, ibnd, irest, own, iown, iownK, idisj⟩ := hI'
  have hsl := in_slot (k := k) ice hin
  obtain ⟨r0, r8, r12, -⟩ := hrep
  have sub : ∀ o l, o + l ≤ 232 → μ0.readN (E + 232 * k + o) l = ((μ1.readN (E + 232 * k) 232).drop o).take l :=
    fun o l hl => by rw [← hsl]; exact Decode.Loop.readN_sub μ0 _ 232 o l _ rfl hl
  refine ⟨sv, h, ?_, by rw [sub 8 4 (by omega)]; exact r8, hsv, by rw [sub 12 32 (by omega)]; exact r12, hlenL,
    hgas, ?_⟩
  · rw [← PVM.readN_take μ0 _ 232 8 (by omega), hsl]; exact r0
  intro μ0' Kp' B' buf hB' hlu hown hnew
  have ho : outT lk (xs k) = .lookedUp (LookupStep.lookupOf env sv h) := by
    rw [hx]; exact congrArg Spec.Instr.lookedUp hlk
  revert hlu hown hnew ho
  generalize LookupStep.lookupOf env sv h = v
  intro hlu hown hnew ho
  cases v with
  | none =>
    obtain ⟨rfl, rfl⟩ := hown
    refine inv_noown hcs hk (fun _ h => h) (fun d hd _ => hd) hB' ?_ (by rw [ho]; exact lu_len none (by simp)) hI
    rw [ho]
    exact fun μ s el hel _ => SlotLU.slotW_lu env K pb hK1 hK C none (fun d e => by cases e) 0 (by decide) el μ s _
      (by rw [hel]; exact hlu) (fun d e => by cases e)
  | some d =>
    rcases hown with ⟨rfl, rfl, rfl, rfl⟩ | ⟨ch, hca, hcsz, hnK, rfl, hdat, hfar⟩
    · refine inv_noown hcs hk (fun _ h => h) (fun d hd _ => hd) hB' ?_
        (by rw [ho]; exact lu_len _ (fun d e => by cases e; simp)) hI
      rw [ho]
      exact fun μ s el hel _ => SlotLU.slotW_lu env K pb hK1 hK C (some []) (fun d e => by cases e; simp) 1
        (by decide) el μ s _ (by rw [hel]; exact hlu) (fun d' e hne => absurd (Option.some.inj e).symm hne)
    · obtain ⟨hn1, hn2, hn3, hn4⟩ := hnew ch (Or.inr rfl) hnK
      have hdl : d.length < 2147483648 := by omega
      have keep : ∀ a, a < 2147483648 → ¬ InData ch a → μ0'.read a = μ0.read a := fun a ha hc =>
        hfar a (by omega) (by unfold InData at hc; omega)
      have keepK : ∀ c, Kp c → ∀ a, InData c a → μ0'.read a = μ0.read a := fun c hc a ha =>
        keep a (ibnd c hc a ha) (fun hch => (hn2 a hch).2 c hc ha)
      refine ⟨fun a ha => (keep a (hceB a ha) (fun hch => (hn2 a hch).1 ha)).trans (ice a ha),
        fun a h1 h2 => (hfar a h2 (Or.inr (by omega))).trans (ifr a h1 h2), Or.inl icp, ?_, ?_,
        fun j h1 h2 c hc => ⟨Or.inl (irest j (by omega) h2 c hc).1, fun a ha =>
          (keepK c (irest j (by omega) h2 c hc).1 a ha).trans ((irest j (by omega) h2 c hc).2 a ha)⟩,
        fun j => if j = k then (· = ch) else own j, fun j hj => ?_, fun j c hj hc => ?_,
        fun j j' c hj hj' hne hc hc' => ?_⟩
      · rintro c e (hc | rfl) (he | rfl) hce'
        · exact iaddr c e hc he hce'
        · exact absurd hce' (hn4 c hc)
        · exact absurd hce'.symm (hn4 e he)
        · rfl
      · rintro c (hc | rfl) a ha
        · exact ibnd c hc a ha
        · unfold InData at ha; omega
      · by_cases e : j = k
        · subst e
          simp only [eq_self_iff_true, if_true]
          rw [ho]
          refine ⟨fun μ s el hel hown' => ?_, lu_len _ (fun d' e => by cases e; exact hdl)⟩
          obtain ⟨hcm, hcu, hcd⟩ := hown' ch rfl
          refine SlotLU.slotW_lu env K pb hK1 hK C (some d) (fun d' e => by cases e; omega) (ch.addr + 32)
            (by omega) el μ s _ (by rw [hel]; exact hlu) (fun d' e _ => ?_)
          cases e
          refine ⟨?_, ch, rfl, hcm, hcu, rfl, by omega⟩
          rw [Memory.readN_congr (fun i hi => hcd _ ⟨by omega, by omega⟩)]
          exact hdat
        · simp only [e, if_false]
          rw [hB' j (by omega)]
          exact ⟨(iown j (by omega)).1.congr (fun c hc a ha => keepK c (iownK j c (by omega) hc).1 a ha),
            (iown j (by omega)).2⟩
      · by_cases e : j = k
        · subst e
          simp only [eq_self_iff_true, if_true] at hc
          subst hc
          exact ⟨Or.inr rfl, hn1, fun e => hnK (e ▸ icp), fun j' h1 h2 hm =>
            hnK (irest j' (by omega) h2 c hm).1⟩
        · simp only [e, if_false] at hc
          obtain ⟨a1, a2, a3, a4⟩ := iownK j c (by omega) hc
          exact ⟨Or.inl a1, a2, a3, fun j' h1 h2 => a4 j' (by omega) h2⟩
      · by_cases e : j = k
        · subst e
          simp only [eq_self_iff_true, if_true, show j' ≠ j from fun h => hne h.symm, if_false] at hc hc'
          subst hc
          exact hnK (iownK j' c (by omega) hc').1
        · by_cases e' : j' = k
          · subst e'
            simp only [e, eq_self_iff_true, if_true, if_false] at hc hc'
            subst hc'
            exact hnK (iownK j c (by omega) hc).1
          · simp only [e, e', if_false] at hc hc'
            exact idisj j j' c (by omega) (by omega) hne hc hc'

end Services.Bootstrap.Refine.InvT
