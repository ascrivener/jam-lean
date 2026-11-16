import Services.Bootstrap.Refine.ExitRunW
import Services.Bootstrap.Refine.EncRSA
import Services.Bootstrap.Refine.EncProvide
import Services.Bootstrap.Refine.Top

/-!
# T1c's output slots: what the exit needs of each

`slotRep y bs μ` is the slot of a decoded instruction y as the decoder leaves it and the encoder and `Debug` read it:
`Kinds.kindRep` for the fixed-width kinds and the decode side's representations for the others (their heap octets in
μ). `DRt C` is the `Debug` line's slot predicate on T1c: some well-formed instruction's `slotRep`; the named
hypothesis is `ExitRun.DebugLineOk … (DRt C)` (it contains `Top.DRm C`).

`SlotW` is what `ExitRunW.exit_runW` needs of one output slot at el (an encoder arm `EncOkMH 232` for the slot's
encoding reading the heap octets `src`, the `Debug` predicate, and a variant whose drop does nothing or a heap element
owning `own`); `SlotOK` is `SlotW` for every memory and state that keep the owned chunks' data as in a reference
memory μr. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code), Appendix C (ℰ).
-/

namespace Services.Bootstrap.Refine.SlotT

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.GrowH
  Services.Bootstrap.Refine.Kinds Services.Bootstrap.Refine.DropVecH Services.Bootstrap.Refine.DropVecW

/-- **The slot of a decoded instruction y** (232 octets bs, heap octets in μ): its discriminant word and fields at
    their Rust offsets, as `Decode` leaves them; the vectors' octets at the buffers the slot points to. -/
def slotRep : Spec.Instr → List UInt8 → Memory → Prop
  | .createService h l g m b memo r f id => fun bs μ =>
      match r with
      | none => Decode.CreateServiceElem.CreateServiceNoneRep h (Codec.fixed 8 l) (Codec.fixed 8 g)
          (Codec.fixed 8 m) (Codec.fixed 8 b) memo (Codec.fixed 8 f) (Spec.opt (Codec.fixed 4) id) bs
      | some d => Decode.CreateServiceElem.CreateServiceSomeRep d.length d h (Codec.fixed 8 l) (Codec.fixed 8 g)
          (Codec.fixed 8 m) (Codec.fixed 8 b) memo (Codec.fixed 8 f) (Spec.opt (Codec.fixed 4) id) bs μ
  | .deleteItems ks => Decode.VecVecElem.VecVecRep 9223372036854775812 ks
  | .bless m a v r z => Decode.BlessHeap.BlessRep (Codec.fixed 4 m) (Codec.fixed 4 a) (Codec.fixed 4 v)
      (Codec.fixed 4 r) z.length (z.map (fun (s, g) => Codec.fixed 4 s ++ Codec.fixed 8 g)).flatten
  | .assign c q a => Decode.Assign.AssignRep q.length (Codec.fixed 2 c) q.flatten (Codec.fixed 4 a)
  | .designate ks => Decode.DesignateHeap.DesignateRep ks.length ks.flatten
  | .provide s (.hash h) => fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧
      (bs.drop 8).take 1 = [0] ∧ (bs.drop 9).take 32 = h ∧ (bs.drop 48).take 4 = Codec.fixed 4 s
  | .provide s (.inline d) => Decode.LookupProvideElem.ProvideInlineRep (Codec.fixed 4 s) d.length d
  | .lookedUp none => fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
      (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615
  | .lookedUp (some d) => Decode.LookupProvideElem.LookedUpSomeRep d.length d
  | .imported ds => Decode.VecVecElem.VecVecRep 9223372036854775826 ds
  | .randomStorageAccumulate none => EncRSA.RSAErrRep
  | .randomStorageAccumulate (some ks) => Decode.RandomStorageOk.RandomStorageOkRep ks.length ks.flatten
  | .assignForGasCost c q a => Decode.AssignGas.AssignGasRep (Codec.fixed 2 c) q.length q.flatten (Codec.fixed 4 a)
  | y => fun bs _ => kindRep y bs

/-- **The `Debug` line's slot predicate on T1c**: the slot of some well-formed instruction. -/
def DRt (C : Spec.Consts) (_j : Nat) (bs : List UInt8) (μ : Memory) : Prop :=
  ∃ y : Spec.Instr, y.WF C ∧ slotRep y bs μ

/-- `slotRep` is `kindRep` on the milestone's kinds. -/
theorem slotRep_fixed {y : Spec.Instr} (hm : MFixed y) (bs : List UInt8) (μ : Memory) :
    slotRep y bs μ ↔ kindRep y bs := by
  cases y <;> simp only [MFixed] at hm <;> exact Iff.rfl

/-- `DRt` contains the milestone's `Top.DRm`. -/
theorem drm_drt (C : Spec.Consts) (j : Nat) (bs : List UInt8) (μ : Memory) (h : Top.DRm C j bs μ) :
    DRt C j bs μ := by
  obtain ⟨y, hm, hw, hk⟩ := h
  exact ⟨y, hw, (slotRep_fixed hm bs μ).mpr hk⟩

/-- **What the exit needs of the output slot at el** (in memory μ, state s, owning the chunks `own`): an encoder arm
    for the slot's encoding `enc` (`EncOkMH 232`, reading the heap octets `src`, which lie in owned chunks), the slot
    satisfying its representation `rep` and a `Debug` predicate `DR` within `DRt`, both depending on memory only through
    `src`; and a variant whose drop does nothing, or a heap element owning `own` (`HeapElW`). -/
def SlotW (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program)
    (DRt : List UInt8 → Memory → Prop) (enc : List UInt8) (el : Nat) (μ : Memory) (s : State)
    (own : Chunk → Prop) : Prop :=
  ∃ (rep DR : List UInt8 → Memory → Prop) (src : Nat → Nat → Prop),
    Encode.EncMH.EncOkMH env K pb p P 232 enc rep src ∧ rep (μ.readN el 232) μ ∧ DR (μ.readN el 232) μ ∧
    (∀ bs μ, DR bs μ → DRt bs μ) ∧
    (∀ bs μ μ', (∀ q m, src q m → μ'.readN q m = μ.readN q m) → rep bs μ → rep bs μ') ∧
    (∀ bs μ μ', (∀ q m, src q m → μ'.readN q m = μ.readN q m) → DR bs μ → DR bs μ') ∧
    (∀ q m, src q m → ∃ c, own c ∧ c.addr + 32 ≤ q ∧ q + m ≤ c.addr + 32 * c.size) ∧
    ((∃ t, DropOut.NoDrop t ∧ μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨ HeapElW μ s el own)

/-- **An output slot's octets bs, good in any memory that keeps the owned chunks as in μr**: `SlotW` at every slot
    address holding bs, in every memory and state where the chunks `own` are allocated with their data as in μr. -/
def SlotOK (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program)
    (DRt : List UInt8 → Memory → Prop) (enc : List UInt8) (bs : List UInt8) (own : Chunk → Prop) (μr : Memory) :
    Prop :=
  ∀ (μ : Memory) (s : State) (el : Nat), μ.readN el 232 = bs →
    (∀ d, own d → d ∈ chunks s ∧ d.used = true ∧ ∀ a, InData d a → μ.read a = μr.read a) →
    SlotW env K pb p P DRt enc el μ s own

/-- `SlotOK` depends on the reference memory only through the owned chunks' data. -/
theorem SlotOK.congr {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program}
    {DRt : List UInt8 → Memory → Prop} {enc bs : List UInt8} {own : Chunk → Prop} {μr μr' : Memory}
    (h : SlotOK env K pb p P DRt enc bs own μr)
    (hk : ∀ d, own d → ∀ a, InData d a → μr'.read a = μr.read a) :
    SlotOK env K pb p P DRt enc bs own μr' :=
  fun μ s el hb ho => h μ s el hb (fun d hd => ⟨(ho d hd).1, (ho d hd).2.1, fun a ha => by
    rw [(ho d hd).2.2 a ha, hk d hd a ha]⟩)

/-- `SlotOK` for fewer owned chunks is not implied; but `SlotOK` with no owned chunks holds in every memory. -/
theorem SlotOK.noown {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program}
    {DRt : List UInt8 → Memory → Prop} {enc bs : List UInt8} {μr : Memory}
    (h : SlotOK env K pb p P DRt enc bs (fun _ => False) μr) (μr' : Memory) :
    SlotOK env K pb p P DRt enc bs (fun _ => False) μr' :=
  h.congr (fun _ hd => hd.elim)

end Services.Bootstrap.Refine.SlotT
