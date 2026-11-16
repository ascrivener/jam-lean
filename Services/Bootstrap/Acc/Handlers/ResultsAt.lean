import Services.Bootstrap.Acc.Handlers.ResultsInit

/-!
# `ResultsAt`: the results `Vec` in memory (R4 of `docs/t2-remaining.md`)

`on_work_item` collects each instruction's `Result<InstructionRet, InstructionError>` (spec `Result`,
GP v0.8.0 Appendix B; bootstrap's own type) in a `Vec` of 144-octet items. The layout is the one
the results encoder reads (36346 … 36394 for the outer tag, then 36299's arms through the table at
68264: 30374 `unit`, 30512 `serviceId`, 30433 `length`, 30438 `transferred`, 30392 `hash`, 30567
`data`, 30640 `dataVec`), and the one the handlers write at `RES` (`Dispatch.lean`):

- `Err e`: the octet 255, then `e.tag` at + 1;
- `Ok r`: r's index (0 … 6), then
  - `serviceId i`, `length n`: the `u32` at + 4;
  - `transferred d a m`: d (`u32`) at + 4, a (`u64`) at + 8, the 128 octets of m at + 16;
  - `hash h`: the 32 octets of h at + 1;
  - `data d`: `Vec<u8>` { cap, ptr, len } at + 8, + 16, + 24, d the len octets at ptr;
  - `dataVec ds`: `Vec<Vec<u8>>` { cap, ptr, len } at + 8, + 16, + 24, element j the `Vec<u8>`
    at ptr + 24·j.

Every octet the value occupies (the item and its heap buffers) lies in the data of an allocated chunk
of the allocator state st, so frames that keep st's chunks with their data keep `ResultsAt`
(`ResultsAt.keep`). Buffers of length 0 are unconstrained (Rust's dangling pointer).
-/

namespace Services.Bootstrap.Acc.Handlers.Results

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Decode.LoopA
open JAM.Codec (fixed)

/-- The n octets from b lie in the data of allocated chunks of st. -/
def InHeap (st : State) (b n : Nat) : Prop :=
  ∀ k, k < n → ∃ d ∈ chunks st, d.used = true ∧ InData d (b + k)

/-- A `Vec<u8>` { cap, ptr, len } at v (three words) holding the octets bs in st's heap. -/
def VecAt (μ : Memory) (st : State) (v : Nat) (bs : List UInt8) : Prop :=
  ∃ cap ptr, μ.readN v 8 = Num.encodeLE 8 cap ∧ μ.readN (v + 8) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (v + 16) 8 = Num.encodeLE 8 bs.length ∧ μ.readN ptr bs.length = bs ∧ InHeap st ptr bs.length

/-- The `Ok` payload r of the item at a (its index octet at a). -/
def OkAt (μ : Memory) (st : State) (a : Nat) : Ret → Prop
  | .unit => μ.readN a 1 = [0]
  | .serviceId i => μ.readN a 1 = [1] ∧ μ.readN (a + 4) 4 = fixed 4 i ∧ i < 2 ^ 32
  | .length n => μ.readN a 1 = [2] ∧ μ.readN (a + 4) 4 = fixed 4 n ∧ n < 2 ^ 32
  | .transferred d am m => μ.readN a 1 = [3] ∧ μ.readN (a + 4) 4 = fixed 4 d ∧ d < 2 ^ 32 ∧
      μ.readN (a + 8) 8 = fixed 8 am ∧ am < 2 ^ 64 ∧ m.length = 128 ∧ μ.readN (a + 16) 128 = m
  | .hash h => μ.readN a 1 = [4] ∧ h.length = 32 ∧ μ.readN (a + 1) 32 = h
  | .data d => μ.readN a 1 = [5] ∧ VecAt μ st (a + 8) d
  | .dataVec ds => μ.readN a 1 = [6] ∧ ∃ cap ptr, μ.readN (a + 8) 8 = Num.encodeLE 8 cap ∧
      μ.readN (a + 16) 8 = Num.encodeLE 8 ptr ∧ μ.readN (a + 24) 8 = Num.encodeLE 8 ds.length ∧
      InHeap st ptr (24 * ds.length) ∧ ∀ j (hj : j < ds.length), VecAt μ st (ptr + 24 * j) ds[j]

/-- The 144-octet item at a holds the result r. -/
def ResultAt (μ : Memory) (st : State) (a : Nat) : Spec.Result → Prop
  | .error e => μ.readN a 1 = [255] ∧ μ.readN (a + 1) 1 = [UInt8.ofNat e.tag]
  | .ok r => OkAt μ st a r

/-- **The results**: the items at rp, rp + 144, … hold rs, and lie in st's heap. -/
def ResultsAt (μ : Memory) (st : State) (rp : Nat) (rs : List Spec.Result) : Prop :=
  InHeap st rp (144 * rs.length) ∧ ∀ j (hj : j < rs.length), ResultAt μ st (rp + 144 * j) rs[j]

/-- **The results `Vec` of `on_work_item`** in accumulate's frame: { cap, ptr, len } at sp + 448,
    sp + 456, sp + 464, holding rs. -/
def ResultsVec (μ : Memory) (st : State) (sp : Nat) (rs : List Spec.Result) : Prop :=
  ∃ cap rp, μ.readN (sp + 448) 8 = Num.encodeLE 8 cap ∧ μ.readN (sp + 456) 8 = Num.encodeLE 8 rp ∧
    μ.readN (sp + 464) 8 = Num.encodeLE 8 rs.length ∧ rs.length ≤ cap ∧ ResultsAt μ st rp rs

/-- The frame that keeps every allocated chunk of st, with its data. -/
def KeepsHeap (st st' : State) (μ μ' : Memory) : Prop :=
  ∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a

theorem InHeap.keep {st st' : State} {μ μ' : Memory} (hk : KeepsHeap st st' μ μ') {b n : Nat}
    (h : InHeap st b n) : InHeap st' b n ∧ μ'.readN b n = μ.readN b n := by
  refine ⟨fun k hk' => ?_, Memory.readN_congr fun j hj => ?_⟩
  · obtain ⟨d, hd, hu, hi⟩ := h k hk'
    exact ⟨d, (hk d hd hu).1, hu, hi⟩
  · obtain ⟨d, hd, hu, hi⟩ := h j hj
    exact (hk d hd hu).2 _ hi

theorem InHeap.sub {st : State} {b n b' n' : Nat} (h : InHeap st b n) (h1 : b ≤ b') (h2 : b' + n' ≤ b + n) :
    InHeap st b' n' := fun k hk => by
  obtain ⟨d, hd, hu, hi⟩ := h (b' - b + k) (by omega)
  exact ⟨d, hd, hu, by rw [show b' + k = b + (b' - b + k) by omega]; exact hi⟩

theorem VecAt.keep {st st' : State} {μ μ' : Memory} (hk : KeepsHeap st st' μ μ') {v : Nat} {bs : List UInt8}
    (hv : InHeap st v 24) (h : VecAt μ st v bs) : VecAt μ' st' v bs := by
  obtain ⟨cap, ptr, m0, m8, m16, md, hd⟩ := h
  obtain ⟨-, e0⟩ := InHeap.keep hk (hv.sub (b' := v) (n' := 8) (by omega) (by omega))
  obtain ⟨-, e8⟩ := InHeap.keep hk (hv.sub (b' := v + 8) (n' := 8) (by omega) (by omega))
  obtain ⟨-, e16⟩ := InHeap.keep hk (hv.sub (b' := v + 16) (n' := 8) (by omega) (by omega))
  obtain ⟨hd', ed⟩ := InHeap.keep hk hd
  exact ⟨cap, ptr, e0.trans m0, e8.trans m8, e16.trans m16, ed.trans md, hd'⟩

theorem OkAt.keep {st st' : State} {μ μ' : Memory} (hk : KeepsHeap st st' μ μ') {a : Nat} {r : Ret}
    (ha : InHeap st a 144) (h : OkAt μ st a r) : OkAt μ' st' a r := by
  have e : ∀ o n, o + n ≤ 144 → μ'.readN (a + o) n = μ.readN (a + o) n := fun o n h =>
    (InHeap.keep hk (ha.sub (b' := a + o) (n' := n) (by omega) (by omega))).2
  have e0 : μ'.readN a 1 = μ.readN a 1 := e 0 1 (by omega)
  cases r with
  | unit => exact e0.trans h
  | serviceId i => exact ⟨e0.trans h.1, (e 4 4 (by omega)).trans h.2.1, h.2.2⟩
  | length n => exact ⟨e0.trans h.1, (e 4 4 (by omega)).trans h.2.1, h.2.2⟩
  | transferred d am m =>
    obtain ⟨h0, h4, hd, h8, ha', hl, h16⟩ := h
    exact ⟨e0.trans h0, (e 4 4 (by omega)).trans h4, hd, (e 8 8 (by omega)).trans h8, ha', hl,
      (e 16 128 (by omega)).trans h16⟩
  | hash hh => exact ⟨e0.trans h.1, h.2.1, (e 1 32 (by omega)).trans h.2.2⟩
  | data d => exact ⟨e0.trans h.1, VecAt.keep hk (ha.sub (by omega) (by omega)) h.2⟩
  | dataVec ds =>
    obtain ⟨h0, cap, ptr, m8, m16, m24, hp, hj⟩ := h
    refine ⟨e0.trans h0, cap, ptr, (e 8 8 (by omega)).trans m8, (e 16 8 (by omega)).trans m16,
      (e 24 8 (by omega)).trans m24, (InHeap.keep hk hp).1, fun j hj' => ?_⟩
    exact VecAt.keep hk (hp.sub (by omega) (by omega)) (hj j hj')

theorem ResultAt.keep {st st' : State} {μ μ' : Memory} (hk : KeepsHeap st st' μ μ') {a : Nat} {r : Spec.Result}
    (ha : InHeap st a 144) (h : ResultAt μ st a r) : ResultAt μ' st' a r := by
  cases r with
  | error e =>
    exact ⟨(InHeap.keep hk (ha.sub (b' := a) (n' := 1) (by omega) (by omega))).2.trans h.1,
      (InHeap.keep hk (ha.sub (b' := a + 1) (n' := 1) (by omega) (by omega))).2.trans h.2⟩
  | ok r => exact OkAt.keep hk ha h

/-- **Frames that keep st's chunks with their data keep `ResultsAt`.** -/
theorem ResultsAt.keep {st st' : State} {μ μ' : Memory} (hk : KeepsHeap st st' μ μ') {rp : Nat}
    {rs : List Spec.Result} (h : ResultsAt μ st rp rs) : ResultsAt μ' st' rp rs :=
  ⟨(InHeap.keep hk h.1).1, fun j hj => ResultAt.keep hk (h.1.sub (by omega) (by
    have : 144 * j + 144 ≤ 144 * rs.length := by have := Nat.mul_le_mul_left 144 (Nat.succ_le_of_lt hj); omega
    omega)) (h.2 j hj)⟩

/-- The empty results. -/
theorem ResultsAt.nil (μ : Memory) (st : State) (rp : Nat) : ResultsAt μ st rp [] :=
  ⟨fun k hk => absurd hk (by simp), fun j hj => absurd hj (by simp)⟩

end Services.Bootstrap.Acc.Handlers.Results
