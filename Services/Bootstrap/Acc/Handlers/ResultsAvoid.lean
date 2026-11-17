import Services.Bootstrap.Acc.Handlers.ResultsAt

/-!
# `ResultsAvoid`: the results held in chunks outside a set of freed buffers

`ResultsAt` (GP v0.8.0 Appendix B, the results of Ω_W; bootstrap's own `Vec` layout) says every octet
the results occupy lies in the data of an allocated chunk of st. Before the results are written (row 11,
R7), the instructions' `IntoIter` is dropped, freeing the buffers `iterFree` (`InstrRep.lean`). The
results must survive that drop, so their octets must lie in chunks whose data address is not freed.

`InHeapP C`, `VecAtP`, `OkAtP`, `ResultAtP` and `ResultsAtP` are `InHeap`, …, `ResultsAt` with the
allocated chunks of st replaced by any chunk predicate C. `ResultsAvoid μ st rp rs F` is `ResultsAtP` for
the allocated chunks of st whose data address is not in F. It implies `ResultsAt` (`ResultsAvoid.toAt`).
A run that keeps every allocated chunk not in F with its data (`Kept`) keeps it (`ResultsAvoid.keep`).
-/

namespace Services.Bootstrap.Acc.Handlers.Results

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Decode.LoopA
open JAM.Codec (fixed)

/-- The n octets from b lie in the data of chunks satisfying C. -/
def InHeapP (C : Chunk → Prop) (b n : Nat) : Prop :=
  ∀ k, k < n → ∃ d, C d ∧ InData d (b + k)

/-- `VecAt`, with the chunks C. -/
def VecAtP (μ : Memory) (C : Chunk → Prop) (v : Nat) (bs : List UInt8) : Prop :=
  ∃ cap ptr, μ.readN v 8 = Num.encodeLE 8 cap ∧ μ.readN (v + 8) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (v + 16) 8 = Num.encodeLE 8 bs.length ∧ μ.readN ptr bs.length = bs ∧ InHeapP C ptr bs.length

/-- `OkAt`, with the chunks C. -/
def OkAtP (μ : Memory) (C : Chunk → Prop) (a : Nat) : Ret → Prop
  | .unit => μ.readN a 1 = [0]
  | .serviceId i => μ.readN a 1 = [1] ∧ μ.readN (a + 4) 4 = fixed 4 i ∧ i < 2 ^ 32
  | .length n => μ.readN a 1 = [2] ∧ μ.readN (a + 4) 4 = fixed 4 n ∧ n < 2 ^ 32
  | .transferred d am m => μ.readN a 1 = [3] ∧ μ.readN (a + 4) 4 = fixed 4 d ∧ d < 2 ^ 32 ∧
      μ.readN (a + 8) 8 = fixed 8 am ∧ am < 2 ^ 64 ∧ m.length = 128 ∧ μ.readN (a + 16) 128 = m
  | .hash h => μ.readN a 1 = [4] ∧ h.length = 32 ∧ μ.readN (a + 1) 32 = h
  | .data d => μ.readN a 1 = [5] ∧ VecAtP μ C (a + 8) d
  | .dataVec ds => μ.readN a 1 = [6] ∧ ∃ cap ptr, μ.readN (a + 8) 8 = Num.encodeLE 8 cap ∧
      μ.readN (a + 16) 8 = Num.encodeLE 8 ptr ∧ μ.readN (a + 24) 8 = Num.encodeLE 8 ds.length ∧
      InHeapP C ptr (24 * ds.length) ∧ ∀ j (hj : j < ds.length), VecAtP μ C (ptr + 24 * j) ds[j]

/-- `ResultAt`, with the chunks C. -/
def ResultAtP (μ : Memory) (C : Chunk → Prop) (a : Nat) : Spec.Result → Prop
  | .error e => μ.readN a 1 = [255] ∧ μ.readN (a + 1) 1 = [UInt8.ofNat e.tag]
  | .ok r => OkAtP μ C a r

/-- `ResultsAt`, with the chunks C. -/
def ResultsAtP (μ : Memory) (C : Chunk → Prop) (rp : Nat) (rs : List Spec.Result) : Prop :=
  InHeapP C rp (144 * rs.length) ∧ ∀ j (hj : j < rs.length), ResultAtP μ C (rp + 144 * j) rs[j]

/-- The allocated chunks of st whose data address is not in F. -/
def AvoidC (st : State) (F : List Nat) (d : Chunk) : Prop :=
  d ∈ chunks st ∧ d.used = true ∧ d.addr + 32 ∉ F

/-- **The results avoid F**: the items at rp, rp + 144, … hold rs, and every octet they occupy lies in an
    allocated chunk of st whose data address is not in F. -/
def ResultsAvoid (μ : Memory) (st : State) (rp : Nat) (rs : List Spec.Result) (F : List Nat) : Prop :=
  ResultsAtP μ (AvoidC st F) rp rs

section Mono

variable {μ μ' : Memory} {C C' : Chunk → Prop}

theorem InHeapP.mono (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {b n : Nat}
    (h : InHeapP C b n) : InHeapP C' b n ∧ μ'.readN b n = μ.readN b n := by
  refine ⟨fun k hk => ?_, Memory.readN_congr fun j hj => ?_⟩
  · obtain ⟨d, hd, hi⟩ := h k hk
    exact ⟨d, (hC d hd).1, hi⟩
  · obtain ⟨d, hd, hi⟩ := h j hj
    exact (hC d hd).2 _ hi

theorem InHeapP.sub {b n b' n' : Nat} (h : InHeapP C b n) (h1 : b ≤ b') (h2 : b' + n' ≤ b + n) :
    InHeapP C b' n' := fun k hk => by
  obtain ⟨d, hd, hi⟩ := h (b' - b + k) (by omega)
  exact ⟨d, hd, by rw [show b' + k = b + (b' - b + k) by omega]; exact hi⟩

theorem VecAtP.mono (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {v : Nat}
    {bs : List UInt8} (hv : InHeapP C v 24) (h : VecAtP μ C v bs) : VecAtP μ' C' v bs := by
  obtain ⟨cap, ptr, m0, m8, m16, md, hd⟩ := h
  obtain ⟨-, e0⟩ := InHeapP.mono hC (hv.sub (b' := v) (n' := 8) (by omega) (by omega))
  obtain ⟨-, e8⟩ := InHeapP.mono hC (hv.sub (b' := v + 8) (n' := 8) (by omega) (by omega))
  obtain ⟨-, e16⟩ := InHeapP.mono hC (hv.sub (b' := v + 16) (n' := 8) (by omega) (by omega))
  obtain ⟨hd', ed⟩ := InHeapP.mono hC hd
  exact ⟨cap, ptr, e0.trans m0, e8.trans m8, e16.trans m16, ed.trans md, hd'⟩

theorem OkAtP.mono (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {a : Nat} {r : Ret}
    (ha : InHeapP C a 144) (h : OkAtP μ C a r) : OkAtP μ' C' a r := by
  have e : ∀ o n, o + n ≤ 144 → μ'.readN (a + o) n = μ.readN (a + o) n := fun o n h =>
    (InHeapP.mono hC (ha.sub (b' := a + o) (n' := n) (by omega) (by omega))).2
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
  | data d => exact ⟨e0.trans h.1, VecAtP.mono hC (ha.sub (by omega) (by omega)) h.2⟩
  | dataVec ds =>
    obtain ⟨h0, cap, ptr, m8, m16, m24, hp, hj⟩ := h
    refine ⟨e0.trans h0, cap, ptr, (e 8 8 (by omega)).trans m8, (e 16 8 (by omega)).trans m16,
      (e 24 8 (by omega)).trans m24, (InHeapP.mono hC hp).1, fun j hj' => ?_⟩
    exact VecAtP.mono hC (hp.sub (by omega) (by omega)) (hj j hj')

theorem ResultAtP.mono (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {a : Nat}
    {r : Spec.Result} (ha : InHeapP C a 144) (h : ResultAtP μ C a r) : ResultAtP μ' C' a r := by
  cases r with
  | error e =>
    exact ⟨(InHeapP.mono hC (ha.sub (b' := a) (n' := 1) (by omega) (by omega))).2.trans h.1,
      (InHeapP.mono hC (ha.sub (b' := a + 1) (n' := 1) (by omega) (by omega))).2.trans h.2⟩
  | ok r => exact OkAtP.mono hC ha h

/-- **`ResultsAtP` is monotone in the chunks**, along any frame that keeps the data of the chunks C. -/
theorem ResultsAtP.mono (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {rp : Nat}
    {rs : List Spec.Result} (h : ResultsAtP μ C rp rs) : ResultsAtP μ' C' rp rs :=
  ⟨(InHeapP.mono hC h.1).1, fun j hj => ResultAtP.mono hC (h.1.sub (by omega) (by
    have : 144 * j + 144 ≤ 144 * rs.length := by have := Nat.mul_le_mul_left 144 (Nat.succ_le_of_lt hj); omega
    omega)) (h.2 j hj)⟩

end Mono

section ToAt

variable {μ : Memory} {st : State} {C : Chunk → Prop}

theorem InHeapP.toAt (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true) {b n : Nat} (h : InHeapP C b n) :
    InHeap st b n := fun k hk => by
  obtain ⟨d, hd, hi⟩ := h k hk
  exact ⟨d, (hC d hd).1, (hC d hd).2, hi⟩

theorem VecAtP.toAt (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true) {v : Nat} {bs : List UInt8}
    (h : VecAtP μ C v bs) : VecAt μ st v bs := by
  obtain ⟨cap, ptr, m0, m8, m16, md, hd⟩ := h
  exact ⟨cap, ptr, m0, m8, m16, md, hd.toAt hC⟩

theorem OkAtP.toAt (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true) {a : Nat} {r : Ret}
    (h : OkAtP μ C a r) : OkAt μ st a r := by
  cases r with
  | unit => exact h
  | serviceId i => exact h
  | length n => exact h
  | transferred d am m => exact h
  | hash hh => exact h
  | data d => exact ⟨h.1, h.2.toAt hC⟩
  | dataVec ds =>
    obtain ⟨h0, cap, ptr, m8, m16, m24, hp, hj⟩ := h
    exact ⟨h0, cap, ptr, m8, m16, m24, hp.toAt hC, fun j hj' => (hj j hj').toAt hC⟩

theorem ResultsAtP.toAt (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true) {rp : Nat} {rs : List Spec.Result}
    (h : ResultsAtP μ C rp rs) : ResultsAt μ st rp rs := by
  refine ⟨h.1.toAt hC, fun j hj => ?_⟩
  have h2 := h.2 j hj
  cases e : rs[j] with
  | error er => rw [e] at h2; exact h2
  | ok r => rw [e] at h2; exact OkAtP.toAt hC h2

end ToAt

/-- **`ResultsAvoid` implies `ResultsAt`.** -/
theorem ResultsAvoid.toAt {μ : Memory} {st : State} {rp : Nat} {rs : List Spec.Result} {F : List Nat}
    (h : ResultsAvoid μ st rp rs F) : ResultsAt μ st rp rs :=
  ResultsAtP.toAt (fun _ hd => ⟨hd.1, hd.2.1⟩) h

/-- **A run that keeps every allocated chunk of st not in F with its data keeps `ResultsAvoid`**, against
    the new memory μ′ and allocator state st′. -/
theorem ResultsAvoid.keep {μ μ' : Memory} {st st' : State} {rp : Nat} {rs : List Spec.Result} {F : List Nat}
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ F → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a)
    (h : ResultsAvoid μ st rp rs F) : ResultsAvoid μ' st' rp rs F :=
  ResultsAtP.mono (fun d hd => ⟨⟨(hk d hd.1 hd.2.1 hd.2.2).1, hd.2.1, hd.2.2⟩,
    (hk d hd.1 hd.2.1 hd.2.2).2⟩) h

end Services.Bootstrap.Acc.Handlers.Results
