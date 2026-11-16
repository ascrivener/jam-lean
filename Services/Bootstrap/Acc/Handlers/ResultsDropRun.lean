import Services.Bootstrap.Acc.Handlers.ResultsDrop
import Services.Bootstrap.Acc.Handlers.HeapKeep

/-!
# The results' drop (28864): the run

`drop_results`: from 28864 with ω₇ = v the results `Vec` (ptr rp at v + 8, len n at v + 16) owned as
`ResultsOwn` says, the drop returns to the caller with every buffer listed by `resPtrs` freed (the
allocator state is `(resPtrs μ₀ rp n).foldl free s₀`), every other allocated chunk kept with its data
(`Kept`), and the stack from the caller's sp up, the globals and the octets that are not writable kept
(`Frm`), ω₁, ω₅, ω₆ restored.

The proof: `Core FR` is what holds throughout with the buffers FR freed (the frame F = S − 56 holds
len, ptr and the saved ω₀, ω₅, ω₆); `Core.sk` (a write of the frame's scratch words), `Core.dk` (a call of
`dealloc` for the next listed buffer) and `Core.rd` (a read of an octet in a chunk that is not freed)
keep it. `dr_item` is one item (by tag), with the inner loop `dv_inner` for a `dataVec`; `dr_loop` the
outer loop.
-/

namespace Services.Bootstrap.Acc.Handlers.ResultsDrop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.DeallocCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- With the buffers FR freed, every other allocated chunk of s₀ is a chunk of s with its data kept
    against μ₀. -/
def Kept (s0 : State) (μ0 : Memory) (FR : List Nat) (μ : Memory) (s : State) : Prop :=
  ∀ d ∈ chunks s0, d.used = true → d.addr + 32 ∉ FR → d ∈ chunks s ∧ ∀ a, InData d a → μ.read a = μ0.read a

/-- The memory from B up, the globals and the octets that are not writable kept against μ₀, with the
    same access. -/
def Frm (μ0 : Memory) (B : Nat) (μ : Memory) : Prop :=
  (∀ a, a < 4294967296 → B ≤ a → μ.read a = μ0.read a) ∧ (∀ a, Glob a → μ.read a = μ0.read a) ∧
  (∀ b, b < two32 → μ0.writable b = false → μ.read b = μ0.read b) ∧
  (∀ a, μ.readable a = μ0.readable a) ∧ (∀ a, μ.writable a = μ0.writable a)

/-- An allocated chunk's data lies below 2³¹. -/
theorem data_lt {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {d : Chunk} (hd : d ∈ chunks s) {a : Nat} (ha : InData d a) :
    a < 2147483648 := by
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt d hd
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := H.hbT
  unfold InData at ha
  omega

/-- What holds throughout the drop, with the buffers FR freed: the context, `Kept`, `Frm` from the
    caller's sp S, the allocator state, ω₁ = F = S − 56 and the frame's len, ptr and saved registers. -/
structure Core (code : ByteArray) (pb S0 S1 : Nat) (s0 : State) (μ0 : Memory) (S rp n ret v5 v6 : Nat)
    (FR : List Nat) (ω : Regs) (μ : Memory) (s : State) : Prop where
  H : HeapCtxC code pb S0 S1 μ s
  K : Kept s0 μ0 FR μ s
  Fm : Frm μ0 S μ
  hs : s = FR.foldl free s0
  r1 : ω[1] = UInt64.ofNat (S - 56)
  mn : rdN μ (S - 56) 8 = n
  mp : rdN μ (S - 56 + 8) 8 = rp
  m0 : rdN μ (S - 56 + 48) 8 = ret
  m5 : rdN μ (S - 56 + 40) 8 = v5
  m6 : rdN μ (S - 56 + 32) 8 = v6

/-- The bounds on the caller's sp. -/
def SpOK (S0 S1 S : Nat) : Prop := 2147483716 + 56 ≤ S ∧ S0 + 96 ≤ S ∧ S ≤ S1

/-- **A write of the frame's scratch words** [F + 16, F + 32) keeps `Core`. -/
theorem Core.sk {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω ω' : Regs} {μ μ' : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (hS : SpOK S0 S1 S) (e1 : ω'[1] = ω[1])
    (fr : ∀ a, a < 4294967296 → (a < S - 56 + 16 ∨ S - 56 + 32 ≤ a) → μ'.read a = μ.read a)
    (rd : ∀ a, μ'.readable a = μ.readable a) (wr : ∀ a, μ'.writable a = μ.writable a) :
    Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω' μ' s := by
  obtain ⟨H, K, ⟨f1, f2, f3, f4, f5⟩, hs, r1, mn, mp, m0, m5, m6⟩ := C
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hT := H.hS1
  have hst := H.st
  refine ⟨HeapKeep.keepHi H (fun a ha => fr a (by omega) (.inl (by omega))) wr, fun d hd hu hn => ?_,
    ⟨fun a h1 h2 => (fr a h1 (.inr (by omega))).trans (f1 a h1 h2),
     fun a ha => (fr a (by unfold Glob at ha; omega) (.inl (by unfold Glob at ha; omega))).trans (f2 a ha),
     fun b hb hw => ?_, fun a => (rd a).trans (f4 a), fun a => (wr a).trans (f5 a)⟩,
    hs, e1.trans r1, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := K d hd hu hn
    exact ⟨h1, fun a ha => (fr a (by have := data_lt H h1 ha; omega)
      (.inl (by have := data_lt H h1 ha; omega))).trans (h2 a ha)⟩
  · unfold two32 at hb
    by_cases hin : S - 56 + 16 ≤ b ∧ b < S - 56 + 32
    · have := hst b (by omega) (by omega)
      rw [f5] at this; rw [this] at hw; exact absurd hw (by decide)
    · exact (fr b hb (by omega)).trans (f3 b (by unfold two32; omega) hw)
  all_goals first
    | (rw [← mn]; exact rdN_frame fun j hj => fr _ (by omega) (by omega))
    | (rw [← mp]; exact rdN_frame fun j hj => fr _ (by omega) (by omega))
    | (rw [← m0]; exact rdN_frame fun j hj => fr _ (by omega) (by omega))
    | (rw [← m5]; exact rdN_frame fun j hj => fr _ (by omega) (by omega))
    | (rw [← m6]; exact rdN_frame fun j hj => fr _ (by omega) (by omega))

/-- **A read in a chunk that is not freed**: the octet is μ₀'s, readable, below 2³¹. -/
theorem Core.rd {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) {b : Nat}
    (hb : ∃ d ∈ chunks s0, d.used = true ∧ InData d b ∧ d.addr + 32 ∉ FR) :
    μ.read b = μ0.read b ∧ μ.readable b = true ∧ b < 2147483648 := by
  obtain ⟨d, hd, hu, hi, hn⟩ := hb
  obtain ⟨h1, h2⟩ := C.K d hd hu hn
  exact ⟨h2 b hi, Memory.readable_of_writable (HeapKeep.writableData C.H h1 hu hi), data_lt C.H h1 hi⟩

/-- `Core.rd` for an 8-octet (or any m-octet) word. -/
theorem Core.rdW {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) {b m : Nat}
    (hb : ∀ j, j < m → ∃ d ∈ chunks s0, d.used = true ∧ InData d (b + j) ∧ d.addr + 32 ∉ FR) :
    rdN μ b m = rdN μ0 b m ∧ (∀ c, b ≤ c → c < b + m → μ.readable c = true) := by
  refine ⟨rdN_frame fun j hj => (C.rd (hb j hj)).1, fun c h1 h2 => ?_⟩
  have := (C.rd (hb (c - b) (by omega))).2.1
  rwa [show b + (c - b) = c by omega] at this

/-- **A call of `dealloc` (40613) for a buffer w that is not yet freed**, the data address of an
    allocated chunk of s₀, from ω₁ = F, returning to t: `Core (FR ++ [w])`, the frame kept, ω₀, ω₅, ω₆
    kept. -/
theorem Core.dk {p : ByteArray} {P : Program} [HasCode p P] {code : ByteArray} {pb S0 S1 : Nat}
    {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat} {FR : List Nat} (x : X) {ω : Regs} {μ : Memory}
    {s : State} (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (hS : SpOK S0 S1 S)
    (w r t : Nat) (hc : ∃ c ∈ chunks s0, c.used = true ∧ c.addr + 32 = w) (hw : w ∉ FR)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat w)
    (hret : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hjt : P.jumpTable.getD (r / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 249 ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (FR ++ [w]) ω' μ' (free s w) ∧
      (∀ a, a < 4294967296 → S - 56 ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨H, K, ⟨f1, f2, f3, f4, f5⟩, hs, r1, mn, mp, m0, m5, m6⟩ := C
  obtain ⟨hS1, hS2, hS3⟩ := hS
  obtain ⟨c, hc0, hcu, hca⟩ := hc
  have hT := H.hS1
  have hcs := (K c hc0 hcu (by rw [hca]; exact hw)).1
  obtain ⟨ω', μ', run, H', -, pg, ro, stk, gl, keep, e0, e1, e5, e6⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω μ s (S - 56) w r t c H hcs hcu hca h0 r1 h7
      hret hjt hbt (by omega) ⟨by omega, by omega⟩
  have rdeq : ∀ a, μ'.readable a = μ.readable a := fun a => by unfold Memory.readable; rw [pg]
  have wreq : ∀ a, μ'.writable a = μ.writable a := fun a => by unfold Memory.writable; rw [pg]
  refine ⟨ω', μ', run, ⟨H', fun d hd hu hn => ?_,
    ⟨fun a h1 h2 => (stk a h1 (by omega)).trans (f1 a h1 h2), fun a ha => (gl a ha).trans (f2 a ha),
     fun b hb hw' => (ro b hb (by rw [f5]; exact hw')).trans (f3 b hb hw'), fun a => (rdeq a).trans (f4 a),
     fun a => (wreq a).trans (f5 a)⟩,
    by rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hs], e1.trans r1, ?_, ?_, ?_, ?_, ?_⟩,
    fun a h1 h2 => stk a h1 h2, e0, e5, e6⟩
  · have hn' : d.addr + 32 ∉ FR := fun h => hn (List.mem_append_left _ h)
    have hdc : d ≠ c := by
      rintro rfl; exact hn (List.mem_append_right _ (by rw [hca]; exact List.mem_singleton_self _))
    obtain ⟨h1, h2⟩ := K d hd hu hn'
    obtain ⟨h3, h4⟩ := keep d h1 hu hdc
    exact ⟨h3, fun a ha => (h4 a ha).trans (h2 a ha)⟩
  all_goals first
    | (rw [← mn]; exact rdN_frame fun j hj => stk _ (by omega) (by omega))
    | (rw [← mp]; exact rdN_frame fun j hj => stk _ (by omega) (by omega))
    | (rw [← m0]; exact rdN_frame fun j hj => stk _ (by omega) (by omega))
    | (rw [← m5]; exact rdN_frame fun j hj => stk _ (by omega) (by omega))
    | (rw [← m6]; exact rdN_frame fun j hj => stk _ (by omega) (by omega))

theorem rdN_enc {μ : Memory} {b x : Nat} (h : μ.readN b 8 = Num.encodeLE 8 x) (hx : x < 2 ^ 64) :
    rdN μ b 8 = x := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt hx

theorem rdN_lt1 (μ : Memory) (b : Nat) : rdN μ b 1 < 256 := by
  have := Services.Bootstrap.Acc.Handlers.KeyEnc.decodeLE_readN_lt μ b 1
  unfold rdN; simpa using this

/-- The buffers of the first k items, then the item k's, then the rest. -/
theorem resPtrs_at (μ : Memory) (rp k n : Nat) (hk : k < n) :
    ∃ R, resPtrs μ rp n = resPtrs μ rp k ++ itemPtrs μ (rp + 144 * k) ++ R := by
  obtain ⟨R, hR⟩ := resPtrs_split μ rp (k + 1) n (by omega)
  exact ⟨R, by rw [hR, resPtrs_succ]⟩

theorem itemPtrs_data {μ : Memory} {a : Nat} (ht : rdN μ a 1 = 5) :
    itemPtrs μ a = if rdN μ (a + 8) 8 = 0 then [] else [rdN μ (a + 16) 8] := by
  unfold itemPtrs; rw [ht]; rfl

theorem itemPtrs_vec {μ : Memory} {a : Nat} (ht : 6 ≤ rdN μ a 1 ∧ rdN μ a 1 < 255) :
    itemPtrs μ a = innerPtrs μ (rdN μ (a + 16) 8) (rdN μ (a + 24) 8) ++
      (if rdN μ (a + 8) 8 = 0 then [] else [rdN μ (a + 16) 8]) := by
  unfold itemPtrs
  rw [if_neg (by omega), if_pos ht]

theorem itemPtrs_none {μ : Memory} {a : Nat} (ht : rdN μ a 1 = 255 ∨ rdN μ a 1 < 5) : itemPtrs μ a = [] := by
  unfold itemPtrs
  rw [if_neg (by omega), if_neg (by omega)]

/-- **A read of the item k's octets** [o, o + m) (m ≥ 1) while a prefix FR of `resPtrs` is freed. -/
theorem Core.item {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (O : ResultsOwn μ0 s0 rp n)
    (hFR : ∃ R, resPtrs μ0 rp n = FR ++ R) {k o m : Nat} (hk : k < n) (hom : o + m ≤ 144) (hm : 0 < m) :
    rdN μ (rp + 144 * k + o) m = rdN μ0 (rp + 144 * k + o) m ∧
    (∀ c, rp + 144 * k + o ≤ c → c < rp + 144 * k + o + m → μ.readable c = true) ∧
    rp + 144 * k + o + m ≤ 2147483648 := by
  have hb : ∀ j, j < m → ∃ d ∈ chunks s0, d.used = true ∧ InData d (rp + 144 * k + o + j) ∧
      d.addr + 32 ∉ FR := by
    intro j hj
    obtain ⟨R, hR⟩ := hFR
    obtain ⟨d, hd, hu, hi, hn⟩ := O.2.2.1 (144 * k + o + j) (by omega)
    rw [show rp + (144 * k + o + j) = rp + 144 * k + o + j by omega] at hi
    exact ⟨d, hd, hu, hi, fun h => hn (by rw [hR]; exact List.mem_append_left _ h)⟩
  obtain ⟨h1, h2⟩ := C.rdW hb
  have := (C.rd (hb (m - 1) (by omega))).2.2
  exact ⟨h1, h2, by omega⟩

/-- **A read of a chunk's data** d (d.addr + 32 = q) at [q + o, q + o + m) (m ≥ 1) while d is not freed. -/
theorem Core.inr {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) {d : Chunk} (hd : d ∈ chunks s0)
    (hu : d.used = true) {q : Nat} (hq : d.addr + 32 = q) (hn : q ∉ FR) {o m : Nat}
    (hom : q + o + m ≤ d.addr + 32 * d.size) (hm : 0 < m) :
    rdN μ (q + o) m = rdN μ0 (q + o) m ∧ (∀ c, q + o ≤ c → c < q + o + m → μ.readable c = true) ∧
    q + o + m ≤ 2147483648 := by
  have hb : ∀ j, j < m → ∃ d ∈ chunks s0, d.used = true ∧ InData d (q + o + j) ∧ d.addr + 32 ∉ FR :=
    fun j hj => ⟨d, hd, hu, ⟨by omega, by omega⟩, by rw [hq]; exact hn⟩
  obtain ⟨h1, h2⟩ := C.rdW hb
  have := (C.rd (hb (m - 1) (by omega))).2.2
  exact ⟨h1, h2, by omega⟩

/-- The stack's octets are readable and writable. -/
theorem Core.stk {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (hS : SpOK S0 S1 S) {lo hi : Nat}
    (hlo : S - 56 ≤ lo) (hhi : hi ≤ S) :
    (∀ a, lo ≤ a → a < hi → μ.readable a = true) ∧ (∀ a, lo ≤ a → a < hi → μ.writable a = true) := by
  obtain ⟨h1, h2, h3⟩ := hS
  exact ⟨fun a ha hb => Memory.readable_of_writable (C.H.st a (by omega) (by omega)),
    fun a ha hb => C.H.st a (by omega) (by omega)⟩

/-! ## The inner loop of a `dataVec` item -/

/-- The facts about the item k, a `dataVec` with inner array q, len L ≠ 0. -/
structure VecHyp (μ0 : Memory) (s0 : State) (rp n k q L : Nat) : Prop where
  hk : k < n
  ht : 6 ≤ rdN μ0 (rp + 144 * k) 1 ∧ rdN μ0 (rp + 144 * k) 1 < 255
  hq : rdN μ0 (rp + 144 * k + 16) 8 = q
  hL : rdN μ0 (rp + 144 * k + 24) 8 = L
  hL0 : L ≠ 0

theorem VecHyp.chunk {μ0 : Memory} {s0 : State} {rp n k q L : Nat} (V : VecHyp μ0 s0 rp n k q L)
    (O : ResultsOwn μ0 s0 rp n) :
    rdN μ0 (rp + 144 * k + 8) 8 ≠ 0 ∧ ∃ d ∈ chunks s0, d.used = true ∧ d.addr + 32 = q ∧
      q + 24 * L ≤ d.addr + 32 * d.size := by
  obtain ⟨hk, ht, hq, hL, hL0⟩ := V
  have := O.2.2.2 k hk ht.1 ht.2 (by rw [hL]; exact hL0)
  rw [hq, hL] at this
  exact this

/-- The item's buffers: the inner ones, then its array q. -/
theorem VecHyp.ptrs {μ0 : Memory} {s0 : State} {rp n k q L : Nat} (V : VecHyp μ0 s0 rp n k q L)
    (O : ResultsOwn μ0 s0 rp n) :
    itemPtrs μ0 (rp + 144 * k) = innerPtrs μ0 q L ++ [q] := by
  rw [itemPtrs_vec V.ht, V.hq, V.hL, if_neg (V.chunk O).1]

/-- The inner array's buffer q is not freed before the inner loop ends. -/
theorem VecHyp.q_notin {μ0 : Memory} {s0 : State} {rp n k q L : Nat} (V : VecHyp μ0 s0 rp n k q L)
    (O : ResultsOwn μ0 s0 rp n) {j : Nat} (hj : j ≤ L) : q ∉ resPtrs μ0 rp k ++ innerPtrs μ0 q j := by
  obtain ⟨R, hR⟩ := resPtrs_at μ0 rp k n V.hk
  obtain ⟨R', hR'⟩ := innerPtrs_split μ0 q j L hj
  rw [V.ptrs O, hR'] at hR
  have h : (resPtrs μ0 rp k ++ innerPtrs μ0 q j ++ R' ++ q :: R).Nodup := by
    have := O.1; rw [hR] at this; simpa [List.append_assoc] using this
  have := nodup_next h
  exact fun hx => this (List.mem_append_left _ hx)

/-- The inner loop's invariant at 29014, for the j-th inner `Vec`. -/
structure InInv (code : ByteArray) (pb S0 S1 : Nat) (s0 : State) (μ0 : Memory) (S rp n ret v5 v6 k q L j : Nat)
    (ω : Regs) (μ : Memory) (s : State) : Prop where
  C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q j) ω μ s
  r5 : ω[5] = UInt64.ofNat (q + 8 + 24 * j)
  r6 : ω[6] = UInt64.ofNat k
  ma : rdN μ (S - 56 + 16) 8 = rp + 144 * k
  me : rdN μ (S - 56 + 24) 8 = q + 8 + 24 * L

/-- `Core` depends on the registers only through ω₁. -/
theorem Core.reg {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat}
    {FR : List Nat} {ω ω' : Regs} {μ : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (e1 : ω'[1] = ω[1]) :
    Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω' μ s :=
  { C with r1 := e1.trans C.r1 }

/-- The inner array's end lies below 2³¹. -/
theorem VecHyp.bound {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory}
    {S rp n ret v5 v6 k q L : Nat} {ω : Regs} {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n)
    (V : VecHyp μ0 s0 rp n k q L) {j : Nat} (hj : j ≤ L)
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q j) ω μ s) :
    q + 24 * L ≤ 2147483648 := by
  obtain ⟨-, d, hd, hu, hdq, hdL⟩ := V.chunk O
  have hL0 := V.hL0
  have := (C.inr hd hu hdq (V.q_notin O hj) (o := 24 * (L - 1)) (m := 24) (by omega) (by omega)).2.2
  omega

/-- **One inner `Vec`** (29014 → 29004): freed if its cap is not 0. -/
theorem dv_cell {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k q L j : Nat} (x : X) {ω : Regs}
    {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (V : VecHyp μ0 s0 rp n k q L)
    (I : InInv code pb S0 S1 s0 μ0 S rp n ret v5 v6 k q L j ω μ s) (hj : j < L) :
    ∃ ω' μ' s' N, FreeStepsH p R 29014 ω μ x 29004 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q (j + 1)) ω' μ' s' ∧
      ω'[5] = UInt64.ofNat (q + 8 + 24 * j) ∧ ω'[6] = UInt64.ofNat k ∧
      rdN μ' (S - 56 + 16) 8 = rp + 144 * k ∧ rdN μ' (S - 56 + 24) 8 = q + 8 + 24 * L := by
  obtain ⟨C, r5, r6, ma, me⟩ := I
  have hT := C.H.hS1
  have hS3 := hS.2.2
  have hS1' := hS.1
  obtain ⟨-, d, hd, hu, hdq, hdL⟩ := V.chunk O
  have hn := V.q_notin O (j := j) (by omega)
  obtain ⟨c1, c2, c3⟩ := C.inr hd hu hdq hn (o := 24 * j) (m := 8) (by omega) (by omega)
  obtain ⟨d1, d2, d3⟩ := C.inr hd hu hdq hn (o := 24 * j + 8) (m := 8) (by omega) (by omega)
  have e8 : q + 8 + 24 * j - 8 = q + 24 * j := by omega
  have e8' : q + 8 + 24 * j = q + (24 * j + 8) := by omega
  have hq8 : 8 ≤ q + 8 + 24 * j ∧ q + 8 + 24 * j + 8 < 4294967296 := by omega
  have hra : ∀ b, q + 8 + 24 * j - 8 ≤ b → b < q + 8 + 24 * j + 8 → μ.readable b = true := fun b h1 h2 => by
    rcases Nat.lt_or_ge b (q + 24 * j + 8) with h | h
    · exact c2 b (by omega) (by omega)
    · exact d2 b (by omega) (by omega)
  have hsucc := innerPtrs_succ μ0 q j
  by_cases hc : rdN μ0 (q + 24 * j) 8 = 0
  · obtain ⟨ω1, run1, a1, a5, a6⟩ := dv_in0 (R := R) (P := P) x ω μ (q + 8 + 24 * j) r5 hq8
      (by rw [e8, c1, hc]) (fun b h1 h2 => hra b h1 (by omega))
    refine ⟨ω1, μ, s, 3, run1, ?_, a5.trans r5, a6.trans r6, ma, me⟩
    rw [hsucc, if_pos hc, List.append_nil]
    exact C.reg a1
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := dv_in1 (R := R) (P := P) x ω μ (q + 8 + 24 * j)
      (rdN μ0 (q + 24 * j) 8) (rdN μ0 (q + 24 * j + 8) 8) r5 hq8 (by rw [e8, c1]) hc
      (by rw [e8', d1, Nat.add_assoc]) hra
    obtain ⟨R', hR'⟩ := innerPtrs_split μ0 q (j + 1) L (by omega)
    rw [hsucc, if_neg hc] at hR'
    obtain ⟨R0, hR⟩ := resPtrs_at μ0 rp k n V.hk
    rw [V.ptrs O, hR'] at hR
    have hnd : (resPtrs μ0 rp k ++ innerPtrs μ0 q j ++ rdN μ0 (q + 24 * j + 8) 8 :: (R' ++ q :: R0)).Nodup := by
      have := O.1; rw [hR] at this; simpa [List.append_assoc] using this
    have hwn := nodup_next hnd
    have hwmem : rdN μ0 (q + 24 * j + 8) 8 ∈ resPtrs μ0 rp n := by rw [hR]; simp
    obtain ⟨cc, hcc, hccu, hcca⟩ := O.2.1 _ hwmem
    obtain ⟨ω2, μ2, run2, C2, fr2, b0, b5, b6⟩ := Core.dk (R := R) (P := P) x (C.reg a1) hS _ 1352 29032
      ⟨cc, hcc, hccu, hcca⟩ hwn a0 a7 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_675]) bs_29032
    refine ⟨ω2, μ2, free s (rdN μ0 (q + 24 * j + 8) 8), _, (run1.trans run2).trans (dv_back (R := R) (P := P) x ω2 μ2), ?_, b5.trans (a5.trans r5),
      b6.trans (a6.trans r6), ?_, ?_⟩
    · rw [hsucc, if_neg hc, ← List.append_assoc]; exact C2
    · rw [← ma]; exact rdN_frame fun i hi => fr2 _ (by omega) (by omega)
    · rw [← me]; exact rdN_frame fun i hi => fr2 _ (by omega) (by omega)

/-- **The inner loop** (29014 → 29034): every inner buffer with cap ≠ 0 freed. -/
theorem dv_inner {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k q L : Nat} (x : X)
    (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (V : VecHyp μ0 s0 rp n k q L) :
    ∀ j ω μ s, j < L → InInv code pb S0 S1 s0 μ0 S rp n ret v5 v6 k q L j ω μ s →
    ∃ ω' μ' s' N, FreeStepsH p R 29014 ω μ x 29034 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q L) ω' μ' s' ∧
      ω'[6] = UInt64.ofNat k ∧ rdN μ' (S - 56 + 16) 8 = rp + 144 * k := by
  suffices h : ∀ m j ω μ s, L - (j + 1) = m → j < L → InInv code pb S0 S1 s0 μ0 S rp n ret v5 v6 k q L j ω μ s →
      ∃ ω' μ' s' N, FreeStepsH p R 29014 ω μ x 29034 ω' μ' x N ∧
        Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q L) ω' μ' s' ∧
        ω'[6] = UInt64.ofNat k ∧ rdN μ' (S - 56 + 16) 8 = rp + 144 * k from
    fun j ω μ s hj I => h _ j ω μ s rfl hj I
  have hS3 := hS.2.2
  have hS1' := hS.1
  intro m
  induction m with
  | zero =>
    intro j ω μ s hm hj I
    obtain ⟨ω1, μ1, s1, N1, run1, C1, a5, a6, ma1, me1⟩ := dv_cell (R := R) (P := P) x O hS V I hj
    have hT := C1.H.hS1
    have hb := V.bound O (Nat.le_refl _) (by have := C1; exact (show j + 1 = L by omega) ▸ this)
    have hjL : j + 1 = L := by omega
    obtain ⟨ω2, run2, b1, b6⟩ := dv_step0 (R := R) (P := P) x ω1 μ1 (S - 56) (q + 8 + 24 * j)
      (q + 8 + 24 * L) C1.r1 a5 (by omega) (by omega) me1 (by omega)
      (C1.stk hS (lo := S - 56 + 24) (hi := S - 56 + 32) (by omega) (by omega)).1
    rw [hjL] at C1
    exact ⟨ω2, μ1, s1, _, run1.trans run2, C1.reg b1, b6.trans a6, ma1⟩
  | succ m ih =>
    intro j ω μ s hm hj I
    obtain ⟨ω1, μ1, s1, N1, run1, C1, a5, a6, ma1, me1⟩ := dv_cell (R := R) (P := P) x O hS V I hj
    have hT := C1.H.hS1
    have hb := V.bound O (by omega) C1
    obtain ⟨ω2, run2, b1, b5, b6⟩ := dv_step1 (R := R) (P := P) x ω1 μ1 (S - 56) (q + 8 + 24 * j)
      (q + 8 + 24 * L) C1.r1 a5 (by omega) (by omega) me1 (by omega)
      (C1.stk hS (lo := S - 56 + 24) (hi := S - 56 + 32) (by omega) (by omega)).1
    have I2 : InInv code pb S0 S1 s0 μ0 S rp n ret v5 v6 k q L (j + 1) ω2 μ1 s1 :=
      ⟨C1.reg b1, by rw [b5]; congr 1; try omega, b6.trans a6, ma1, me1⟩
    obtain ⟨ω3, μ3, s3, N3, run3, rest⟩ := ih (j + 1) ω2 μ1 s1 (by omega) (by omega) I2
    exact ⟨ω3, μ3, s3, _, (run1.trans run2).trans run3, rest⟩

/-! ## One item -/

/-- **The end of a `dataVec` item** (29034 → 28922): its array freed if its cap is not 0. -/
theorem dv_out {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k q L : Nat} (x : X) {ω : Regs}
    {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (hk : k < n)
    (ht : 6 ≤ rdN μ0 (rp + 144 * k) 1 ∧ rdN μ0 (rp + 144 * k) 1 < 255)
    (hq : rdN μ0 (rp + 144 * k + 16) 8 = q) (hL : rdN μ0 (rp + 144 * k + 24) 8 = L)
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k ++ innerPtrs μ0 q L) ω μ s)
    (r6 : ω[6] = UInt64.ofNat k) (ma : rdN μ (S - 56 + 16) 8 = rp + 144 * k) :
    ∃ ω' μ' s' N, FreeStepsH p R 29034 ω μ x 28922 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp (k + 1)) ω' μ' s' ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat k := by
  have hT := C.H.hS1
  have hS3 := hS.2.2
  have hS1' := hS.1
  have hip := itemPtrs_vec ht
  rw [hq, hL] at hip
  obtain ⟨R0, hR⟩ := resPtrs_at μ0 rp k n hk
  rw [hip] at hR
  have hFR : ∃ R', resPtrs μ0 rp n = (resPtrs μ0 rp k ++ innerPtrs μ0 q L) ++ R' :=
    ⟨(if rdN μ0 (rp + 144 * k + 8) 8 = 0 then [] else [q]) ++ R0, by rw [hR]; simp only [List.append_assoc]⟩
  obtain ⟨i1, j1, -⟩ := C.item O hFR (o := 8) (m := 8) hk (by omega) (by omega)
  obtain ⟨i2, j2, k2⟩ := C.item O hFR (o := 16) (m := 8) hk (by omega) (by omega)
  have hra : ∀ b, rp + 144 * k + 8 ≤ b → b < rp + 144 * k + 24 → μ.readable b = true := fun b h1 h2 => by
    rcases Nat.lt_or_ge b (rp + 144 * k + 16) with h | h
    · exact j1 b (by omega) (by omega)
    · exact j2 b (by omega) (by omega)
  obtain ⟨sr, -⟩ := C.stk hS (lo := S - 56) (hi := S - 56 + 24) (by omega) (by omega)
  by_cases hc : rdN μ0 (rp + 144 * k + 8) 8 = 0
  · obtain ⟨ω1, run1, a1, a5, a6⟩ := dv_out0 (R := R) (P := P) x ω μ (S - 56) (rp + 144 * k) n C.r1
      (by omega) (by omega) ma (by rw [i1, hc]) C.mn sr (fun b h1 h2 => hra b h1 (by omega))
    refine ⟨ω1, μ, s, _, run1, ?_, a5, a6.trans r6⟩
    rw [resPtrs_succ, hip, if_pos hc, List.append_nil]
    exact C.reg a1
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := dv_out1 (R := R) (P := P) x ω μ (S - 56) (rp + 144 * k) n
      (rdN μ0 (rp + 144 * k + 8) 8) q C.r1 (by omega) (by omega) ma (by rw [i1]) hc (by rw [i2, hq]) C.mn sr hra
    rw [if_neg hc] at hR
    have hnd : (resPtrs μ0 rp k ++ innerPtrs μ0 q L ++ q :: R0).Nodup := by
      have := O.1; rw [hR] at this; simpa [List.append_assoc] using this
    have hqm : q ∈ resPtrs μ0 rp n := by rw [hR]; simp
    obtain ⟨cc, hcc, hccu, hcca⟩ := O.2.1 _ hqm
    obtain ⟨ω2, μ2, run2, C2, -, b0, b5, b6⟩ := Core.dk (R := R) (P := P) x (C.reg a1) hS q 1350 28922
      ⟨cc, hcc, hccu, hcca⟩ (nodup_next hnd) a0 a7 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_674]) bs_28922
    refine ⟨ω2, μ2, free s q, _, run1.trans run2, ?_, b5.trans a5, b6.trans (a6.trans r6)⟩
    rw [resPtrs_succ, hip, if_neg hc, ← List.append_assoc]
    exact C2

/-- **A `data` item** (28896 → 28922): its buffer freed if its cap is not 0. -/
theorem dr_data {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k : Nat} (x : X) {ω : Regs}
    {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (hk : k < n)
    (ht : rdN μ0 (rp + 144 * k) 1 = 5)
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k) ω μ s)
    (r5 : ω[5] = UInt64.ofNat n) (r6 : ω[6] = UInt64.ofNat k) (ma : rdN μ (S - 56 + 16) 8 = rp + 144 * k) :
    ∃ ω' μ' s' N, FreeStepsH p R 28896 ω μ x 28922 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp (k + 1)) ω' μ' s' ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat k := by
  have hT := C.H.hS1
  have hS3 := hS.2.2
  have hS1' := hS.1
  have hip := itemPtrs_data ht
  obtain ⟨R0, hR⟩ := resPtrs_at μ0 rp k n hk
  have hFR : ∃ R', resPtrs μ0 rp n = resPtrs μ0 rp k ++ R' :=
    ⟨itemPtrs μ0 (rp + 144 * k) ++ R0, by rw [hR, List.append_assoc]⟩
  rw [hip] at hR
  obtain ⟨i1, j1, -⟩ := C.item O hFR (o := 8) (m := 8) hk (by omega) (by omega)
  obtain ⟨i2, j2, k2⟩ := C.item O hFR (o := 16) (m := 8) hk (by omega) (by omega)
  have hra : ∀ b, rp + 144 * k + 8 ≤ b → b < rp + 144 * k + 24 → μ.readable b = true := fun b h1 h2 => by
    rcases Nat.lt_or_ge b (rp + 144 * k + 16) with h | h
    · exact j1 b (by omega) (by omega)
    · exact j2 b (by omega) (by omega)
  obtain ⟨sr, -⟩ := C.stk hS (lo := S - 56 + 16) (hi := S - 56 + 24) (by omega) (by omega)
  by_cases hc : rdN μ0 (rp + 144 * k + 8) 8 = 0
  · obtain ⟨ω1, run1, a1, a5, a6⟩ := dr_data0 (R := R) (P := P) x ω μ (S - 56) (rp + 144 * k) C.r1
      (by omega) (by omega) ma (by rw [i1, hc]) sr (fun b h1 h2 => hra b h1 (by omega))
    refine ⟨ω1, μ, s, _, run1, ?_, a5.trans r5, a6.trans r6⟩
    rw [resPtrs_succ, hip, if_pos hc, List.append_nil]
    exact C.reg a1
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := dr_data1 (R := R) (P := P) x ω μ (S - 56) (rp + 144 * k)
      (rdN μ0 (rp + 144 * k + 8) 8) (rdN μ0 (rp + 144 * k + 16) 8) C.r1 (by omega) (by omega) ma
      (by rw [i1]) hc (by rw [i2]) sr hra
    rw [if_neg hc] at hR
    have hnd : (resPtrs μ0 rp k ++ rdN μ0 (rp + 144 * k + 16) 8 :: R0).Nodup := by
      have := O.1; rw [hR] at this; simpa [List.append_assoc] using this
    have hqm : rdN μ0 (rp + 144 * k + 16) 8 ∈ resPtrs μ0 rp n := by rw [hR]; simp
    obtain ⟨cc, hcc, hccu, hcca⟩ := O.2.1 _ hqm
    obtain ⟨ω2, μ2, run2, C2, -, b0, b5, b6⟩ := Core.dk (R := R) (P := P) x (C.reg a1) hS _ 1350 28922
      ⟨cc, hcc, hccu, hcca⟩ (nodup_next hnd) a0 a7 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_674]) bs_28922
    refine ⟨ω2, μ2, free s (rdN μ0 (rp + 144 * k + 16) 8), _, run1.trans run2, ?_, b5.trans (a5.trans r5), b6.trans (a6.trans r6)⟩
    rw [resPtrs_succ, hip, if_neg hc]
    exact C2

/-- **A `dataVec` item** (28967 → 28922): its inner buffers, then its array, freed. -/
theorem dr_vec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k : Nat} (x : X) {ω : Regs}
    {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (hk : k < n)
    (ht : 6 ≤ rdN μ0 (rp + 144 * k) 1 ∧ rdN μ0 (rp + 144 * k) 1 < 255)
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k) ω μ s)
    (r6 : ω[6] = UInt64.ofNat k) (ma : rdN μ (S - 56 + 16) 8 = rp + 144 * k) :
    ∃ ω' μ' s' N, FreeStepsH p R 28967 ω μ x 28922 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp (k + 1)) ω' μ' s' ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat k := by
  have hT := C.H.hS1
  have hS3 := hS.2.2
  have hS1' := hS.1
  obtain ⟨R0, hR⟩ := resPtrs_at μ0 rp k n hk
  have hFR : ∃ R', resPtrs μ0 rp n = resPtrs μ0 rp k ++ R' :=
    ⟨itemPtrs μ0 (rp + 144 * k) ++ R0, by rw [hR, List.append_assoc]⟩
  obtain ⟨i2, j2, -⟩ := C.item O hFR (o := 16) (m := 8) hk (by omega) (by omega)
  obtain ⟨i3, j3, k3⟩ := C.item O hFR (o := 24) (m := 8) hk (by omega) (by omega)
  have hra : ∀ b, rp + 144 * k + 16 ≤ b → b < rp + 144 * k + 32 → μ.readable b = true := fun b h1 h2 => by
    rcases Nat.lt_or_ge b (rp + 144 * k + 24) with h | h
    · exact j2 b (by omega) (by omega)
    · exact j3 b (by omega) (by omega)
  obtain ⟨sr, sw⟩ := C.stk hS (lo := S - 56 + 16) (hi := S - 56 + 32) (by omega) (by omega)
  have e0 : ∀ q, innerPtrs μ0 q 0 = [] := fun q => by simp [innerPtrs]
  by_cases hL : rdN μ0 (rp + 144 * k + 24) 8 = 0
  · obtain ⟨ω1, run1, a1, a6⟩ := dv_pre0 (R := R) (P := P) x ω μ (S - 56) (rp + 144 * k) C.r1
      (by omega) (by omega) ma (by rw [i3, hL]) (fun b h1 h2 => sr b h1 (by omega))
      (fun b h1 h2 => hra b (by omega) h2)
    have C1 : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6
        (resPtrs μ0 rp k ++ innerPtrs μ0 (rdN μ0 (rp + 144 * k + 16) 8) (rdN μ0 (rp + 144 * k + 24) 8))
        ω1 μ s := by
      rw [hL, e0, List.append_nil]; exact C.reg a1
    obtain ⟨ω2, μ2, s2, N2, run2, rest⟩ := dv_out (R := R) (P := P) x O hS hk ht rfl rfl C1 (a6.trans r6) ma
    exact ⟨ω2, μ2, s2, _, run1.trans run2, rest⟩
  · have V : VecHyp μ0 s0 rp n k (rdN μ0 (rp + 144 * k + 16) 8) (rdN μ0 (rp + 144 * k + 24) 8) :=
      ⟨hk, ht, rfl, rfl, hL⟩
    have C0 : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6
        (resPtrs μ0 rp k ++ innerPtrs μ0 (rdN μ0 (rp + 144 * k + 16) 8) 0) ω μ s := by
      rw [e0, List.append_nil]; exact C
    have hb := V.bound O (Nat.zero_le _) C0
    obtain ⟨ω1, μ1, run1, a1, a5, a6, w24, fr1, rd1, wr1⟩ := dv_pre1 (R := R) (P := P) x ω μ (S - 56)
      (rp + 144 * k) (rdN μ0 (rp + 144 * k + 16) 8) (rdN μ0 (rp + 144 * k + 24) 8) C.r1 (by omega)
      (by omega) (by omega) (.inl (by omega)) ma (by rw [i2]) (by rw [i3]) hL
      (fun b h1 h2 => sr b h1 (by omega)) hra (fun b h1 h2 => sw b (by omega) h2)
    have C1 := C0.sk hS a1 (fun a h1 h2 => fr1 a h1 (by omega)) rd1 wr1
    have I0 : InInv code pb S0 S1 s0 μ0 S rp n ret v5 v6 k (rdN μ0 (rp + 144 * k + 16) 8)
        (rdN μ0 (rp + 144 * k + 24) 8) 0 ω1 μ1 s :=
      ⟨C1, by rw [a5]; try (congr 1; omega), a6.trans r6,
        by rw [← ma]; exact rdN_frame fun i hi => fr1 _ (by omega) (by omega),
        rdN_enc w24 (by omega)⟩
    obtain ⟨ω2, μ2, s2, N2, run2, C2, b6, mb⟩ := dv_inner (R := R) (P := P) x O hS V 0 ω1 μ1 s (by omega) I0
    obtain ⟨ω3, μ3, s3, N3, run3, rest⟩ := dv_out (R := R) (P := P) x O hS hk ht rfl rfl C2 b6 mb
    exact ⟨ω3, μ3, s3, _, (run1.trans run2).trans run3, rest⟩

/-- The loop head's frame write (F + 16) keeps `Core`; the item's address is at F + 16. -/
theorem head_core {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k : Nat}
    {FR : List Nat} {ω ω' : Regs} {μ μ' : Memory} {s : State}
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω μ s) (hS : SpOK S0 S1 S)
    (ha : rp + 144 * k < 2 ^ 64) (hp : HeadPost ω μ (S - 56) rp k ω' μ') :
    Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 FR ω' μ' s ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (S - 56 + 16) 8 = rp + 144 * k := by
  obtain ⟨e1, e5, e6, m16, fr, rd, wr⟩ := hp
  exact ⟨C.sk hS e1 (fun a h1 h2 => fr a h1 (by omega)) rd wr, e5, e6, rdN_enc m16 ha⟩

/-- **One item** (28929 → 28922), by its tag. -/
theorem dr_item {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 k : Nat} (x : X) {ω : Regs}
    {μ : Memory} {s : State} (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) (hk : k < n)
    (C : Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k) ω μ s)
    (r5 : ω[5] = UInt64.ofNat n) (r6 : ω[6] = UInt64.ofNat k) :
    ∃ ω' μ' s' N, FreeStepsH p R 28929 ω μ x 28922 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp (k + 1)) ω' μ' s' ∧
      ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat k := by
  have hT := C.H.hS1
  have hS3 := hS.2.2
  have hS1' := hS.1
  have hS1 := hS.1
  obtain ⟨R0, hR⟩ := resPtrs_at μ0 rp k n hk
  have hFR : ∃ R', resPtrs μ0 rp n = resPtrs μ0 rp k ++ R' :=
    ⟨itemPtrs μ0 (rp + 144 * k) ++ R0, by rw [hR, List.append_assoc]⟩
  obtain ⟨i0, j0, k0⟩ := C.item O hFR (o := 0) (m := 1) hk (by omega) (by omega)
  simp only [Nat.add_zero] at i0 j0 k0
  obtain ⟨sr, sw⟩ := C.stk hS (lo := S - 56) (hi := S - 56 + 24) (by omega) (by omega)
  have HH : HeadHyp ω μ (S - 56) rp k (rdN μ0 (rp + 144 * k) 1) :=
    ⟨C.r1, r6, by omega, by omega, .inl (by omega), C.mp, i0, fun a h1 h2 => sr a (by omega) (by omega),
      j0 _ (by omega) (by omega), fun a h1 h2 => sw a (by omega) h2⟩
  have ha : rp + 144 * k < 2 ^ 64 := by omega
  have hnone : ∀ ω' μ', rdN μ0 (rp + 144 * k) 1 = 255 ∨ rdN μ0 (rp + 144 * k) 1 < 5 →
      HeadPost ω μ (S - 56) rp k ω' μ' →
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp (k + 1)) ω' μ' s ∧
        ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat k := fun ω' μ' ht hp => by
    obtain ⟨C1, e5, e6, -⟩ := head_core C hS ha hp
    rw [resPtrs_succ, itemPtrs_none ht, List.append_nil]
    exact ⟨C1, e5.trans r5, e6.trans r6⟩
  have ht256 := rdN_lt1 μ0 (rp + 144 * k)
  by_cases h255 : rdN μ0 (rp + 144 * k) 1 = 255
  · obtain ⟨ω1, μ1, run1, hp⟩ := dr_err (R := R) (P := P) x ω μ (S - 56) rp k (h255 ▸ HH)
    exact ⟨ω1, μ1, s, _, run1, hnone ω1 μ1 (.inl h255) hp⟩
  by_cases h5 : rdN μ0 (rp + 144 * k) 1 < 5
  · obtain ⟨ω1, μ1, run1, hp⟩ := dr_small (R := R) (P := P) x ω μ (S - 56) rp k _ HH h5
    exact ⟨ω1, μ1, s, _, run1, hnone ω1 μ1 (.inr h5) hp⟩
  by_cases hd5 : rdN μ0 (rp + 144 * k) 1 = 5
  · obtain ⟨ω1, μ1, run1, hp⟩ := dr_isdata (R := R) (P := P) x ω μ (S - 56) rp k (hd5 ▸ HH)
    obtain ⟨C1, e5, e6, ma⟩ := head_core C hS ha hp
    obtain ⟨ω2, μ2, s2, N2, run2, rest⟩ :=
      dr_data (R := R) (P := P) x O hS hk hd5 C1 (e5.trans r5) (e6.trans r6) ma
    exact ⟨ω2, μ2, s2, _, run1.trans run2, rest⟩
  · have ht : 6 ≤ rdN μ0 (rp + 144 * k) 1 ∧ rdN μ0 (rp + 144 * k) 1 < 255 := by omega
    obtain ⟨ω1, μ1, run1, hp⟩ := dr_isvec (R := R) (P := P) x ω μ (S - 56) rp k _ HH ht
    obtain ⟨C1, e5, e6, ma⟩ := head_core C hS ha hp
    obtain ⟨ω2, μ2, s2, N2, run2, rest⟩ := dr_vec (R := R) (P := P) x O hS hk ht C1 (e6.trans r6) ma
    exact ⟨ω2, μ2, s2, _, run1.trans run2, rest⟩

/-- **The items loop** (28929 → 29072): the items k … n − 1 dropped. -/
theorem dr_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {s0 : State} {μ0 : Memory} {S rp n ret v5 v6 : Nat} (x : X)
    (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S) :
    ∀ k ω μ s, k < n → Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k) ω μ s →
    ω[5] = UInt64.ofNat n → ω[6] = UInt64.ofNat k →
    ∃ ω' μ' s' N, FreeStepsH p R 28929 ω μ x 29072 ω' μ' x N ∧
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp n) ω' μ' s' := by
  suffices h : ∀ m k ω μ s, n - (k + 1) = m → k < n →
      Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp k) ω μ s →
      ω[5] = UInt64.ofNat n → ω[6] = UInt64.ofNat k →
      ∃ ω' μ' s' N, FreeStepsH p R 28929 ω μ x 29072 ω' μ' x N ∧
        Core code pb S0 S1 s0 μ0 S rp n ret v5 v6 (resPtrs μ0 rp n) ω' μ' s' from
    fun k ω μ s hk C r5 r6 => h _ k ω μ s rfl hk C r5 r6
  intro m
  induction m with
  | zero =>
    intro k ω μ s hm hk C r5 r6
    obtain ⟨ω1, μ1, s1, N1, run1, C1, a5, a6⟩ := dr_item (R := R) (P := P) x O hS hk C r5 r6
    have hl : n < 2 ^ 64 := C.mn ▸ rdN_lt8 μ (S - 56)
    obtain ⟨ω2, run2, b1, -, -⟩ := dr_next0 (R := R) (P := P) x ω1 μ1 k n a5 a6 hl (by omega)
    rw [show k + 1 = n by omega] at C1
    exact ⟨ω2, μ1, s1, _, run1.trans run2, C1.reg b1⟩
  | succ m ih =>
    intro k ω μ s hm hk C r5 r6
    obtain ⟨ω1, μ1, s1, N1, run1, C1, a5, a6⟩ := dr_item (R := R) (P := P) x O hS hk C r5 r6
    have hl : n < 2 ^ 64 := C.mn ▸ rdN_lt8 μ (S - 56)
    obtain ⟨ω2, run2, b1, b5, b6⟩ := dr_next1 (R := R) (P := P) x ω1 μ1 k n a5 a6 hl (by omega)
    obtain ⟨ω3, μ3, s3, N3, run3, C3⟩ :=
      ih (k + 1) ω2 μ1 s1 (by omega) (by omega) (C1.reg b1) (b5.trans a5) b6
    exact ⟨ω3, μ3, s3, _, (run1.trans run2).trans run3, C3⟩

/-- The frame's first writes (in [F, S)) keep the context, `Kept []` and `Frm`. -/
theorem init3 {code : ByteArray} {pb S0 S1 : Nat} {s0 : State} {μ0 μ : Memory} {S : Nat}
    (H : HeapCtxC code pb S0 S1 μ0 s0) (hS : SpOK S0 S1 S)
    (fr : ∀ a, a < 4294967296 → (a < S - 56 ∨ S ≤ a) → μ.read a = μ0.read a)
    (rd : ∀ a, μ.readable a = μ0.readable a) (wr : ∀ a, μ.writable a = μ0.writable a) :
    HeapCtxC code pb S0 S1 μ s0 ∧ Kept s0 μ0 [] μ s0 ∧ Frm μ0 S μ := by
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hT := H.hS1
  refine ⟨HeapKeep.keepHi H (fun a ha => fr a (by omega) (.inl (by omega))) wr,
    fun d hd hu _ => ⟨hd, fun a ha => fr a (by have := data_lt H hd ha; omega)
      (.inl (by have := data_lt H hd ha; omega))⟩,
    fun a h1 h2 => fr a h1 (.inr h2),
    fun a ha => fr a (by unfold Glob at ha; omega) (.inl (by unfold Glob at ha; omega)),
    fun b hb hw => ?_, rd, wr⟩
  unfold two32 at hb
  by_cases hin : S - 56 ≤ b ∧ b < S
  · rw [H.st b (by omega) (by omega)] at hw; exact absurd hw (by decide)
  · exact fr b hb (by omega)

/-- **The results' drop (28864), any n**: from ω₇ = v the results `Vec` (ptr rp at v + 8, len n at
    v + 16, owned as `ResultsOwn` says, against the allocator's context) and a return address ω₀ that
    `djump` resolves to t, the drop returns to t with every buffer listed by `resPtrs` freed (allocator
    state `(resPtrs μ₀ rp n).foldl free s₀`), every other allocated chunk kept with its data (`Kept`),
    the memory from the caller's sp S up, the globals and the octets that are not writable kept with
    the same access (`Frm`), and ω₁ = S, ω₅, ω₆ restored. -/
theorem drop_results {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} (x : X) (ω : Regs) (μ0 : Memory) (s0 : State) (S v rp n ret t : Nat)
    (H : HeapCtxC code pb S0 S1 μ0 s0) (O : ResultsOwn μ0 s0 rp n) (hS : SpOK S0 S1 S)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat v)
    (hv : v + 24 < 4294967296) (hd : v + 24 ≤ S - 56 ∨ S ≤ v)
    (mp : rdN μ0 (v + 8) 8 = rp) (ml : rdN μ0 (v + 16) 8 = n)
    (hr : ∀ a, v + 8 ≤ a → a < v + 24 → μ0.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ' N, FreeStepsH p R 28864 ω μ0 x t ω' μ' x N ∧
      HeapCtxC code pb S0 S1 μ' ((resPtrs μ0 rp n).foldl free s0) ∧
      Kept s0 μ0 (resPtrs μ0 rp n) μ' ((resPtrs μ0 rp n).foldl free s0) ∧ Frm μ0 S μ' ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hT := H.hS1
  obtain ⟨hS1, hS2, hS3⟩ := hS
  have hw : ∀ a, S - 56 ≤ a → a < S → μ0.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have e0 : ω[0].toNat = ret := by rw [h0]; simp [Nat.mod_eq_of_lt (show ret < 2 ^ 64 by omega)]
  have l0 := UInt64.toNat_lt ω[0]
  have l5 := UInt64.toNat_lt ω[5]
  have l6 := UInt64.toNat_lt ω[6]
  have hr' : ∀ a, v + 16 ≤ a → a < v + 24 → μ0.readable a = true := fun a h1 h2 => hr a (by omega) h2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    obtain ⟨ω1, μ1, run1, a1, w0, w5, w6, fr1, rd1, wr1⟩ :=
      dr_pre0 (R := R) (P := P) x ω μ0 S v h1 h7 ⟨by omega, by omega⟩ hv hd ml hr' hw
    obtain ⟨H1, K1, F1⟩ := init3 H ⟨hS1, hS2, hS3⟩ fr1 rd1 wr1
    obtain ⟨ω2, run2, b1, b5, b6⟩ := dr_end (R := R) (P := P) x ω1 μ1 (S - 56) ret ω[5].toNat ω[6].toNat t a1
      ⟨by omega, by omega⟩ (by rw [rdN_enc w0 l0, e0]) (rdN_enc w5 l5) (rdN_enc w6 l6) hret hjt hbt
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hw a (by omega) (by omega)))
    have e00 : resPtrs μ0 rp 0 = [] := by simp [resPtrs]
    refine ⟨ω2, μ1, _, run1.trans run2, ?_, ?_, F1, by rw [b1]; congr 1; omega, by rw [b5, UInt64.ofNat_toNat],
      by rw [b6, UInt64.ofNat_toNat]⟩
    · rw [e00]; exact H1
    · rw [e00]; exact K1
  · obtain ⟨ω1, μ1, run1, a1, a5, a6, w0, w5, w6, wn, wp, fr1, rd1, wr1⟩ :=
      dr_pre1 (R := R) (P := P) x ω μ0 S v rp n h1 h7 ⟨by omega, by omega⟩ hv hd mp ml (by omega) hr hw
    obtain ⟨H1, K1, F1⟩ := init3 H ⟨hS1, hS2, hS3⟩ fr1 rd1 wr1
    have hl : n < 2 ^ 64 := ml ▸ rdN_lt8 μ0 (v + 16)
    have hp : rp < 2 ^ 64 := mp ▸ rdN_lt8 μ0 (v + 8)
    have C1 : Core code pb S0 S1 s0 μ0 S rp n ret ω[5].toNat ω[6].toNat (resPtrs μ0 rp 0) ω1 μ1 s0 :=
      ⟨H1, by simpa [resPtrs] using K1, F1, by simp [resPtrs], a1, rdN_enc wn hl, rdN_enc wp hp,
        by rw [rdN_enc w0 l0, e0], rdN_enc w5 l5, rdN_enc w6 l6⟩
    obtain ⟨ω2, μ2, s2, N2, run2, C2⟩ :=
      dr_loop (R := R) (P := P) x O ⟨hS1, hS2, hS3⟩ 0 ω1 μ1 s0 hn C1 a5 a6
    obtain ⟨ω3, run3, b1, b5, b6⟩ := dr_end (R := R) (P := P) x ω2 μ2 (S - 56) ret ω[5].toNat ω[6].toNat t
      C2.r1 ⟨by omega, by omega⟩ C2.m0 C2.m5 C2.m6 hret hjt hbt
      (fun a h1 h2 => (C2.stk ⟨hS1, hS2, hS3⟩ (lo := S - 56 + 32) (hi := S) (by omega) (by omega)).1 a h1 (by omega))
    have hs2 := C2.hs
    subst hs2
    exact ⟨ω3, μ2, _, (run1.trans run2).trans run3, C2.H, C2.K, C2.Fm, by rw [b1]; congr 1; omega,
      by rw [b5, UInt64.ofNat_toNat], by rw [b6, UInt64.ofNat_toNat]⟩
/-! ## `ResultsOwn` survives a run that keeps the allocated chunks -/

section Keep

variable {μ μ' : Memory} {st st' : State} {rp n : Nat}

/-- The chunks kept: every allocated chunk of st is a chunk of st' with its data kept. -/
def ChunksKept (μ : Memory) (st : State) (μ' : Memory) (st' : State) : Prop :=
  ∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a

theorem item_keep (O : ResultsOwn μ st rp n) (hk : ChunksKept μ st μ' st') {i o m : Nat} (hi : i < n)
    (hom : o + m ≤ 144) : rdN μ' (rp + 144 * i + o) m = rdN μ (rp + 144 * i + o) m :=
  rdN_frame fun j hj => by
    obtain ⟨d, hd, hu, hin, -⟩ := O.2.2.1 (144 * i + o + j) (by omega)
    rw [show rp + 144 * i + o + j = rp + (144 * i + o + j) by omega]
    exact (hk d hd hu).2 _ hin

theorem innerPtrs_congr {q : Nat} :
    ∀ L, (∀ j, j < L → rdN μ' (q + 24 * j) 8 = rdN μ (q + 24 * j) 8 ∧
      rdN μ' (q + 24 * j + 8) 8 = rdN μ (q + 24 * j + 8) 8) → innerPtrs μ' q L = innerPtrs μ q L
  | 0, _ => by simp [innerPtrs]
  | L + 1, h => by
    rw [innerPtrs_succ, innerPtrs_succ, innerPtrs_congr L (fun j hj => h j (by omega)),
      (h L (by omega)).1, (h L (by omega)).2]

theorem itemPtrs_keep (O : ResultsOwn μ st rp n) (hk : ChunksKept μ st μ' st') {i : Nat} (hi : i < n) :
    itemPtrs μ' (rp + 144 * i) = itemPtrs μ (rp + 144 * i) := by
  have e0 := item_keep O hk hi (o := 0) (m := 1) (by omega)
  simp only [Nat.add_zero] at e0
  have e8 := item_keep O hk hi (o := 8) (m := 8) (by omega)
  have e16 := item_keep O hk hi (o := 16) (m := 8) (by omega)
  have e24 := item_keep O hk hi (o := 24) (m := 8) (by omega)
  unfold itemPtrs
  rw [e0, e8, e16, e24]
  by_cases h5 : rdN μ (rp + 144 * i) 1 = 5
  · rw [if_pos h5, if_pos h5]
  · rw [if_neg h5, if_neg h5]
    by_cases hv : 6 ≤ rdN μ (rp + 144 * i) 1 ∧ rdN μ (rp + 144 * i) 1 < 255
    · rw [if_pos hv, if_pos hv]
      suffices hin : innerPtrs μ' (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) =
          innerPtrs μ (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) by rw [hin]
      by_cases hL : rdN μ (rp + 144 * i + 24) 8 = 0
      · rw [hL]; simp [innerPtrs]
      · obtain ⟨-, d, hd, hu, hq, hend⟩ := O.2.2.2 i hi hv.1 hv.2 hL
        have hk' := (hk d hd hu).2
        apply innerPtrs_congr
        intro j hj
        exact ⟨rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩,
          rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩⟩
    · rw [if_neg hv, if_neg hv]

theorem resPtrs_keep (O : ResultsOwn μ st rp n) (hk : ChunksKept μ st μ' st') :
    ∀ k, k ≤ n → resPtrs μ' rp k = resPtrs μ rp k
  | 0, _ => by simp [resPtrs]
  | k + 1, h => by
    rw [resPtrs_succ, resPtrs_succ, resPtrs_keep O hk k (by omega), itemPtrs_keep O hk (by omega)]

/-- **`ResultsOwn` survives a run that keeps every allocated chunk with its data** (e.g. the results
    store `store_core`, whose `StorePost` says so). -/
theorem ResultsOwn.keep (O : ResultsOwn μ st rp n) (hk : ChunksKept μ st μ' st') :
    ResultsOwn μ' st' rp n := by
  have hr := resPtrs_keep O hk n (Nat.le_refl _)
  refine ⟨hr ▸ O.1, fun q hq => ?_, fun k hk' => ?_, fun i hi h6 h255 hL => ?_⟩
  · obtain ⟨d, hd, hu, ha⟩ := O.2.1 q (hr ▸ hq)
    exact ⟨d, (hk d hd hu).1, hu, ha⟩
  · obtain ⟨d, hd, hu, hin, hn⟩ := O.2.2.1 k hk'
    exact ⟨d, (hk d hd hu).1, hu, hin, hr ▸ hn⟩
  · have e0 := item_keep O hk hi (o := 0) (m := 1) (by omega)
    simp only [Nat.add_zero] at e0
    rw [item_keep O hk hi (o := 8) (m := 8) (by omega), item_keep O hk hi (o := 16) (m := 8) (by omega)]
    rw [item_keep O hk hi (o := 24) (m := 8) (by omega)] at hL ⊢
    rw [e0] at h6 h255
    obtain ⟨hc, d, hd, hu, hq, hend⟩ := O.2.2.2 i hi h6 h255 hL
    exact ⟨hc, d, (hk d hd hu).1, hu, hq, hend⟩

end Keep

end Services.Bootstrap.Acc.Handlers.ResultsDrop
