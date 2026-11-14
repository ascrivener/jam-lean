import Services.Bootstrap.Refine.PassGrow
import Services.Bootstrap.Refine.LoopG
import Services.Bootstrap.Bridge

/-!
# Refine's transform loop over instructions passed through unchanged

`PInv k` is the loop's state at 5042 after the first k of the n decoded instructions (at E, 232 octets
each, inside an allocated chunk `ce`), all passed through: the output `Vec<Instruction>` at M + 248 is
`{cap, ptr, k}` and holds the first k instructions' octets as they were (in μ0), the allocator's context
holds (`HeapCtx`), and the instructions' chunk is kept. `step` is one more instruction (`Pass.pass_elem`
when the output has room, `PassGrow.pass_elem_grow` when it is full); `loop` is all of them, under
refine's host contract, unless the heap is exhausted.
-/

namespace Services.Bootstrap.Refine.PassLoop

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.Pass Services.Bootstrap.Refine.PassGrow
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Distinct chunks of a well-formed heap lie apart, each one's 32-octet header included. -/
theorem chunk_apart {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s) (hcd : c ≠ d) :
    c.addr + 32 * c.size ≤ d.addr ∨ d.addr + 32 * d.size ≤ c.addr := by
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  exact Decode.HeapFrame.Tiles.disjoint ht c hc d hd hcd

/-- **A failed allocation** (`Bridge.AllocFails`: a null allocation at one of the allocators' return
    points, or the size check before one), reached by a run whose host context may change on the way: the
    heap exhaustion of `Bridge.ExhaustsHeap`, for loops whose steps make host calls. -/
def ExhaustsX (env : RefineHost.Env) (cap pb : Nat) (p : ByteArray) (i : Nat) (ω : Regs) (μ : Memory)
    (x : RefineCtx) (n : Nat) : Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (x' : RefineCtx) (j : Nat),
    FreeStepsH p (refineContractK cap env) i ω μ x j ω' μ' x' n ∧ Bridge.AllocFails j ω'

theorem ExhaustsX.of {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat} {ω : Regs}
    {μ : Memory} {x : RefineCtx} {n : Nat} (h : Exhausts env cap pb p P i ω μ x n) : ExhaustsX env cap pb p i ω μ x n := by
  obtain ⟨ω', μ', j, run, e7, ha⟩ := h
  refine ⟨ω', μ', x, j, run, Or.inl ⟨?_, e7⟩⟩
  rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-- `Fmt.Exhausts` (the `alloc` or `realloc` wrapper returning null) under refine's contract is `ExhaustsX`. -/
theorem ExhaustsX.ofFmt {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {i : Nat} {ω : Regs}
    {μ : Memory} {x : RefineCtx} {n : Nat}
    (h : ∃ (ω' : Regs) (μ' : Memory) (x' : RefineCtx) (j : Nat),
      FreeStepsH p (refineContractK cap env) i ω μ x j ω' μ' x' n ∧ ω'[7] = UInt64.ofNat 0 ∧ (j = 40611 ∨ j = 40821)) :
    ExhaustsX env cap pb p i ω μ x n := by
  obtain ⟨ω', μ', x', j, run, e7, hj⟩ := h
  refine ⟨ω', μ', x', j, run, Or.inl ⟨?_, e7⟩⟩
  rcases hj with rfl | rfl <;> decide

theorem ExhaustsX.pre {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {i j : Nat} {ω ω1 : Regs}
    {μ μ1 : Memory} {x x1 : RefineCtx} {n m : Nat}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x j ω1 μ1 x1 n) (h : ExhaustsX env cap pb p j ω1 μ1 x1 m) :
    ExhaustsX env cap pb p i ω μ x (n + m) := by
  obtain ⟨ω', μ', x', k, run', ha⟩ := h
  exact ⟨ω', μ', x', k, run.trans run', ha⟩

theorem ExhaustsX.mono {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory}
    {x : RefineCtx} {n m : Nat} (h : ExhaustsX env cap pb p i ω μ x n) (hnm : n ≤ m) :
    ExhaustsX env cap pb p i ω μ x m := by
  obtain ⟨ω', μ', x', k, run', ha⟩ := h
  exact ⟨ω', μ', x', k, run'.mono hnm, ha⟩

/-- **The transform loop's state at 5042 after k instructions passed through.** -/
structure PInv (env : RefineHost.Env) (pb S0 S1 M E n : Nat) (ce : Chunk) (capI : Nat) (μ0 : Memory)
    (Kp : Chunk → Prop) (O : Nat → List UInt8 → Prop) (i k : Nat) (ω : Regs) (μ : Memory) (s : State) : Prop where
  h1 : ω[1] = UInt64.ofNat M
  /-- The cursor: at the loop head 5042, the word at M + 144; at 5054, where refine's prologue enters the
      loop past the end test, ω₅. -/
  cur : (i = 5042 ∧ μ.readN (M + 144) 8 = Num.encodeLE 8 (E + 232 * k)) ∨ (i = 5054 ∧ ω[5] = UInt64.ofNat (E + 232 * k))
  en : μ.readN (M + 120) 8 = Num.encodeLE 8 (E + 232 * n)
  c128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832
  c136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809
  /-- `isize::MAX / 24`, `Import`'s bound on its item count. -/
  c48 : μ.readN (M + 48) 8 = Num.encodeLE 8 384307168202282325
  /-- The mask of the dispatch indices whose staged element needs no drop after its handler
      (bits 9, 10, 21), tested at 5950. -/
  c40 : μ.readN (M + 40) 8 = Num.encodeLE 8 2098688
  /-- The `Lookup` log line's constants: its target (66793), template (66506) and the argument's
      `Debug` function (668). -/
  c16 : μ.readN (M + 16) 8 = Num.encodeLE 8 66793
  c24 : μ.readN (M + 24) 8 = Num.encodeLE 8 66506
  c32 : μ.readN (M + 32) 8 = Num.encodeLE 8 668
  /-- The input's `vec::IntoIter` at M + 272: `{buf, ptr, cap, end}`. -/
  i0 : μ.readN (M + 272) 8 = Num.encodeLE 8 (ce.addr + 32)
  i8 : μ.readN (M + 280) 8 = Num.encodeLE 8 (E + 232 * k)
  i16 : μ.readN (M + 288) 8 = Num.encodeLE 8 capI
  i24 : μ.readN (M + 296) 8 = Num.encodeLE 8 (E + 232 * n)
  out : ∃ cap ptr, μ.readN (M + 248) 8 = Num.encodeLE 8 cap ∧ μ.readN (M + 256) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (M + 264) 8 = Num.encodeLE 8 k ∧ k ≤ cap ∧ cap ≤ 2 * n + 4 ∧ ptr < 2147483648 ∧
    ((cap = 0 ∧ ptr = 8) ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1 ∧
      c ≠ ce ∧ ¬ Kp c) ∧
    ∀ j, j < k → O j (μ.readN (ptr + 232 * j) 232)
  H : HeapCtx env pb S0 S1 μ s
  hce : ce ∈ chunks s ∧ ce.used = true
  data : ∀ a, InData ce a → μ.read a = μ0.read a
  /-- The chunks to keep (`Kp`), such as the payload's copy: allocated, with their data as in μ0. -/
  kp : ∀ d, Kp d → d ∈ chunks s ∧ d.used = true ∧ ∀ a, InData d a → μ.read a = μ0.read a
  /-- The frame's words refine's epilogue reads, as in μ0: the work item's index (M + 80), the payload's
      `Vec`'s capacity and buffer (M + 88, M + 112) and the saved ω₆, ω₅ and return address
      (M + 608 … M + 632). The handlers use the words between them. -/
  fr : ∀ a, (M + 80 ≤ a ∧ a < M + 96) ∨ (M + 112 ≤ a ∧ a < M + 120) ∨ (M + 608 ≤ a ∧ a < M + 632) →
    μ.read a = μ0.read a

/-- At the loop head 5042, the cursor is the word at M + 144. -/
theorem PInv.cur42 {env : RefineHost.Env} {pb S0 S1 M E n : Nat} {ce : Chunk} {capI : Nat} {μ0 : Memory}
    {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {k : Nat} {ω : Regs} {μ : Memory} {s : State}
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 k ω μ s) :
    μ.readN (M + 144) 8 = Num.encodeLE 8 (E + 232 * k) := by
  rcases st.cur with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

/-- What the loop needs of its layout: refine's frame M on the stack, the n < 128 instructions at E inside
    the allocated chunk `ce`. -/
structure LayP (S0 S1 M E n : Nat) (ce : Chunk) : Prop where
  hM : S0 + 456 ≤ M ∧ M + 632 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0
  hn : n < 128
  hE : ce.addr + 32 ≤ E ∧ E + 232 * n ≤ ce.addr + 32 * ce.size
  hEtop : E + 232 * n < 2147483648

/-- Equal reads of 232·k octets are equal slot by slot. -/
theorem slot_eq {μ μ' : Memory} {a a' k j : Nat} (h : μ'.readN a' (232 * k) = μ.readN a (232 * k)) (hj : j < k) :
    μ'.readN (a' + 232 * j) 232 = μ.readN (a + 232 * j) 232 := by
  rw [Decode.Loop.readN_sub μ' a' (232 * k) (232 * j) 232 _ h (by omega),
    Decode.Loop.readN_sub μ a (232 * k) (232 * j) 232 _ rfl (by omega)]

/-- **One instruction passed through, with room in the output** (`k ≠ cap`): `PInv k` at 5042 becomes
    `PInv (k + 1)` at 5042, the new output slot holding instruction k's octets as they were in μ0. -/
theorem step_room {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    {X : Type} {R : HostRel X} (env : RefineHost.Env) (x : X) (ω : Regs) (μ μ0 : Memory) (s : State)
    {pb S0 S1 M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i : Nat} (L : LayP S0 S1 M E n ce)
    (k : Nat) (hk : k < n) (t : Nat) (ht : PassK t (rdN μ0 (E + 232 * k + 44) 1))
    (sD0 : μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (hO : O k (μ0.readN (E + 232 * k) 232))
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s)
    (hroom : ∀ cap, μ.readN (M + 248) 8 = Num.encodeLE 8 cap → k ≠ cap) :
    ∃ ω' μ', FreeStepsH p R i ω μ x 5042 ω' μ' x 4000 ∧
      PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 (k + 1) ω' μ' s := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨hE0, hE1⟩ := L.hE
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  have hkc' := hroom cap vc
  obtain ⟨co, hco, hcoa, hcou, hcos, hcoe, hcok⟩ := hold.resolve_left (fun h => hkc' (by omega))
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in st.H.wf hco hcou
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have hap := chunk_apart st.H.wf hco st.hce.1 hcoe
  have inE : ∀ a, E ≤ a → a < E + 232 * n → InData ce a := fun a h1 h2 => ⟨by omega, by omega⟩
  have sD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t) := by
    rw [Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]; exact sD0
  have hcs : 232 * cap + 32 ≤ 32 * co.size := by rw [hcos]; omega
  have hb : rdN μ (E + 232 * k + 44) 1 = rdN μ0 (E + 232 * k + 44) 1 := by
    unfold rdN; rw [Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]
  obtain ⟨ω', μ', run, e1, ecur, elen, eslot, een, e128, e136, ecap, eptr, efr, erd, ewr, e280, efr2⟩ :=
    pass_elem (p := p) (P := P) (R := R) x ω μ M (E + 232 * k) (E + 232 * n) t cap ptr k (by rw [hb]; exact ht)
    ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) hkc' (by omega)
    ⟨by omega, by omega⟩ (by omega) (by omega) st.h1 i st.cur st.en sD st.c128 st.c136 vc vp vl
    (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable st.H st.hce.1 st.hce.2
      (inE a (by omega) (by omega))))
    (fun a h1 h2 => st.H.st a (by omega) (by omega))
    (fun a h1 h2 => Decode.VecU8.heap_writable st.H hco hcou ⟨by omega, by omega⟩)
  have H' : HeapCtx env pb S0 S1 μ' s := Decode.VecU8.ctx_congr_data st.H hco
    (fun a ha h => efr a (by omega) (by omega) (by omega)) ewr
  have fr : ∀ a l, a ≤ M + 296 → M ≤ a → l ≤ 8 → (a + l ≤ M + 144 ∨ (M + 152 ≤ a ∧ a + l ≤ M + 264) ∨
      (M + 272 ≤ a ∧ a + l ≤ M + 280) ∨ (M + 288 ≤ a ∧ a + l ≤ M + 304)) → μ'.readN a l = μ.readN a l :=
    fun a l _ h0 _ h => Memory.readN_congr (fun j hj => efr2 _ (by omega))
  refine ⟨ω', μ', run, ⟨e1, ?_, een, e128, e136, by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.c48,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.c40,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.c16,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.c24,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.c32,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.i0, ?_,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.i16,
    by rw [fr _ 8 (by omega) (by omega) (by omega) (by omega)]; exact st.i24,
    ⟨cap, ptr, ecap, eptr, elen, by omega, hcapn, hptr, Or.inr ⟨co, hco, hcoa, hcou, hcos, hcoe, hcok⟩, ?_⟩, H', st.hce,
    fun a ha => ?_, fun d hd => ?_, fun a ha => ?_⟩⟩
  · exact Or.inl ⟨rfl, by rw [ecur]; congr 1 <;> omega⟩
  · rw [e280]; congr 1 <;> omega
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Memory.readN_congr (fun i hi => efr _ (by omega) (by omega) (by omega))]; exact hout j hj
    · rw [eslot, Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]; exact hO
  · unfold InData at ha
    rw [efr a (by omega) (by omega) (by omega), st.data a ha]
  · obtain ⟨hd', hdu, hdd⟩ := st.kp d hd
    refine ⟨hd', hdu, fun a ha => ?_⟩
    have hne : d ≠ co := fun h => hcok (h ▸ hd)
    have hd := hd'
    have hdj := Decode.VecU8.data_disj st.H.wf hd hco hne ha
    obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hd hdu
    unfold InData at ha
    rw [efr a (by omega) (by omega) (by omega), hdd a ⟨ha.1, ha.2⟩]
  · rw [efr2 a (by omega), st.fr a ha]

/-- **One instruction passed through, with the output full** (`k = cap`): `PInv k` at 5042 becomes
    `PInv (k + 1)` at 5042 for a grown heap s', or the heap is exhausted. -/
theorem step_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) {hb : Nat} (s : State)
    {pb S0 S1 M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop} {i : Nat} (L : LayP S0 S1 M E n ce)
    (k : Nat) (hk : k < n) (t : Nat) (ht : PassK t (rdN μ0 (E + 232 * k + 44) 1))
    (sD0 : μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (hO : O k (μ0.readN (E + 232 * k) 232))
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O i k ω μ s)
    (hfull : μ.readN (M + 248) 8 = Num.encodeLE 8 k) :
    (∃ s' ω' μ', FreeStepsH p (refineContractK cap0 env) i ω μ x 5042 ω' μ' x (512 * n + 6100) ∧
      PInv env pb S0 S1 M E n ce capI μ0 Kp O 5042 (k + 1) ω' μ' s') ∨
    Exhausts env cap0 pb p P i ω μ x (512 * n + 6100) := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn := L.hn
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨hE0, hE1⟩ := L.hE
  have hEtop := L.hEtop
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  have hck : cap = k := by
    have := vc.symm.trans hfull
    have h1 := congrArg Num.decodeLE this
    rw [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE] at h1
    omega
  subst hck
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have inE : ∀ a, E ≤ a → a < E + 232 * n → InData ce a := fun a h1 h2 => ⟨by omega, by omega⟩
  have sD : μ.readN (E + 232 * cap) 8 = Num.encodeLE 8 (9223372036854775807 + t) := by
    rw [Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]; exact sD0
  -- the old buffer, and the instructions' chunk apart from it
  have hold' : cap = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1 := by
    rcases hold with ⟨h0, _⟩ | ⟨c, hc, ha, hu, hs, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨c, hc, ha, hu, hs⟩
  have hcep : ce.addr + 32 ≠ ptr := by
    rcases hold with ⟨_, rfl⟩ | ⟨c, hc, ha, hu, hs, hne, -⟩
    · omega
    · intro h
      have := chunk_apart st.H.wf hc st.hce.1 hne
      omega
  have hpl : ptr + 232 * cap < 2147483648 := by
    rcases hold with ⟨h0, rfl⟩ | ⟨c, hc, ha, hu, hs, _⟩
    · subst h0; omega
    · obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in st.H.wf hc hu
      rw [hs] at hcT; omega
  have hb44 : rdN μ (E + 232 * cap + 44) 1 = rdN μ0 (E + 232 * cap + 44) 1 := by
    unfold rdN; rw [Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]
  rcases pass_elem_grow (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω μ s M (E + 232 * cap) (E + 232 * n) t
      cap ptr pb S0 S1 st.H (by rw [hb44]; exact ht) hold' (by omega) ⟨by omega, by omega, hM2, hM8⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega) hpl st.h1 i st.cur st.en sD st.c128 st.c136 vc vp vl
      (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable st.H st.hce.1 st.hce.2
        (inE a (by omega) (by omega)))) with
    ⟨q, s', ω', μ', run, e1, ecur, elen, ecap, eptr, hnew, emove, eslot, een, e128, e136, H', keep, fresh, e280,
      efr2⟩ | hx
  · obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H'.wf hnew rfl
    simp only at hq0 hqT
    have hb0' := H'.hb0
    have hbT' := H'.hbT
    obtain ⟨hce', hkeep⟩ := keep ce st.hce.1 st.hce.2 hcep
    have hfr := fresh ce st.hce.1 st.hce.2 hcep
    have fr : ∀ a l, M ≤ a → (a + l ≤ M + 144 ∨ (M + 272 ≤ a ∧ a + l ≤ M + 280) ∨
        (M + 288 ≤ a ∧ a + l ≤ M + 304)) → μ'.readN a l = μ.readN a l :=
      fun a l h0 h => Memory.readN_congr (fun j hj => efr2 _ (by omega))
    refine Or.inl ⟨s', ω', μ', run.mono (by omega), ⟨e1, ?_, een, e128, e136,
      by rw [fr _ 8 (by omega) (by omega)]; exact st.c48, by rw [fr _ 8 (by omega) (by omega)]; exact st.c40,
      by rw [fr _ 8 (by omega) (by omega)]; exact st.c16, by rw [fr _ 8 (by omega) (by omega)]; exact st.c24,
      by rw [fr _ 8 (by omega) (by omega)]; exact st.c32,
      by rw [fr _ 8 (by omega) (by omega)]; exact st.i0, ?_,
      by rw [fr _ 8 (by omega) (by omega)]; exact st.i16, by rw [fr _ 8 (by omega) (by omega)]; exact st.i24,
      ⟨max (2 * cap) 4, q, ecap, eptr, elen, by omega, by omega, by omega,
        Or.inr ⟨_, hnew, by simp; omega, rfl, rfl, fun h => hfr (by rw [← h]; simp; omega), ?_⟩, ?_⟩,
      H', ⟨hce', st.hce.2⟩, fun a ha => by rw [hkeep a ha, st.data a ha], fun d hd => ?_, fun a ha => ?_⟩⟩
    · exact Or.inl ⟨rfl, by rw [ecur]; congr 1 <;> omega⟩
    · rw [e280]; congr 1 <;> omega
    · -- the new buffer is none of the chunks to keep
      intro hK
      obtain ⟨hd, hdu, -⟩ := st.kp _ hK
      by_cases hp : (⟨q - 32, (232 * max (2 * cap) 4 + 31) / 32 + 1, true⟩ : Chunk).addr + 32 = ptr
      · rcases hold with ⟨h0, rfl⟩ | ⟨c, hc, ha, hu, hs, -, hck⟩
        · obtain ⟨hd0, -, -⟩ := Decode.VecU8.chunk_in st.H.wf hd hdu
          simp at hp hd0
        · by_cases hcd : (⟨q - 32, (232 * max (2 * cap) 4 + 31) / 32 + 1, true⟩ : Chunk) = c
          · exact hck (hcd ▸ hK)
          · have := chunk_apart st.H.wf hd hc hcd
            simp at hp this; omega
      · exact fresh _ hd hdu hp (by simp; omega)
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [slot_eq emove hj]; exact hout j hj
      · rw [eslot, Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]; exact hO
    · have hKd := hd
      obtain ⟨hd, hdu, hdd⟩ := st.kp d hKd
      have hdp : d.addr + 32 ≠ ptr := by
        rcases hold with ⟨h0, rfl⟩ | ⟨c, hc, ha, hu, hs, -, hck⟩
        · obtain ⟨hd0, -, -⟩ := Decode.VecU8.chunk_in st.H.wf hd hdu
          omega
        · intro h
          have hcd : d ≠ c := fun e => hck (e ▸ hKd)
          have ht := st.H.wf.2.2.2.1
          unfold TilesOk at ht
          exact hcd (Picoalloc.Tiles.addr_inj ht d hd c hc (by omega))
      obtain ⟨hd', hk⟩ := keep d hd hdu hdp
      exact ⟨hd', hdu, fun a ha => by rw [hk a ha, hdd a ha]⟩
    · rw [efr2 a (by omega), st.fr a ha]
  · exact Or.inr (hx.mono (by omega))

/-- **The loop over instructions passed through** (5042 … 5042): from `PInv k`, the remaining m = n − k
    instructions, each of a kind passed through, reach `PInv n` for some heap s', or the heap is
    exhausted. The output's slot j holds instruction j's octets as they were in μ0. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (μ0 : Memory) {hb : Nat} {pb S0 S1 M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop}
    (L : LayP S0 S1 M E n ce)
    (kinds : ∀ j, j < n → ∃ t, PassK t (rdN μ0 (E + 232 * j + 44) 1) ∧
      μ0.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (m k : Nat) (ω : Regs) (μ : Memory) (s : State) (hkm : k + m = n)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = μ0.readN (E + 232 * j) 232) 5042 k ω μ s) :
    (∃ s' ω' μ', FreeStepsH p (refineContractK cap0 env) 5042 ω μ x 5042 ω' μ' x (m * (512 * n + 6100)) ∧
      PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = μ0.readN (E + 232 * j) 232) 5042 n ω' μ' s') ∨
    ExhaustsX env cap0 pb p 5042 ω μ x (m * (512 * n + 6100)) := by
  have step : ∀ k ω μ y, k < n → (y = x ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 Kp
      (fun j bs => bs = μ0.readN (E + 232 * j) 232) 5042 k ω μ s) →
      (∃ ω' μ' y', FreeStepsH p (refineContractK cap0 env) 5042 ω μ y 5042 ω' μ' y' (512 * n + 6100) ∧
        (y' = x ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 Kp (fun j bs => bs = μ0.readN (E + 232 * j) 232)
          5042 (k + 1) ω' μ' s)) ∨ ExhaustsX env cap0 pb p 5042 ω μ y (512 * n + 6100) := by
    intro k ω μ y hk ⟨hy, s, st⟩
    subst hy
    obtain ⟨t, ht, sD0⟩ := kinds k hk
    obtain ⟨cap, ptr, vc, -, -, -, hcapn, -⟩ := st.out
    by_cases hkc : k = cap
    · subst hkc
      rcases step_full (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 y ω μ μ0 s L k hk t ht sD0 rfl st vc with
        ⟨s1, ω1, μ1, run1, st1⟩ | hx
      · exact Or.inl ⟨ω1, μ1, y, run1, rfl, s1, st1⟩
      · exact Or.inr (ExhaustsX.of hx)
    · obtain ⟨ω1, μ1, run1, st1⟩ := step_room (p := p) (P := P) env y ω μ μ0 s L k hk t ht sD0 rfl st
        (fun c hc => by
          intro h; subst h
          have h1 := congrArg Num.decodeLE (vc.symm.trans hc)
          rw [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE] at h1
          have := L.hn
          omega)
      exact Or.inl ⟨ω1, μ1, y, run1.mono (by omega), rfl, s, st1⟩
  rcases LoopG.loop (p := p) (R := refineContractK cap0 env) 5042 n (512 * n + 6100)
      (fun k ω μ y => y = x ∧ ∃ s, PInv env pb S0 S1 M E n ce capI μ0 Kp
        (fun j bs => bs = μ0.readN (E + 232 * j) 232) 5042 k ω μ s)
      (fun i ω μ y b => ExhaustsX env cap0 pb p i ω μ y b)
      (fun run h => ExhaustsX.pre run h) (fun h hab => h.mono hab) step m k ω μ x hkm ⟨rfl, s, st⟩ with
    ⟨ω', μ', y, run, rfl, s', st'⟩ | hx
  · exact Or.inl ⟨s', ω', μ', run, st'⟩
  · exact Or.inr hx

end Services.Bootstrap.Refine.PassLoop
