import Services.Bootstrap.Acc.Transfer.ImplTr
import Services.Bootstrap.Acc.Inputs.Inputs
import Services.Bootstrap.Acc.Items.Disp
import Services.Bootstrap.Acc.Items.Exit
import Services.Bootstrap.Acc.ValuesFitStep
import Services.Bootstrap.SpecLemmas.Items
import Services.Bootstrap.Acc.Handlers.Dispatch

/-!
# The items loop's invariant (R1)

`Spec.accumulate` runs `for it in items do …` over the decoded inputs (`specItem`s, GP v0.8.0 §12).
The binary runs it as the loop at 6766: the `IntoIter` of the decoded `Vec<AccumulateItem>` keeps the
current slot at sp + 168 and the end at sp + 144, over 184-octet slots in the buffer at q (sp + 16)
of capacity cap (sp + 32). Each iteration dispatches on the slot's first word at 6782: −1 is a
transfer (7159, `tr_impl`), anything else (but −2, never a decoded slot) an operand (6827).

**`ItemsInv`** is the state at the loop head for the inputs `ins` still to run. It carries what every
arm needs and keeps:
- the stack frame: sp in ω₁, the iterator's words, the prologue's formatter words (sp + 208 / 136,
  `tr_impl`), the saved return address (sp + 1848, the halt), and the words R5 reads at sp + 184 /
  216 (stored once at 6746 / 6760);
- the allocator's context `HeapCtxC` for some state st, with the slot buffer an allocated chunk;
- each slot left holds its input (`itemOf`), and the slots' buffers are distinct allocated chunks
  (`ItemsOwn`, an obligation on `inputs_decode`), so a frame that keeps those chunks keeps the slots
  (`itemOf_local`);
- the read-only data `tr_impl` and the operand arm read (`TrRO`, `OpRO`), the parameter statics (`Glob`, equal to a base memory
  μ₀'s), and `ValuesFit` of the context (T2's premise, kept by every operation: `ValuesFit.step`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc

/-- The read-only data `tr_impl` reads: the key "transfer-count" at 65956 and `set`'s error table at
    69056 … 69076 (`accRoBytes`). -/
def TrRO (μ : Memory) : Prop :=
  μ.readN 65956 14 = trKey ∧ (∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true) ∧
  rdN μ 69072 4 = 4294900408 ∧ rdN μ 69056 4 = 4294900402 ∧
  (∀ a, 69056 ≤ a → a < 69076 → μ.readable a = true)

/-- `TrRO` reads only below 196608. -/
theorem TrRO.keep {μ μ' : Memory} (h : TrRO μ)
    (hk : ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) : TrRO μ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, fun a ha hb => ?_, ?_, ?_, fun a ha hb => ?_⟩
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact h1
  · rw [(hk a (by omega)).2]; exact h2 a ha hb
  · rw [rdN_frame fun j hj => (hk _ (by omega)).1]; exact h3
  · rw [rdN_frame fun j hj => (hk _ (by omega)).1]; exact h4
  · rw [(hk a (by omega)).2]; exact h5 a ha hb

/-- The operand arm's read-only facts besides `TrRO` (see the module doc). -/
def OpRO (μ : Memory) : Prop :=
  (∃ k, μ.readN 68680 8 = Num.encodeLE 8 k ∧ 1 ≤ k ∧ k + 31 < 68719476736) ∧
  (∃ k, μ.readN 68688 8 = Num.encodeLE 8 k ∧ 5 ≤ k ∧ k + 31 < 68719476736) ∧
  (∃ k, μ.readN 68696 8 = Num.encodeLE 8 k ∧ 35 ≤ k ∧ k + 31 < 68719476736) ∧
  (∀ a, 68680 ≤ a → a < 69076 → μ.readable a = true) ∧
  μ.readN 65736 100 = Services.Bootstrap.Acc.Handlers.jumpTab ∧
  (∀ a, 65736 ≤ a → a < 65836 → μ.readable a = true)

/-- `OpRO` reads only below 196608. -/
theorem OpRO.keep {μ μ' : Memory} (h : OpRO μ)
    (hk : ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) : OpRO μ' := by
  obtain ⟨⟨k0, e0, b0⟩, ⟨k1, e1, b1⟩, ⟨k2, e2, b2⟩, r1, ej, r2⟩ := h
  refine ⟨⟨k0, ?_, b0⟩, ⟨k1, ?_, b1⟩, ⟨k2, ?_, b2⟩, fun a h1 h2 => ?_, ?_, fun a h1 h2 => ?_⟩
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact e0
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact e1
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact e2
  · rw [(hk a (by omega)).2]; exact r1 a h1 h2
  · rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact ej
  · rw [(hk a (by omega)).2]; exact r2 a h1 h2

/-- **The buffers a slot owns** (pointer, length): an operand's trace (capacity at + 0, pointer + 8,
    length + 16) when its capacity is not 0, and its work output's (+ 24 / + 32 / + 40) likewise; a
    transfer owns none. -/
def slotFoot : AccumulateInput → List UInt8 → List (Nat × Nat)
  | .operand o, bs => (if wd bs 0 = 0 then [] else [(wd bs 8, wd bs 16)]) ++
      (match o.result with
       | .ok _ => if wd bs 24 = 0 then [] else [(wd bs 32, wd bs 40)]
       | .err _ => [])
  | .transfer _, _ => []

/-- The buffers the slots from c on own, for the inputs `ins`. -/
def footL : List AccumulateInput → Nat → Memory → List (Nat × Nat)
  | [], _, _ => []
  | i :: r, c, μ => slotFoot i (μ.readN c 184) ++ footL r (c + 184) μ

/-- **Ownership of the slots' buffers** (obligation: `inputs_decode` is to be strengthened to state
    it; decided 2026-11-16, option (C)): the slots' buffers have distinct pointers, none the slot
    buffer q's, and each is the data of an allocated chunk of st covering its length. -/
def ItemsOwn (st : State) (μ : Memory) (c q : Nat) (ins : List AccumulateInput) : Prop :=
  ((footL ins c μ).map Prod.fst).Nodup ∧ q ∉ (footL ins c μ).map Prod.fst ∧
  ∀ pl ∈ footL ins c μ, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = pl.1 ∧
    ∀ a, pl.1 ≤ a → a < pl.1 + pl.2 → InDataA d a

/-- `footL` reads only the slots. -/
theorem footL_congr {μ μ' : Memory} : ∀ (ins : List AccumulateInput) (c : Nat),
    (∀ a, c ≤ a → a < c + 184 * ins.length → μ'.read a = μ.read a) →
    footL ins c μ' = footL ins c μ
  | [], _, _ => rfl
  | i :: r, c, h => by
    simp only [footL, List.length_cons] at h ⊢
    rw [Memory.readN_congr fun j hj => h _ (by omega) (by omega),
      footL_congr r (c + 184) fun a h1 h2 => h a (by omega) (by omega)]

/-- **A slot's input reads only the slot and the buffers it owns.** -/
theorem itemOf_local {i : AccumulateInput} {c : Nat} {μ μ' : Memory}
    (h : (itemOf i).2 (μ.readN c 184) μ)
    (hf : ∀ pl ∈ slotFoot i (μ.readN c 184), ∀ a, pl.1 ≤ a → a < pl.1 + pl.2 → μ'.read a = μ.read a)
    (hs : μ'.readN c 184 = μ.readN c 184) : (itemOf i).2 (μ'.readN c 184) μ' := by
  rw [hs]
  cases i with
  | transfer x => exact h
  | operand o =>
    have tr : ∀ t : List UInt8, RepOpBase (opHashes o) o.gasLimit t (μ.readN c 184) μ →
        RepOpBase (opHashes o) o.gasLimit t (μ.readN c 184) μ' := by
      intro t ⟨b0, b16, b8, bh, bg⟩
      refine ⟨b0, b16, ?_, bh, bg⟩
      by_cases ht : t.length = 0
      · rw [ht]; rw [ht] at b8; exact b8
      · refine (Memory.readN_congr fun j hj => ?_).trans b8
        exact hf (wd (μ.readN c 184) 8, wd (μ.readN c 184) 16)
          (by simp [slotFoot, b0, ht]) _ (by omega) (by rw [b16]; omega)
    simp only [itemOf] at h ⊢
    split
    · next b hb =>
      simp only [slotFoot] at hf
      rw [hb] at h hf
      obtain ⟨hb0, h24, h40, ho⟩ := h
      refine ⟨tr _ hb0, h24, h40, ?_⟩
      by_cases hl : b.toList.length = 0
      · rw [hl]; rw [hl] at ho; exact ho
      · refine (Memory.readN_congr fun j hj => ?_).trans ho
        exact hf (wd (μ.readN c 184) 32, wd (μ.readN c 184) 40)
          (by simp [h24, hl]) _ (by omega) (by rw [h40]; omega)
    · next er he =>
      rw [he] at h
      obtain ⟨hb0, h24, h32⟩ := h
      exact ⟨tr _ hb0, h24, h32⟩

/-- A slot's buffers are among `footL`'s. -/
theorem mem_footL {μ : Memory} : ∀ (ins : List AccumulateInput) (c j : Nat) (i : AccumulateInput)
    (pl : Nat × Nat), ins[j]? = some i → pl ∈ slotFoot i (μ.readN (c + 184 * j) 184) →
    pl ∈ footL ins c μ
  | [], _, _, _, _, h, _ => by simp at h
  | i0 :: r, c, 0, i, pl, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp only [footL, List.mem_append]
    left; simpa using hp
  | i0 :: r, c, j + 1, i, pl, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    simp only [footL, List.mem_append]
    right
    exact mem_footL r (c + 184) j i pl h (by rw [show c + 184 + 184 * j = c + 184 * (j + 1) by omega]; exact hp)

/-- **The slots and their ownership for the inputs after the first**, under a frame that keeps the
    slot buffer's data and every chunk the later slots own, with its data. -/
theorem rest_keep {st st' : State} {μ μ' : Memory} {cur q : Nat} {i : AccumulateInput}
    {rest : List AccumulateInput} {db : Chunk}
    (hslots : ∀ (j : Nat) (i' : AccumulateInput), (i :: rest)[j]? = some i' →
      (itemOf i').2 (μ.readN (cur + 184 * j) 184) μ)
    (hown : ItemsOwn st μ cur q (i :: rest))
    (hdb : ∀ a, cur ≤ a → a < cur + 184 * (rest.length + 1) → InDataA db a)
    (kb : ∀ a, InDataA db a → μ'.read a = μ.read a)
    (kf : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ (footL rest (cur + 184) μ).map Prod.fst →
      d ∈ chunks st' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) :
    (∀ (j : Nat) (i' : AccumulateInput), rest[j]? = some i' →
      (itemOf i').2 (μ'.readN (cur + 184 + 184 * j) 184) μ') ∧ ItemsOwn st' μ' (cur + 184) q rest := by
  have hfeq : footL rest (cur + 184) μ' = footL rest (cur + 184) μ :=
    footL_congr rest _ (fun a h1 h2 => kb a (hdb a (by omega) (by omega)))
  obtain ⟨hnd, hq, hch⟩ := hown
  simp only [footL, List.map_append] at hnd hq hch
  have hch' : ∀ pl ∈ footL rest (cur + 184) μ, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = pl.1 ∧
      ∀ a, pl.1 ≤ a → a < pl.1 + pl.2 → InDataA d a := fun pl hp =>
    hch pl (List.mem_append_right _ hp)
  refine ⟨fun j i' hj => ?_, ?_, ?_, ?_⟩
  · have hjl : j < rest.length := by
      have := List.getElem?_eq_some_iff.1 hj; exact this.1
    have h1 := hslots (j + 1) i' (by simpa using hj)
    rw [show cur + 184 + 184 * j = cur + 184 * (j + 1) by omega]
    refine itemOf_local h1 (fun pl hp a ha1 ha2 => ?_) (Memory.readN_congr fun k hk =>
      kb _ (hdb _ (by omega) (by omega)))
    have hm := mem_footL rest (cur + 184) j i' pl hj
      (by rw [show cur + 184 + 184 * j = cur + 184 * (j + 1) by omega]; exact hp)
    obtain ⟨d, hd, hdu, hda, hdr⟩ := hch' pl hm
    exact (kf d hd hdu (by rw [hda]; exact List.mem_map_of_mem hm)).2 a (hdr a ha1 ha2)
  · rw [hfeq]; exact (List.nodup_append.1 hnd).2.1
  · rw [hfeq]; exact fun h => hq (List.mem_append_right _ h)
  · intro pl hp
    rw [hfeq] at hp
    obtain ⟨d, hd, hdu, hda, hdr⟩ := hch' pl hp
    exact ⟨d, (kf d hd hdu (by rw [hda]; exact List.mem_map_of_mem hp)).1, hdu, hda, hdr⟩

/-- **A decoded slot's buffers are `uFoot`'s** (for a sized input). -/
theorem slotFoot_eq {i : AccumulateInput} {bs : List UInt8} {μ : Memory} (h : (itemOf i).2 bs μ)
    (hs : InputSized i) : slotFoot i bs = uFoot bs := by
  cases i with
  | transfer x =>
    simp only [itemOf, RepTr] at h
    have w0 : wd bs 0 = 18446744073709551615 := by unfold wd; simpa using h.1
    simp [slotFoot, uFoot, w0]
  | operand o =>
    simp only [InputSized] at hs
    have htl : o.authTrace.toList.length ≤ 16384 := by rw [ByteArray.length_toList']; exact hs.2.2.2.2.2.1
    cases hr : o.result with
    | ok b =>
      simp only [itemOf, hr] at h
      obtain ⟨⟨b0, -⟩, b24, -⟩ := h
      have hbl : b.toList.length ≤ 16384 := by rw [ByteArray.length_toList']; exact hs.2.2.2.2.2.2 b hr
      simp only [slotFoot, uFoot, hr, b0, b24, show o.authTrace.toList.length ≠ 18446744073709551615 by omega,
        show b.toList.length ≠ 18446744073709551615 by omega, if_false, or_false]
    | err e =>
      simp only [itemOf, hr] at h
      obtain ⟨⟨b0, -⟩, b24, -⟩ := h
      simp only [slotFoot, uFoot, hr, b0, b24, show o.authTrace.toList.length ≠ 18446744073709551615 by omega,
        if_false, or_true, if_true, List.append_nil]

/-- The slots' buffers, `footL` against `feetL`. -/
theorem footL_eq_feetL {μ : Memory} {q : Nat} : ∀ (ins : List AccumulateInput) (L : Nat),
    (∀ (j : Nat) (i : AccumulateInput), ins[j]? = some i → (itemOf i).2 (μ.readN (q + 184 * (L + j)) 184) μ) →
    (∀ i ∈ ins, InputSized i) → footL ins (q + 184 * L) μ = feetL μ q L ins.length
  | [], _, _, _ => rfl
  | i :: r, L, h, hs => by
    rw [footL, List.length_cons, feetL_succ, slotFoot_eq (by simpa using h 0 i rfl) (hs i (by simp)),
      show q + 184 * L + 184 = q + 184 * (L + 1) by omega,
      footL_eq_feetL r (L + 1) (fun j i' hj => by
        have := h (j + 1) i' (by simpa using hj); rwa [show L + (j + 1) = L + 1 + j by omega] at this)
        (fun i' hi' => hs i' (by simp [hi']))]

/-- **`ItemsOwn` from the decode's `SlotsOwn`** (the cursor at the buffer q, before the loop). -/
theorem itemsOwn_of_slots {st : State} {μ : Memory} {q : Nat} {ins : List AccumulateInput}
    (h : ∀ (j : Nat) (i : AccumulateInput), ins[j]? = some i → (itemOf i).2 (μ.readN (q + 184 * j) 184) μ)
    (hs : ∀ i ∈ ins, InputSized i) (hS : SlotsOwn st μ q ins.length) : ItemsOwn st μ q q ins := by
  have e : footL ins q μ = feetL μ q 0 ins.length := by
    have := footL_eq_feetL (μ := μ) (q := q) ins 0 (fun j i hj => by simpa using h j i hj) hs
    simpa using this
  obtain ⟨-, hnd, hq, hpl⟩ := hS
  rw [ItemsOwn, e]
  exact ⟨hnd, hq, hpl⟩

/-- The loop's cursor in state s: ω₅ at the dispatch 6782 (the loop's first entry, 6764 → 6782), else the
    word at sp + 168 (the loop head 6766). -/
def curAt (sp : Nat) (s : St Stream) : Nat := if s.i = 6782 then s.ω[5].toNat else rdN s.μ (sp + 168) 8

theorem curAt_6766 {sp : Nat} {s : St Stream} (h : s.i = 6766) : curAt sp s = rdN s.μ (sp + 168) 8 := by
  simp [curAt, h]

theorem curAt_6782 {sp : Nat} {s : St Stream} (h : s.i = 6782) : curAt sp s = s.ω[5].toNat := by
  simp [curAt, h]

/-- **The items loop's state at its head 6766** with the inputs `ins` still to run (see the module
    docstring), or at the dispatch 6782 with the cursor in ω₅ (the loop's first entry). The frame: sp, the slot buffer q of capacity cap, the end e; μ₀ fixes the statics. -/
structure ItemsInv (env : AccEnv) (pb S0 S1 sp q cap e : Nat) (μ₀ : Memory)
    (ins : List AccumulateInput) (s : St Stream) : Prop where
  pc : s.i = 6766 ∨ (s.i = 6782 ∧ ins ≠ [])
  r1 : s.ω[1] = UInt64.ofNat sp
  hsp : 2147487744 ≤ sp ∧ sp % 8 = 0
  hstk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1
  cur : curAt sp s + 184 * ins.length = e
  m144 : rdN s.μ (sp + 144) 8 = e
  m16 : rdN s.μ (sp + 16) 8 = q
  m32 : rdN s.μ (sp + 32) 8 = cap
  m208 : rdN s.μ (sp + 208) 8 = 2800
  m136 : rdN s.μ (sp + 136) 8 = 2804
  m184 : rdN s.μ (sp + 184) 8 = 2 ^ 63
  m216 : rdN s.μ (sp + 216) 8 = 2 ^ 63 + 1
  m1848 : rdN s.μ (sp + 1848) 8 = 4294901760
  hcap : ins.length ≤ cap
  heap : ∃ st, HeapCtxC env.code pb S0 S1 s.μ st ∧
    (cap ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q ∧
      ∀ a, curAt sp s ≤ a → a < e → InDataA d a) ∧
    (∀ (j : Nat) (i : AccumulateInput), ins[j]? = some i →
      (itemOf i).2 (s.μ.readN (curAt sp s + 184 * j) 184) s.μ) ∧
    ItemsOwn st s.μ (curAt sp s) q ins
  ro : TrRO s.μ
  ro2 : OpRO s.μ
  glob : ∀ a, Glob a → s.μ.read a = μ₀.read a
  fit : ValuesFit env s.c.1
  sized : ∀ i ∈ ins, InputSized i

/-- **To the dispatch 6782** from the loop's state with an input left: from 6766 by `il_step`, or already
    there; ω₁ = sp and ω₅ = the cursor, the memory unchanged. -/
theorem ItemsInv.to6782 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type} {R : HostRel X}
    {env : AccEnv} {pb S0 S1 sp q cap e : Nat} {μ₀ : Memory} {i : AccumulateInput}
    {rest : List AccumulateInput} {s : St Stream} (hI : ItemsInv env pb S0 S1 sp q cap e μ₀ (i :: rest) s)
    (x : X) (hS : sp + 1856 < 4294967296) (hrf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.readable a = true) :
    ∃ ω' N, FreeStepsH p R s.i s.ω s.μ x 6782 ω' s.μ x N ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = UInt64.ofNat (curAt sp s) := by
  rcases hI.pc with h | ⟨h, -⟩
  · have hc := hI.cur
    simp only [List.length_cons] at hc
    rw [curAt_6766 h] at hc ⊢
    have := hI.hstk
    obtain ⟨ω1, r1, e5, f1⟩ := il_step (p := p) (P := P) (R := R) x s.ω s.μ sp _ e hI.r1
      ⟨by have := hI.hsp; omega, hS⟩ rfl hI.m144 (by omega) hrf
    exact ⟨ω1, _, by rw [h]; exact r1, (f1 1 (by decide)).trans hI.r1, e5⟩
  · exact ⟨s.ω, 0, by rw [h]; exact .refl, hI.r1, by rw [curAt_6782 h, UInt64.ofNat_toNat]⟩

end Services.Bootstrap.Acc
