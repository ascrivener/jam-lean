import Services.Bootstrap.Refine.DropOutL

/-!
# Refine's exit: the output `Vec<Instruction>` dropped, with heap elements

`DropOut.drop_vec` walks the output slice when no element owns heap memory. Here an element may also be a
`DeleteItems` (index 5) or `Imported` (index 19), whose `Vec<Vec<u8>>` is freed by `DropOutH.drop_vv`. `VVAt` describes
such an element: its words in memory, its items, and the chunks it owns (`own`). The elements lie in the data of an
allocated chunk `cb` (the output buffer) that no element owns, and different elements own different chunks.
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code).
-/

namespace Services.Bootstrap.Refine.DropVecH

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.CodeT1B
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Refine.DropOut Services.Bootstrap.Refine.DropOutH Services.Bootstrap.Refine.DropOutL
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Picoalloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **A heap element at el** (memory μ, allocator state s): index t ∈ {5, 19} (`VK`), its `Vec<Vec<u8>>` {c0, ptr, len}
    at el + 8 … el + 32, len items {c i, q i} at ptr + 24 i lying in the data of the outer buffer `co` (allocated, with
    co.addr + 32 = ptr, when c0 ≠ 0), each item with c i ≠ 0 owning the allocated chunk `cs i` (data at q i), distinct
    and not `co`. Every chunk it owns satisfies `own`. -/
def VVAt (μ : Memory) (s : State) (el : Nat) (own : Chunk → Prop) : Prop :=
  ∃ (t arm head nxt back ret c0 ptr len : Nat) (c q : Nat → Nat) (cs : Nat → Chunk) (co : Chunk),
    VK t arm head nxt back ret ∧
    μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + t) ∧
    μ.readN (el + 8) 8 = Num.encodeLE 8 c0 ∧ μ.readN (el + 16) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (el + 24) 8 = Num.encodeLE 8 len ∧
    (∀ i, i < len → μ.readN (ptr + 24 * i) 8 = Num.encodeLE 8 (c i) ∧
      μ.readN (ptr + 24 * i + 8) 8 = Num.encodeLE 8 (q i)) ∧
    (c0 ≠ 0 → co.addr + 32 = ptr ∧ co ∈ chunks s ∧ co.used = true ∧ own co) ∧
    24 * c0 < 18446744073709551616 ∧ (len ≠ 0 → c0 ≠ 0) ∧ ptr + 24 * len + 8 ≤ 2147483648 ∧
    (∀ i, i < len → c i < 18446744073709551616 ∧ q i < 18446744073709551616) ∧
    (∀ i, i < len → c i ≠ 0 →
      (cs i).addr + 32 = q i ∧ cs i ∈ chunks s ∧ (cs i).used = true ∧ own (cs i) ∧ cs i ≠ co) ∧
    (∀ i i', i < len → i' < len → i ≠ i' → c i ≠ 0 → c i' ≠ 0 → cs i ≠ cs i') ∧
    (∀ a, ptr ≤ a → a < ptr + 24 * len → InData co a)

/-- `VVAt` survives a step that keeps the element's words (in `cb`) and every owned chunk with its data. -/
theorem VVAt.congr {μ μ' : Memory} {s s' : State} {el : Nat} {own : Chunk → Prop} {cb : Chunk}
    (hv : VVAt μ s el own) (hcbD : ∀ a, el ≤ a → a < el + 32 → InData cb a)
    (kcb : ∀ a, InData cb a → μ'.read a = μ.read a)
    (kp : ∀ d ∈ chunks s, d.used = true → own d → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    VVAt μ' s' el own := by
  obtain ⟨t, arm, head, nxt, back, ret, c0, ptr, len, c, q, cs, co, hv, e0, e8, e16, e24, hw, hco, hc01, hl0, hptr,
    hcq, hcs, hdist, hcoD⟩ := hv
  have rc : ∀ a l, el ≤ a → a + l ≤ el + 32 → μ'.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => kcb _ (hcbD _ (by omega) (by omega)))
  refine ⟨t, arm, head, nxt, back, ret, c0, ptr, len, c, q, cs, co, hv, by rw [rc _ _ (by omega) (by omega)]; exact e0,
    by rw [rc _ _ (by omega) (by omega)]; exact e8, by rw [rc _ _ (by omega) (by omega)]; exact e16,
    by rw [rc _ _ (by omega) (by omega)]; exact e24, fun i hi => ?_, fun h => ?_, hc01, hl0, hptr, hcq,
    fun i hi hci => ?_, hdist, hcoD⟩
  · obtain ⟨-, hcom, hcou, hown⟩ := hco (hl0 (by omega))
    have kco := (kp co hcom hcou hown).2
    obtain ⟨w1, w2⟩ := hw i hi
    exact ⟨by rw [Memory.readN_congr (fun j hj => kco _ (hcoD _ (by omega) (by omega)))]; exact w1,
      by rw [Memory.readN_congr (fun j hj => kco _ (hcoD _ (by omega) (by omega)))]; exact w2⟩
  · obtain ⟨a, hcom, hcou, hown⟩ := hco h
    exact ⟨a, (kp co hcom hcou hown).1, hcou, hown⟩
  · obtain ⟨a, hm, hu, ho, hne⟩ := hcs i hi hci
    exact ⟨a, (kp _ hm hu ho).1, hu, ho, hne⟩

/-- **A `LookedUp` element at el**: index 18, its `Option<Vec<u8>>` capacity c (2^64 − 1 for `None`) and buffer ptr at
    el + 8, el + 16; when c is neither 2^64 − 1 nor 0, the buffer is the data of an allocated chunk `ch` it owns. -/
def LUAt (μ : Memory) (s : State) (el : Nat) (own : Chunk → Prop) : Prop :=
  ∃ (c ptr : Nat) (ch : Chunk), μ.readN el 8 = Num.encodeLE 8 (9223372036854775807 + 18) ∧
    μ.readN (el + 8) 8 = Num.encodeLE 8 c ∧ μ.readN (el + 16) 8 = Num.encodeLE 8 ptr ∧ ptr < 18446744073709551616 ∧
    (c = 18446744073709551615 ∨ c = 0 ∨
      (c < 18446744073709551615 ∧ ch ∈ chunks s ∧ ch.used = true ∧ ch.addr + 32 = ptr ∧ own ch))

/-- An output element owning heap memory: a `DeleteItems` / `Imported` (`VVAt`) or a `LookedUp` (`LUAt`). -/
def HeapEl (μ : Memory) (s : State) (el : Nat) (own : Chunk → Prop) : Prop :=
  VVAt μ s el own ∨ LUAt μ s el own

theorem LUAt.congr {μ μ' : Memory} {s s' : State} {el : Nat} {own : Chunk → Prop} {cb : Chunk}
    (hv : LUAt μ s el own) (hcbD : ∀ a, el ≤ a → a < el + 32 → InData cb a)
    (kcb : ∀ a, InData cb a → μ'.read a = μ.read a)
    (kp : ∀ d ∈ chunks s, d.used = true → own d → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    LUAt μ' s' el own := by
  obtain ⟨c, ptr, ch, e0, e8, e16, hp, hc⟩ := hv
  have rc : ∀ a l, el ≤ a → a + l ≤ el + 32 → μ'.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => kcb _ (hcbD _ (by omega) (by omega)))
  refine ⟨c, ptr, ch, by rw [rc _ _ (by omega) (by omega)]; exact e0, by rw [rc _ _ (by omega) (by omega)]; exact e8,
    by rw [rc _ _ (by omega) (by omega)]; exact e16, hp, ?_⟩
  rcases hc with h | h | ⟨h1, hm, hu, ha, ho⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h1, (kp ch hm hu ho).1, hu, ha, ho⟩)

theorem HeapEl.congr {μ μ' : Memory} {s s' : State} {el : Nat} {own : Chunk → Prop} {cb : Chunk}
    (hv : HeapEl μ s el own) (hcbD : ∀ a, el ≤ a → a < el + 32 → InData cb a)
    (kcb : ∀ a, InData cb a → μ'.read a = μ.read a)
    (kp : ∀ d ∈ chunks s, d.used = true → own d → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    HeapEl μ' s' el own := by
  rcases hv with h | h
  · exact Or.inl (h.congr hcbD kcb kp)
  · exact Or.inr (h.congr hcbD kcb kp)

/-- **The output `Vec<Instruction>` dropped, with heap elements** (29087 … t): the slice of n ≥ 1 elements at E (from
    V + 8, V + 16), in the data of the allocated chunk `cb`, each of a variant whose drop does nothing or a heap element
    (`HeapEl`, owning `own j`; no chunk is owned by two elements, none is `cb`). Every owned chunk is freed; the function
    returns to `ret` (→ t) with ω₁, ω₅, ω₆ as they were. The heap context holds after; every allocated chunk owned by no
    element stays, with its data; the stack from sp up, the pages and the read-only bytes are kept. -/
theorem drop_vecH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] [HasCodeT1B p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (sp V E n ret t : Nat) (cb : Chunk) (own : Nat → Chunk → Prop)
    (hsp : 2147483716 + 80 ≤ sp ∧ S0 + 120 ≤ sp ∧ sp ≤ S1 ∧ sp % 8 = 0) (hV : V + 24 ≤ 4294967296)
    (hVs : V + 24 ≤ sp - 80 ∨ sp ≤ V) (hn : 0 < n)
    (H : HeapCtx env pb S0 S1 μ s) (cbm : cb ∈ chunks s) (cbu : cb.used = true)
    (hcbD : ∀ a, E ≤ a → a < E + 232 * n → InData cb a)
    (hown : ∀ j j' d, j < n → j' < n → j ≠ j' → own j d → own j' d → False)
    (hcbo : ∀ j, j < n → ¬ own j cb)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat V)
    (sV8 : μ.readN (V + 8) 8 = Num.encodeLE 8 E) (sV16 : μ.readN (V + 16) 8 = Num.encodeLE 8 n)
    (kinds : ∀ j, j < n → (∃ t, NoDrop t ∧ μ.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨
      HeapEl μ s (E + 232 * j) (own j))
    (tab : μ.readN 67760 96 = dtable) (hrt : ∀ a, 67760 ≤ a → a < 67856 → μ.readable a = true)
    (hrV : ∀ a, V + 8 ≤ a → a < V + 24 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ' s' N, FreeStepsH p R 29087 ω μ x t ω' μ' x N ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → (∀ j, j < n → ¬ own j d) → d ∈ chunks s' ∧
        ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) := by
  obtain ⟨hsp0, hsp1, hsp2, hsp8⟩ := hsp
  have hS := H.hS1
  have hEn : E + 232 * n ≤ 2147483648 := by
    have := data_lo H cbm cbu (hcbD (E + 232 * n - 1) (by omega) (by omega)); omega
  have hr0 : ω[0].toNat = ret := by rw [h0]; simp; omega
  have hwS : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a72, a64, a56, a40, a32, a24, a16, afr, ard, awr, a0⟩ := dh (p := p) (P := P)
    (R := R) x ω μ sp V E n ⟨by omega, by omega, hsp8⟩ hV hVs (by omega) (by omega) (by omega) h1 h7 sV8 sV16 hrV hwS
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H (fun a ha => afr a (by omega) (Or.inl (by omega))) awr
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => afr a (by omega) (Or.inl (by omega))
  have ro1 : ∀ b, b < two32 → μ.writable b = false → μ1.read b = μ.read b := fun b hb hwb => by
    refine afr b (by unfold two32 at hb; omega) ?_
    by_cases h : sp - 80 ≤ b ∧ b < sp
    · have := hwS b h.1 h.2; rw [hwb] at this; exact absurd this (by decide)
    · omega
  -- the hypotheses, in μ1
  have kinds1 : ∀ j, j < n → (∃ t, NoDrop t ∧ μ1.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)) ∨
      HeapEl μ1 s (E + 232 * j) (own j) := fun j hj => by
    rcases kinds j hj with ⟨tk, htk, hD⟩ | hvv
    · exact Or.inl ⟨tk, htk, by rw [Memory.readN_congr (fun i hi => lo1 _ (by omega))]; exact hD⟩
    · exact Or.inr (hvv.congr (cb := cb) (fun a h1 h2 => hcbD a (by omega) (by omega))
        (fun a ha => lo1 a (data_lo H cbm cbu ha))
        (fun d hd hu _ => ⟨hd, fun a ha => lo1 a (data_lo H hd hu ha)⟩))
  have tab1 : μ1.readN 67760 96 = dtable := by rw [Memory.readN_congr (fun i hi => lo1 _ (by omega))]; exact tab
  -- the element loop, from element k
  have loop : ∀ m k (ω2 : Regs) (μ2 : Memory) (s2 : State), k + m = n → k < n → ω2[1] = UInt64.ofNat (sp - 80) →
      ω2[5] = UInt64.ofNat n → ω2[6] = UInt64.ofNat k → HeapCtx env pb S0 S1 μ2 s2 →
      (∀ a, a < 4294967296 → sp - 80 ≤ a → (a < sp - 80 + 8 ∨ sp - 80 + 16 ≤ a) → (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) →
        μ2.read a = μ1.read a) →
      (∀ d ∈ chunks s, d.used = true → (∀ j, j < k → ¬ own j d) → d ∈ chunks s2 ∧
        ∀ a, InData d a → μ2.read a = μ1.read a) →
      (∀ a, μ2.readable a = μ1.readable a) → (∀ a, μ2.writable a = μ1.writable a) →
      (∀ b, b < two32 → μ1.writable b = false → μ2.read b = μ1.read b) →
      ∃ ω' μ' s' N, FreeStepsH p R 29188 ω2 μ2 x t ω' μ' x N ∧
        ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        HeapCtx env pb S0 S1 μ' s' ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ1.read a) ∧
        (∀ d ∈ chunks s, d.used = true → (∀ j, j < n → ¬ own j d) → d ∈ chunks s' ∧
          ∀ a, InData d a → μ'.read a = μ1.read a) ∧
        (∀ a, μ'.readable a = μ1.readable a) ∧ (∀ a, μ'.writable a = μ1.writable a) ∧
        (∀ b, b < two32 → μ1.writable b = false → μ'.read b = μ1.read b) := by
    intro m
    induction m with
    | zero => intro k _ _ _ hkm hk; omega
    | succ m ih =>
      intro k ω2 μ2 s2 hkm hk b1 b5 b6 H2 bfr bkp brd bwr bro
      have kr : ∀ a l, sp - 80 ≤ a → (a + l ≤ sp - 80 + 8 ∨ sp - 80 + 16 ≤ a) →
          (a + l ≤ sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → a + l ≤ 4294967296 → μ2.readN a l = μ1.readN a l :=
        fun a l h0 h h' h'' => Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega))
      have kcb := bkp cb cbm cbu (fun j _ => hcbo j (by omega))
      have rcb : ∀ a l, E ≤ a → a + l ≤ E + 232 * n → μ2.readN a l = μ1.readN a l :=
        fun a l h h' => Memory.readN_congr (fun j hj => kcb.2 _ (hcbD _ (by omega) (by omega)))
      have rdcb2 : ∀ a, E ≤ a → a < E + 232 * n → μ2.readable a = true := fun a h1 h2 =>
        Memory.readable_of_writable (Decode.VecU8.heap_writable H2 kcb.1 cbu (hcbD a h1 h2))
      have hrt2 : ∀ a, 67760 ≤ a → a < 67856 → μ2.readable a = true := fun a h1 h2 => by rw [brd, ard]; exact hrt a h1 h2
      have tab2 : μ2.readN 67760 96 = dtable := by
        rw [Memory.readN_congr (fun i hi => bro _ (by unfold two32; omega) (H1.ro _ (by omega)))]; exact tab1
      have f40 : μ2.readN (sp - 80 + 40) 8 = Num.encodeLE 8 E := by rw [kr _ _ (by omega) (by omega) (by omega) (by omega)]; exact a40
      have f32 : μ2.readN (sp - 80 + 32) 8 = Num.encodeLE 8 9223372036854775807 := by
        rw [kr _ _ (by omega) (by omega) (by omega) (by omega)]; exact a32
      have f24 : μ2.readN (sp - 80 + 24) 8 = Num.encodeLE 8 9223372036854775832 := by
        rw [kr _ _ (by omega) (by omega) (by omega) (by omega)]; exact a24
      have f16 : μ2.readN (sp - 80 + 16) 8 = Num.encodeLE 8 67760 := by
        rw [kr _ _ (by omega) (by omega) (by omega) (by omega)]; exact a16
      have f0 : μ2.readN (sp - 80) 8 = Num.encodeLE 8 n := by
        rw [kr _ _ (by omega) (by omega) (by omega) (by omega)]; exact a0
      -- after element k: at 29181 with the invariant for k + 1
      have next : ∀ (ω3 : Regs) (μ3 : Memory) (s3 : State) (N3 : Nat), FreeStepsH p R 29188 ω2 μ2 x 29181 ω3 μ3 x N3 →
          ω3[1] = ω2[1] → ω3[5] = ω2[5] → ω3[6] = ω2[6] → HeapCtx env pb S0 S1 μ3 s3 →
          (∀ a, a < 4294967296 → sp - 80 ≤ a → (a < sp - 80 + 8 ∨ sp - 80 + 16 ≤ a) →
            (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → μ3.read a = μ2.read a) →
          (∀ d ∈ chunks s2, d.used = true → ¬ own k d → d ∈ chunks s3 ∧ ∀ a, InData d a → μ3.read a = μ2.read a) →
          (∀ a, μ3.readable a = μ2.readable a) → (∀ a, μ3.writable a = μ2.writable a) →
          (∀ b, b < two32 → μ2.writable b = false → μ3.read b = μ2.read b) →
          ∃ ω' μ' s' N, FreeStepsH p R 29188 ω2 μ2 x t ω' μ' x N ∧
            ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
            HeapCtx env pb S0 S1 μ' s' ∧
            (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ1.read a) ∧
            (∀ d ∈ chunks s, d.used = true → (∀ j, j < n → ¬ own j d) → d ∈ chunks s' ∧
              ∀ a, InData d a → μ'.read a = μ1.read a) ∧
            (∀ a, μ'.readable a = μ1.readable a) ∧ (∀ a, μ'.writable a = μ1.writable a) ∧
            (∀ b, b < two32 → μ1.writable b = false → μ'.read b = μ1.read b) := by
        intro ω3 μ3 s3 N3 run3 c1 c5 c6 H3 cfr ckp crd cwr cro
        have e3 : ∀ a, a < 4294967296 → sp - 80 ≤ a → (a < sp - 80 + 8 ∨ sp - 80 + 16 ≤ a) →
            (a < sp - 80 + 48 ∨ sp - 80 + 56 ≤ a) → μ3.read a = μ1.read a :=
          fun a h0 h h' h'' => by rw [cfr a h0 h h' h'', bfr a h0 h h' h'']
        have kp3 : ∀ d ∈ chunks s, d.used = true → (∀ j, j < k + 1 → ¬ own j d) → d ∈ chunks s3 ∧
            ∀ a, InData d a → μ3.read a = μ1.read a := fun d hd hu hne => by
          obtain ⟨hd2, kd2⟩ := bkp d hd hu (fun j hj => hne j (by omega))
          obtain ⟨hd3, kd3⟩ := ckp d hd2 hu (hne k (by omega))
          exact ⟨hd3, fun a ha => by rw [kd3 a ha, kd2 a ha]⟩
        have rd3 : ∀ a, μ3.readable a = μ1.readable a := fun a => by rw [crd, brd]
        have wr3 : ∀ a, μ3.writable a = μ1.writable a := fun a => by rw [cwr, bwr]
        have ro3 := ro_trans bwr bro cro
        by_cases hlast : k + 1 = n
        · obtain ⟨ω4, run4, d0, d1, d5, d6⟩ := dl (p := p) (P := P) (R := R) x ω3 μ3 (sp - 80) k n ret
            ω[5].toNat ω[6].toNat t (by omega) hlast (by omega) (c1.trans b1) (c5.trans b5) (c6.trans b6)
            (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega) (by omega) (by omega)), a72, hr0])
            (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega) (by omega) (by omega))]; exact a64)
            (by rw [Memory.readN_congr (fun j hj => e3 _ (by omega) (by omega) (by omega) (by omega))]; exact a56)
            hret (UInt64.toNat_lt _) (UInt64.toNat_lt _) hjt hbt
            (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
          refine ⟨ω4, μ3, s3, N3 + 10, run3.trans run4, d0, by rw [d1]; congr 1; omega, by rw [d5]; simp,
            by rw [d6]; simp, H3, fun a h0 h => e3 a h0 (by omega) (by omega) (by omega),
            fun d hd hu hne => kp3 d hd hu (fun j hj => hne j (by omega)), rd3, wr3, ro3⟩
        · obtain ⟨ω4, run4, d1, d5, d6⟩ := dn (p := p) (P := P) (R := R) x ω3 μ3 k n (by omega) (by omega)
            (c5.trans b5) (c6.trans b6)
          obtain ⟨ω', μ', s', N, run', r0, r1, r5, r6, H', rfr, rkp, rrd, rwr, rro⟩ := ih (k + 1) ω4 μ3 s3 (by omega)
            (by omega) (by rw [d1, c1, b1]) (by rw [d5, c5, b5]) d6 H3 e3 kp3 rd3 wr3 ro3
          exact ⟨ω', μ', s', N3 + 2 + N, (run3.trans run4).trans run', r0, r1, r5, r6, H', rfr, rkp, rrd, rwr, rro⟩
      rcases kinds1 k hk with ⟨tk, htk, hD⟩ | hvv
      · obtain ⟨ω3, μ3, run3, c1, c5, c6, cfr, crd, cwr⟩ := dd (p := p) (P := P) (R := R) x ω2 μ2 (sp - 80) E k tk
          ⟨by omega, by omega, by omega⟩ htk (by omega) (Or.inl (by omega)) b1 b6 f40 f32 f24 f16
          (by rw [rcb _ _ (by omega) (by omega)]; exact hD) tab2 hrt2
          (fun a h1 h2 => rdcb2 a (by omega) (by omega))
          (fun a h1 h2 => H2.st a (by omega) (by omega))
        have lo3 : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a ha => cfr a (by omega) (Or.inl (by omega))
        refine next ω3 μ3 s2 20 run3 c1 c5 c6
          (Decode.GrowOne.ctx_high H2 lo3 cwr) (fun a h0 _ _ h => cfr a h0 h)
          (fun d hd hu _ => ⟨hd, fun a ha => lo3 a (data_lo H2 hd hu ha)⟩) crd cwr (fun b hb hwb => ?_)
        refine cfr b (by unfold two32 at hb; omega) ?_
        by_cases h : sp - 80 + 48 ≤ b ∧ b < sp - 80 + 56
        · have := H2.st b (by omega) (by omega); rw [hwb] at this; exact absurd this (by decide)
        · omega
      · have hel2 : HeapEl μ2 s2 (E + 232 * k) (own k) := hvv.congr (cb := cb)
          (fun a h1 h2 => hcbD a (by omega) (by omega)) kcb.2
          (fun d hd hu ho => bkp d hd hu (fun j hj hoj => hown j k d (by omega) hk (by omega) hoj ho))
        rcases hel2 with hvv2 | hlu2
        rotate_left
        · obtain ⟨c, ptr, ch, l0, l8, l16, lp, lc⟩ := hlu2
          have hco : c ≠ 0 → c ≠ 18446744073709551615 → own k ch := fun h0 hm => by
            rcases lc with h | h | ⟨-, -, -, -, ho⟩
            · exact absurd h hm
            · exact absurd h h0
            · exact ho
          obtain ⟨ω3, μ3, s3, N3, run3, c1, c5, c6, H3, cfr, ckp, crd, cwr, cro⟩ := drop_lu (p := p) (P := P) (R := R)
            env pb S0 S1 x ω2 μ2 s2 (sp - 80) E k c ptr ch cb ⟨by omega, by omega, by omega, by omega⟩ (by omega) lp
            (by rcases lc with h | h | ⟨h1, h2, h3, h4, -⟩
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩))
            (fun a h1 h2 => hcbD a (by omega) (by omega)) (fun h0 hm he => hcbo k hk (he ▸ hco h0 hm))
            b1 b6 H2 kcb.1 cbu f40 f32 f24 f16 l0 l8 l16 tab2 hrt2
          exact next ω3 μ3 s3 N3 run3 c1 c5 c6 H3 (fun a h0 h1 h2 h3 => cfr a h0 h1 h2 h3)
            (fun d hd hu hno => ckp d hd hu (fun h0 hm he => hno (he ▸ hco h0 hm))) crd cwr cro
        obtain ⟨tv, arm, head, nxt, back, rt, c0, ptr, len, c, q, cs, co, hv, e0, e8, e16, e24, hw, hco, hc01, hl0, hptr,
          hcq, hcs, hdist, hcoD⟩ := hvv2
        obtain ⟨ω3, μ3, s3, N3, run3, c1, c5, c6, H3, cfr, ckp, crd, cwr, cro⟩ := drop_vv (p := p) (P := P) (R := R)
          env pb S0 S1 x ω2 μ2 s2 (sp - 80) E k n tv arm head nxt back rt hv c0 ptr len c q cs co cb
          ⟨by omega, by omega, by omega, by omega⟩ (by omega) (by omega) (fun h => (hco h).1) hc01 hl0 hptr
          (fun i hi => (hcq i hi).1) (fun i hi => (hcq i hi).2) (fun i hi hci => (hcs i hi hci).1) hdist
          (fun i hi hci => (hcs i hi hci).2.2.2.2) hcoD (fun a h1 h2 => hcbD a (by omega) (by omega))
          (fun h he => hcbo k hk (he ▸ (hco h).2.2.2))
          (fun i hi hci he => hcbo k hk (he ▸ (hcs i hi hci).2.2.2.1))
          b1 b6 H2 kcb.1 cbu (fun h => ⟨(hco h).2.1, (hco h).2.2.1⟩)
          (fun i hi hci => ⟨(hcs i hi hci).2.1, (hcs i hi hci).2.2.1⟩)
          f0 f40 f32 f24 f16 e0 e8 e16 e24 hw tab2 hrt2
        exact next ω3 μ3 s3 N3 run3 c1 (by rw [c5, b5]) c6 H3 (fun a h0 h1 h2 h3 => cfr a h0 h1 h2 h3)
          (fun d hd hu hno => ckp d hd hu (fun h he => hno (he ▸ (hco h).2.2.2))
            (fun i hi hci he => hno (he ▸ (hcs i hi hci).2.2.2.1))) crd cwr cro
  obtain ⟨ω', μ', s', N, run', r0, r1, r5, r6, H', rfr, rkp, rrd, rwr, rro⟩ := loop n 0 ω1 μ1 s (by omega) hn a1 a5 a6 H1
    (fun _ _ _ _ _ => rfl) (fun d hd _ _ => ⟨hd, fun _ _ => rfl⟩) (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl)
  refine ⟨ω', μ', s', 20 + N, run1.trans run', r0, r1, r5, r6, H', fun a h0 h => by rw [rfr a h0 h, afr a h0 (Or.inr h)],
    fun d hd hu hne => ?_, fun a => by rw [rrd, ard], fun a => by rw [rwr, awr], ro_trans awr ro1 rro⟩
  obtain ⟨hd', kd'⟩ := rkp d hd hu hne
  exact ⟨hd', fun a ha => by rw [kd' a ha, lo1 a (data_lo H hd hu ha)]⟩

end Services.Bootstrap.Refine.DropVecH
