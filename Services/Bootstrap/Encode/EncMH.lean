import Services.Bootstrap.Encode.PrefixH
import Services.Bootstrap.Encode.EncMD

/-!
# The element contract with growth (`EncOkMH`), and the encoder over it

`EncMD.EncOkMD` assumes the writer has room for the element (`LayD.hroom`). `EncOkMH` is the contract
with growth, under refine's contract `refineContractK K env` (K ≥ 2²⁷):

* the layout `LayDH`: `LayD` without the room, the writer's buffer an allocated chunk of the allocator
  state s (`HeapCtx`), its capacity within `capBound`, the value slot kept by the appends (`SafeR`: on
  the stack at or above F, or in another allocated chunk), the stack `FrH`;
* the heap octets `Src q m` (stretches q … q + m) kept by the appends (`SafeR`);
* the conclusion: the element encodes (the octets appended: `BufH … enc`, from which the vector, the
  buffer's contents, the context and what is kept follow), or the run reaches a failed allocator call
  (`ExhaustsW`). Gas `encGas enc`.

`startH`, `startVH` (dispatch into `StH []` / `StDH []`), `closeH` (from `StH enc` at a tail) are the
arm's ends, from `Fixed.start`, `VecCore.startV` and the tails. `LayLMH`, `loopMH`, `restMH`,
`encode_okMH_big` are `EncMD`'s loop and encoder for `EncOkMH` elements, with no capacity hypothesis:
twice the output within `capBound` (`hbig`) is the top level's obligation.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Encode.Top Services.Bootstrap.Encode.Loop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## The contract -/

/-- **The layout of one `encode_to` call with growth** (frame base F, callees down to F − D). -/
structure LayDH (env : RefineHost.Env) (pb S0 S1 : Nat) (P : Program) (D F S v cap ptr len ret t : Nat)
    (s : State) (μ : Memory) : Prop where
  fr : FrH S0 S1 D F v
  hS : 65536 ≤ S
  hS' : S + 256 < 4294967296
  slot : SafeR s ptr F S1 v S 232
  vc : μ.readN v 8 = Num.encodeLE 8 cap
  vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr
  vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len
  hlc : len ≤ cap
  cpos : 0 < cap
  cb : cap ≤ capBound
  H : HeapCtx env pb S0 S1 μ s
  chunk : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = ptr ∧ cap ≤ 32 * (c.size - 1)
  hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0
  hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t
  hbt : P.isBlockStart t = true

/-- **One element encodes, with growth** (`Instruction::encode_to`, 30145; see the module doc). -/
def EncOkMH (env : RefineHost.Env) (K pb : Nat) (p : ByteArray) (P : Program) (D : Nat) (enc : List UInt8)
    (Rep : List UInt8 → Memory → Prop) (Src : Nat → Nat → Prop) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (S0 S1 F S v cap ptr len ret t : Nat),
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat F → ω[7] = UInt64.ofNat S → ω[8] = UInt64.ofNat v →
    Rep (μ.readN S 232) μ → LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ →
    2 * (len + enc.length) ≤ capBound →
    μ.readN 67376 100 = table → (∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) →
    (∀ q m, Src q m → SafeR s ptr F S1 v q m) →
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x t ω' μ' x (encGas enc) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ∃ cap' ptr' s', BufH env pb S0 S1 F v len ptr s μ enc cap' ptr' s' μ') ∨
    ExhaustsW env K pb p P 30145 ω μ x (encGas enc)

theorem LayDH.mono {env : RefineHost.Env} {pb S0 S1 : Nat} {P : Program} {D D' F S v cap ptr len ret t : Nat}
    {s : State} {μ : Memory} (L : LayDH env pb S0 S1 P D' F S v cap ptr len ret t s μ) (hD : D ≤ D') :
    LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ :=
  { L with fr := ⟨L.fr.hF8, by have := L.fr.hFS0; omega, by have := L.fr.hF2; omega, L.fr.hFv, L.fr.hvS1,
      L.fr.hS1⟩ }

/-- **`EncOkMH` is monotone in the stack depth.** -/
theorem EncOkMH.mono {env : RefineHost.Env} {K pb : Nat} {p : ByteArray} {P : Program} {D D' : Nat}
    {enc : List UInt8} {Rep : List UInt8 → Memory → Prop} {Src : Nat → Nat → Prop}
    (h : EncOkMH env K pb p P D enc Rep Src) (hD : D ≤ D') : EncOkMH env K pb p P D' enc Rep Src :=
  fun x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hl tab rt hs =>
    h x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep (L.mono hD) hl tab rt hs

/-- A kept stretch for a bound is kept for a smaller one. -/
theorem SafeR.mono {s : State} {ptr B B' S1 v q m : Nat} (h : SafeR s ptr B' S1 v q m) (hB : B ≤ B') :
    SafeR s ptr B S1 v q m := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨by omega, h2, h3⟩
  · exact Or.inr h

section
variable {env : RefineHost.Env} {pb S0 S1 : Nat} {P : Program} {D F S v cap ptr len ret t : Nat}
  {s : State} {μ : Memory}

/-- The buffer and the slot of a `LayDH` layout, numerically. -/
theorem LayDH.nums (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) :
    206896 ≤ ptr ∧ ptr + cap < 2147483648 ∧ S + 232 ≤ S1 ∧ 2147484072 + D ≤ F ∧ F ≤ v ∧ v + 24 ≤ S1 ∧
      S1 < 4294967296 ∧ S0 + D + 424 ≤ F ∧ F % 8 = 0 := by
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := L.chunk
  have := chunk_in L.H.wf hc hcu
  have := L.H.hb0; have := L.H.hbT; have := L.H.hS1; have := L.hlc; have := L.cpos
  have := L.fr.hF2; have := L.fr.hFv; have := L.fr.hvS1; have := L.fr.hFS0; have := L.fr.hF8
  have hS : S + 232 ≤ S1 := by
    rcases L.slot with ⟨h1, h2, h3⟩ | ⟨e, he, heu, -, h1, h2⟩
    · exact h2
    · have := chunk_in L.H.wf he heu; have := L.H.hSb; omega
  refine ⟨by omega, by omega, hS, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The writer at entry**, as `BufH` with nothing appended. -/
theorem LayDH.init (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) :
    BufH env pb S0 S1 F v len ptr s μ [] cap ptr s μ :=
  BufH.init L.fr.hvS1 L.vc L.vp L.vl L.hlc L.cpos L.cb L.H L.chunk

/-- The slot lies apart from the buffer, and below the frame or above F. -/
theorem LayDH.slot_apart (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) :
    (ptr + cap + 24 ≤ S ∨ S + 256 ≤ ptr) ∧ (S + 256 ≤ F - D ∨ F ≤ S) ∧ (v + 24 ≤ S ∨ S + 232 ≤ v) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, -⟩ := L.nums
  rcases L.slot with ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
  · refine ⟨Or.inl (by omega), Or.inr h1, by omega⟩
  · obtain ⟨c, hc, hcu, hcp, hcc⟩ := L.chunk
    have hce : c ≠ e := fun h => hne (by rw [← h]; exact hcp)
    have := chunk_in L.H.wf hc hcu
    have := L.hlc; have := L.cpos
    have ht := L.H.wf.2.2.2.1
    unfold TilesOk at ht
    have := chunk_in L.H.wf he heu
    have := L.H.hbT
    rcases Services.Bootstrap.Decode.HeapFrame.Tiles.disjoint ht c hc e he hce with h | h
    · exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inr (by omega)⟩
    · exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inr (by omega)⟩

/-- The slot is readable. -/
theorem LayDH.rS (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) :
    ∀ a, S ≤ a → a < S + 232 → μ.readable a = true := by
  have := L.fr.hFS0
  intro a h1 h2
  rcases L.slot with ⟨b1, b2, -⟩ | ⟨e, he, heu, -, e1, e2⟩
  · exact Memory.readable_of_writable (L.H.st a (by omega) (by omega))
  · exact Memory.readable_of_writable (heap_writable L.H he heu ⟨by omega, by omega⟩)

/-- **`LayDH` gives `Fixed`'s `Lay` for no octets**, for the dispatch (`Fixed.start`). -/
theorem LayDH.toLay0 (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) (hD : 136 ≤ D) :
    Lay P F S v cap ptr len 0 ret t μ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨a1, a2, a3⟩ := L.slot_apart
  have hst := L.H.st
  have hlc := L.hlc
  exact
    { hF := (by omega), hF' := (by omega), hF8 := n9, hS := L.hS, hS' := L.hS', hSF := (by omega),
      vc := L.vc, vp := L.vp, vl := L.vl, hroom := (by have := L.hlc; omega), hcap := (by have := L.hlc; omega),
      hv := (by omega), hvF := Or.inr n5, hvS := a3, hd := (by omega), hd' := (by omega), hdF := (by omega),
      hdS := (by have := L.hlc; omega), hdv := (by have := L.hlc; omega), hret := L.hret, hjt := L.hjt,
      hbt := L.hbt, hrS := L.rS,
      hrv := fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      hwv := fun a h1 h2 => hst a (by omega) (by omega), hwd := fun a h1 h2 => by omega,
      hwF := fun a h1 h2 => hst a (by omega) (by omega) }

/-- **`LayDH` gives `LayD` for no octets**, for the dispatch (`VecCore.startV`). -/
theorem LayDH.toLayD0 (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) :
    LayD P D F S v cap ptr len 0 ret t μ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨a1, a2, a3⟩ := L.slot_apart
  have hst := L.H.st
  have hlc := L.hlc
  exact
    { hF := (by omega), hF' := (by omega), hF8 := n9, hS := L.hS, hS' := L.hS', hSF := a2,
      vc := L.vc, vp := L.vp, vl := L.vl, hroom := (by have := L.hlc; omega), hcap := (by have := L.hlc; omega),
      hv := (by omega), hvF := Or.inr n5, hvS := a3, hd := (by omega), hd' := (by omega), hdF := (by omega),
      hdS := (by have := L.hlc; omega), hdv := (by have := L.hlc; omega), hret := L.hret, hjt := L.hjt,
      hbt := L.hbt, hrS := L.rS,
      hrv := fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      hwv := fun a h1 h2 => hst a (by omega) (by omega), hwd := fun a h1 h2 => by omega,
      hwF := fun a h1 h2 => hst a (by omega) (by omega) }

end

/-- A word written back with its own value: memory kept pointwise there. -/
theorem keep_vl {μ μ' : Memory} {v len : Nat} {Q : Nat → Prop}
    (vl' : μ'.readN (v + 16) 8 = Num.encodeLE 8 len) (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (k : ∀ a, Q a → (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) : ∀ a, Q a → μ'.read a = μ.read a := by
  intro a ha
  by_cases h : v + 16 ≤ a ∧ a < v + 24
  · have e1 := Memory.read_of_readN vl' (a - (v + 16)) (by omega)
    have e2 := Memory.read_of_readN vl (a - (v + 16)) (by omega)
    rw [show v + 16 + (a - (v + 16)) = a by omega] at e1 e2
    rw [e1, e2]
  · exact k a ha (by omega)

/-! ## The arm's ends -/

/-- **From 30145 to the arm of a fixed-width variant** (discriminant word 2^63 + t − 1), in `StH []`,
    the writer in ω₁₀ and the value in ω₁₁ (`Fixed.start`). -/
theorem startH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (K : Nat) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t' : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t' s μ) (hD : 136 ≤ D) (t : Nat) (ht : 1 ≤ t ∧ t < 25)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p (refineContractK K env) 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ [] ω1 μ1 ∧ ω1[10] = UInt64.ofNat v ∧
      ω1[11] = UInt64.ofNat S := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := start (p := p) (P := P) (R := refineContractK K env) x ω μ
    (L.toLay0 hD) t ht h0 h1 h7 h8 hD8 tab hrt
  have hk := keep_vl (Q := fun a => a < 4294967296 ∧ (a < F - 136 ∨ F ≤ a)) (by simpa using st1.vl) L.vl
    (fun a ha h => st1.keep a ha.1 ha.2 (by simp; omega) h)
  exact ⟨ω1, μ1, run1, ⟨st1.h1, st1.s0, st1.s5, st1.s6, ⟨cap, ptr, s,
    L.init.frame (F - 136) F (by omega) (Nat.le_refl _) (Or.inl n5) (fun a h0 h1 => hk a ⟨h0, h1⟩) st1.rd st1.wr⟩⟩,
    a10, a11⟩

/-- **From 30145 to the arm of `LookedUp` (18) or `Imported` (19)**, in `StDH []`, ω₅ = 2^64 − 1
    (`VecCore.startV`). -/
theorem startVH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (K : Nat) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t' : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t' s μ) (hD : 136 ≤ D) (t : Nat) (ht : t = 18 ∨ t = 19)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p (refineContractK K env) 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StDH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ [] ω1 μ1 ∧
      ω1[5] = UInt64.ofNat 18446744073709551615 ∧ ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startV (p := p) (P := P) (R := refineContractK K env) x ω μ
    L.toLayD0 hD t ht h0 h1 h7 h8 hD8 tab hrt
  have hk := keep_vl (Q := fun a => a < 4294967296 ∧ (a < F - D ∨ F ≤ a)) (by simpa using st1.vl) L.vl
    (fun a ha h => st1.keep a ha.1 ha.2 (by simp; omega) h)
  exact ⟨ω1, μ1, run1, ⟨⟨st1.h1, st1.s0, st1.s5, st1.s6, ⟨cap, ptr, s,
    L.init.frame (F - D) F (by omega) (Nat.le_refl _) (Or.inl n5) (fun a h0 h1 => hk a ⟨h0, h1⟩) st1.rd st1.wr⟩⟩,
    st1.sv⟩, a5, a10, a11⟩

/-- **Closing a variant, with growth**: from `StH enc` at one of the function's ends, after a run from
    30145 of k steps (k + 7 ≤ `encGas enc`), `EncOkMH`'s success. -/
theorem closeH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] {K : Nat} {x : RefineCtx}
    {ω ω5 : Regs} {μ μ5 : Memory} {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t : Nat} {s : State}
    {enc : List UInt8} (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ)
    (e k : Nat) (he : e = 20155 ∨ e = 20204 ∨ e = 20329 ∨ e = 20383 ∨ e = 19636 ∨ e = 20118)
    (hk : k + 7 ≤ encGas enc) (run : FreeStepsH p (refineContractK K env) 30145 ω μ x e ω5 μ5 x k)
    (st : StH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ enc ω5 μ5) :
    ∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x t ω' μ' x (encGas enc) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ∃ cap' ptr' s', BufH env pb S0 S1 F v len ptr s μ enc cap' ptr' s' μ' := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨cap', ptr', s', W⟩ := st.buf
  have hr : ∀ a, F - 56 + 32 ≤ a → a < F - 56 + 56 → μ5.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (W.H.st a (by omega) (by omega))
  have s0 : μ5.readN (F - 56 + 48) 8 = Num.encodeLE 8 ret := by rw [show F - 56 + 48 = F - 8 by omega]; exact st.w0
  have s5 : μ5.readN (F - 56 + 40) 8 = Num.encodeLE 8 ω[5].toNat := by
    rw [show F - 56 + 40 = F - 16 by omega]; exact st.w5
  have s6 : μ5.readN (F - 56 + 32) 8 = Num.encodeLE 8 ω[6].toNat := by
    rw [show F - 56 + 32 = F - 24 by omega]; exact st.w6
  have fin : ∃ ω6, FreeStepsH p (refineContractK K env) e ω5 μ5 x t ω6 μ5 x 7 ∧ ω6[0] = UInt64.ofNat ret ∧
      ω6[1] = UInt64.ofNat (F - 56 + 56) ∧ ω6[5] = UInt64.ofNat ω[5].toNat ∧
      ω6[6] = UInt64.ofNat ω[6].toNat := by
    rcases he with he | he | he | he | he | he
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t
        _ _ (Or.inl he) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t
        _ _ (Or.inr (Or.inl he)) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt
        L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t
        _ _ (Or.inr (Or.inr (Or.inl he))) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t
        _ _ (Or.inr (Or.inr (Or.inr he))) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · exact tailV (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t _ _ (Or.inl he)
        (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
    · exact tailV (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 e (F - 56) ret t _ _ (Or.inr he)
        (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
  obtain ⟨ω6, run6, e0, e1, e5, e6⟩ := fin
  exact ⟨ω6, μ5, (run.trans run6).mono hk, e0, by rw [e1]; congr 1; omega,
    by rw [e5]; exact UInt64.ofNat_toNat, by rw [e6]; exact UInt64.ofNat_toNat, cap', ptr', s', W⟩

end Services.Bootstrap.Encode.GrowH
