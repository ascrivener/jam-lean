import Services.Bootstrap.Encode.EncMH

/-!
# An arm proved without growth, run where no growth happens

`EncOkMD.runH`: an element proved as `EncOkMD` (no growth, any host) gives, under `LayDH` and with room
for its encoding (len + |enc| ≤ cap), `EncOkMH`'s success: the same run under refine's contract, the
octets appended, and the writer as `BufH` (buffer, capacity and allocator state unchanged). An arm not
yet converted to `EncOkMH` can so be used wherever its writer has room.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Encode.Enc Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `LayDH` with room for N octets is `LayD`. -/
theorem LayDH.toLayD {env : RefineHost.Env} {pb S0 S1 : Nat} {P : Program} {D F S v cap ptr len ret t N : Nat}
    {s : State} {μ : Memory} (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) (hroom : len + N ≤ cap) :
    LayD P D F S v cap ptr len N ret t μ := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨a1, a2, a3⟩ := L.slot_apart
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := L.chunk
  have hst := L.H.st
  have hlc := L.hlc
  exact
    { hF := (by omega), hF' := (by omega), hF8 := n9, hS := L.hS, hS' := L.hS', hSF := a2,
      vc := L.vc, vp := L.vp, vl := L.vl, hroom := hroom, hcap := (by omega),
      hv := (by omega), hvF := Or.inr n5, hvS := a3, hd := (by omega), hd' := (by omega), hdF := (by omega),
      hdS := (by omega), hdv := (by omega), hret := L.hret, hjt := L.hjt,
      hbt := L.hbt, hrS := L.rS,
      hrv := fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)),
      hwv := fun a h1 h2 => hst a (by omega) (by omega),
      hwd := fun a h1 h2 => heap_writable L.H hc hcu (show InData c a from ⟨by omega, by omega⟩),
      hwF := fun a h1 h2 => hst a (by omega) (by omega) }

/-- **An `EncOkMD` element where its writer has room**, under refine's contract: `EncOkMH`'s success. -/
theorem EncOkMD.runH {p : ByteArray} {P : Program} {D : Nat} {enc : List UInt8}
    {Rep : List UInt8 → Memory → Prop} {Src : Nat → Prop} (h : EncOkMD p P D enc Rep Src)
    {env : RefineHost.Env} (K : Nat) {pb : Nat} (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    {S0 S1 F S v cap ptr len ret t : Nat}
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (rep : Rep (μ.readN S 232) μ)
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) (hroom : len + enc.length ≤ cap)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true)
    (hsrc : ∀ a, Src a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + enc.length ≤ a) ∧ (a < v ∨ v + 24 ≤ a)) :
    ∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x t ω' μ' x (encGas enc) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ∃ cap' ptr' s', BufH env pb S0 S1 F v len ptr s μ enc cap' ptr' s' μ' := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := L.chunk
  have hci := chunk_in L.H.wf hc hcu
  have hb0 := L.H.hb0; have hbT := L.H.hbT; have hSb := L.H.hSb
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eo, el, efr, erd, ewr⟩ :=
    h RefineCtx (refineContractK K env) x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep (L.toLayD hroom) tab hrt hsrc
  have kl : ∀ a, a < 2147483648 → (a < ptr + len ∨ ptr + len + enc.length ≤ a) → μ'.read a = μ.read a :=
    fun a h0 h1 => efr a (by omega) (Or.inl (by omega)) h1 (Or.inl (by omega))
  refine ⟨ω', μ', run.mono (by unfold encGas; omega), e0, e1, e5, e6, cap, ptr, s,
    ⟨L.fr.hvS1, ?_, ?_, el, ?_, hroom, L.cpos, L.cb, ?_, ⟨c, hc, hcu, hcp, hcc⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Memory.readN_congr (fun j hj => efr (v + j) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega))) |>.trans L.vc
  · exact Memory.readN_congr (fun j hj => efr (v + 8 + j) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega))) |>.trans L.vp
  · rw [readN_add', eo, Memory.readN_congr (fun j hj => kl (ptr + j) (by omega) (Or.inl (by omega)))]
  · exact ctx_congr_data L.H hc (fun a h0 h1 => kl a h0 (by omega)) ewr
  · intro e he heu hne
    have hec : e ≠ c := fun h => hne (by rw [h]; exact hcp)
    refine ⟨he, hne, fun a ha => ?_⟩
    have hca := ha
    unfold InData at hca
    have := chunk_in L.H.wf he heu
    have hdd := data_disj L.H.wf he hc hec ha
    exact kl a (by omega) (by omega)
  · intro a _; exact ⟨erd a, ewr a⟩
  · intro a ha; exact kl a (by omega) (Or.inl (by omega))
  · intro a ha; unfold Glob at ha; exact kl a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2; exact efr a h0 (Or.inr h1) (Or.inr (by omega)) (by omega)

end Services.Bootstrap.Encode.GrowH
