import Services.Bootstrap.Refine.PassGrow

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

/-- **The transform loop's state at 5042 after k instructions passed through.** -/
structure PInv (env : RefineHost.Env) (pb S0 S1 M E n : Nat) (ce : Chunk) (μ0 : Memory) (k : Nat) (ω : Regs)
    (μ : Memory) (s : State) : Prop where
  h1 : ω[1] = UInt64.ofNat M
  cur : μ.readN (M + 144) 8 = Num.encodeLE 8 (E + 232 * k)
  en : μ.readN (M + 120) 8 = Num.encodeLE 8 (E + 232 * n)
  c128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832
  c136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809
  out : ∃ cap ptr, μ.readN (M + 248) 8 = Num.encodeLE 8 cap ∧ μ.readN (M + 256) 8 = Num.encodeLE 8 ptr ∧
    μ.readN (M + 264) 8 = Num.encodeLE 8 k ∧ k ≤ cap ∧ cap ≤ 2 * n + 4 ∧ ptr < 2147483648 ∧
    (cap = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1 ∧
      c ≠ ce) ∧
    μ.readN ptr (232 * k) = μ0.readN E (232 * k)
  H : HeapCtx env pb S0 S1 μ s
  hce : ce ∈ chunks s ∧ ce.used = true
  data : ∀ a, InData ce a → μ.read a = μ0.read a

/-- What the loop needs of its layout: refine's frame M on the stack, the n < 128 instructions at E inside
    the allocated chunk `ce`, each of a kind passed through (as in μ0). -/
structure LayP (S0 S1 M E n : Nat) (ce : Chunk) (μ0 : Memory) : Prop where
  hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0
  hn : n < 128
  hE : ce.addr + 32 ≤ E ∧ E + 232 * n ≤ ce.addr + 32 * ce.size
  kinds : ∀ j, j < n → ∃ t, PassIdx t ∧ μ0.readN (E + 232 * j) 8 = Num.encodeLE 8 (9223372036854775807 + t)

/-- **One instruction passed through, with room in the output** (`k ≠ cap`): `PInv k` at 5042 becomes
    `PInv (k + 1)` at 5042. -/
theorem step_room {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) (s : State)
    {pb S0 S1 M E n : Nat} {ce : Chunk} (L : LayP S0 S1 M E n ce μ0) (k : Nat) (hk : k < n)
    (st : PInv env pb S0 S1 M E n ce μ0 k ω μ s)
    (hroom : ∀ cap, μ.readN (M + 248) 8 = Num.encodeLE 8 cap → k ≠ cap) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap0 env) 5042 ω μ x 5042 ω' μ' x 4000 ∧
      PInv env pb S0 S1 M E n ce μ0 (k + 1) ω' μ' s := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨hE0, hE1⟩ := L.hE
  obtain ⟨cap, ptr, vc, vp, vl, hkc, hcapn, hptr, hold, hout⟩ := st.out
  have hkc' := hroom cap vc
  obtain ⟨co, hco, hcoa, hcou, hcos, hcoe⟩ := hold.resolve_left (by omega)
  obtain ⟨hco0, -, hcoT⟩ := Decode.VecU8.chunk_in st.H.wf hco hcou
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have hap := chunk_apart st.H.wf hco st.hce.1 hcoe
  obtain ⟨t, ht, sD0⟩ := L.kinds k hk
  have inE : ∀ a, E ≤ a → a < E + 232 * n → InData ce a := fun a h1 h2 => ⟨by omega, by omega⟩
  have sD : μ.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + t) := by
    rw [Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]; exact sD0
  have hcs : 232 * cap + 32 ≤ 32 * co.size := by rw [hcos]; omega
  obtain ⟨ω', μ', run, e1, ecur, elen, eslot, een, e128, e136, ecap, eptr, efr, erd, ewr⟩ := pass_elem (p := p)
    (P := P) (R := refineContractK cap0 env) x ω μ M (E + 232 * k) (E + 232 * n) t cap ptr k ht
    ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) hkc' (by omega)
    ⟨by omega, by omega⟩ (by omega) (by omega) st.h1 st.cur st.en sD st.c128 st.c136 vc vp vl
    (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable st.H st.hce.1 st.hce.2
      (inE a (by omega) (by omega))))
    (fun a h1 h2 => st.H.st a (by omega) (by omega))
    (fun a h1 h2 => Decode.VecU8.heap_writable st.H hco hcou ⟨by omega, by omega⟩)
  have H' : HeapCtx env pb S0 S1 μ' s := Decode.VecU8.ctx_congr_data st.H hco
    (fun a ha h => efr a (by omega) (by omega) (by omega)) ewr
  refine ⟨ω', μ', run, ⟨e1, ecur, een, e128, e136, ⟨cap, ptr, ecap, eptr, elen, by omega, hcapn, hptr,
    Or.inr ⟨co, hco, hcoa, hcou, hcos, hcoe⟩, ?_⟩, H', st.hce, fun a ha => ?_⟩⟩
  · rw [show 232 * (k + 1) = 232 * k + 232 by omega, readN_add2, readN_add2, eslot,
      Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega)), hout,
      Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))]
  · unfold InData at ha
    rw [efr a (by omega) (by omega) (by omega), st.data a ha]

end Services.Bootstrap.Refine.PassLoop
