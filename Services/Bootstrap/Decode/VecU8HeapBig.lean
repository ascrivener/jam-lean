import Services.Bootstrap.Decode.ReallocCall
import Services.Bootstrap.Decode.VecU8Pass

/-!
# Reading more than 16384 octets into a fresh `Vec<u8>`, the payload in the heap

`vec_u8_heap_big` is `VecU8.vec_u8_big` in the decode loop's setting (as `vec_u8_heap` is
`vec_u8_small` there): the payload lies inside an allocated chunk of the heap, the allocator's
context is `HeapCtx`, the run is under `refineContractK cap` (cap ≥ 2²⁷). `read_vec` (3473) reads
the first 16384 octets into a block from `alloc` (`HeapCtx.alloc_call`), then its chunk loop (3520)
grows the buffer to L + min(left, L) octets with `realloc` (`ReallocCall.realloc_call`) and reads
the next min(left, L) octets, until all n are read.

The loop's invariant (`loop_heap`): L octets read into the buffer q, the data of an allocated chunk
of ⌈L/32⌉ + 1 units; a set `K` of protected chunks (in the composed theorem: the allocated chunks of
the state before `read_vec`), each allocated and not q's, one of them holding the payload; `HeapCtx`.
`realloc` keeps every other allocated chunk with its data (`OthersData`), so the protected chunks
and the payload survive; its new block is q's chunk grown in place or a block that was free
(`realloc_fresh`), so it is never a protected chunk; its copy clause keeps the L octets read.

Either `read_vec` returns, or the run reaches a failed allocator call (`LoopA.Exhausts`): the
`alloc` of the first chunk or one of the `realloc`s fails (heap exhaustion, bootstrap decision 4).

Not stated (unlike `vec_u8_heap`): the globals below the allocator (`Glob`) are kept. `realloc_call`
does not record it, so the composed run cannot carry it through the `realloc`s.

GP v0.8.0: the octets are read from the service's memory by the PVM (Appendix A); the
`Vec<u8>` is the bootstrap service's own decoding of an argument blob.
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`realloc`'s block is the old one or was free** (alignment one unit, a nonzero request, the
    data address of an allocated chunk): no other allocated chunk of `s` has its data at the result. -/
theorem realloc_fresh {grow : Grow} {hb : Nat} {s s' : State} {ptr newReq p : Nat} {cp : Bool} (hwf : WF s)
    (hptr : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (h0 : newReq ≠ 0)
    (h : realloc grow hb s ptr 1 newReq = some (p, s', cp)) :
    ∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d.addr + 32 ≠ p := by
  intro d hd hdu hda
  obtain ⟨c, hc, h1, h2⟩ := hptr
  have hcur : wordSize (s.hdr (ptr - 32)).size = c.size := by
    have := chunks_hdr c hc
    rw [show c.addr = ptr - 32 by omega, h2] at this
    rw [this, wordSize_sizeWord]
  unfold realloc usable at h
  rw [hcur] at h
  by_cases e1 : newReq = c.size - 1
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, -, -⟩ := h
    rw [← hp]; exact hda
  by_cases e3 : newReq < c.size - 1
  · simp only [e1, h0, e3, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, -, -⟩ := h
    rw [← hp]; exact hda
  simp only [e1, h0, e3, ↓reduceIte] at h
  cases hg : growInplace grow s ptr newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hp, -, -⟩ := h
    rw [← hp]; exact hda
  | none =>
    simp only [hg] at h
    cases ha : alloc grow hb 1 newReq s with
    | none => simp [ha] at h
    | some r =>
      obtain ⟨p1, s1⟩ := r
      simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨hp, -, -⟩ := h
      rw [← hp]
      obtain ⟨pre, post, S, hcs, -, -⟩ := alloc_chunks hwf ha
      intro e
      have ht := hwf.2.2.2.1
      unfold TilesOk at ht
      rw [hcs] at ht hd
      have hfree : (⟨p1 - 32, S, false⟩ : Chunk) ∈ pre ++ ⟨p1 - 32, S, false⟩ :: post :=
        List.mem_append_right _ List.mem_cons_self
      have := Tiles.addr_inj ht d hd _ hfree (by simp only; omega)
      rw [this] at hdu; simp at hdu

/-- **One pass of `read_vec`'s chunk loop, the payload in the heap** (3520 …): as `pass_ok` /
    `pass_fail`, on the allocator's context `HeapCtx` under `refineContractK cap`. From L ≥ 1 octets
    read into the buffer q (an allocated chunk of ⌈L/32⌉ + 1 units) with `left` ≥ 1 to go, and the
    payload ptr0 … ptr0 + L + left inside a protected chunk (`K`: allocated, not q's): either the
    model's `realloc` of q to ⌈(L + c)/32⌉ units (c = min(left, L)) gives a block r and state `s'`,
    and the pass reaches 3635 with r holding the payload's first L + c octets, the context kept for
    `s'`, r's chunk allocated of ⌈(L + c)/32⌉ + 1 units, every protected chunk still allocated in
    `s'`, not r's, with its data; or the run reaches a failed `realloc` (`Exhausts`). -/
theorem pass_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    (hb : Nat) (s : State) (K : Chunk → Prop) (S rd q L left ptr0 len pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ c ∈ chunks s, c.addr + 32 = q ∧ c.used = true ∧ c.size = (L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ c, K c ∧ c.addr + 32 ≤ ptr0 ∧ ptr0 + L + left ≤ c.addr + 32 * c.size)
    (hS : S0 + 360 ≤ S ∧ S + 96 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat left)
    (hL : 1 ≤ L) (hl1 : 1 ≤ left) (hn : L + left < 1073741760) (hlen : left ≤ len ∧ len < 4294967296)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 rd) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q)
    (hrd : S + 96 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + L)) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hdat : μ.readN q L = μ.readN ptr0 L) :
    (∃ ω' μ' s' r, FreeStepsH p (refineContractK cap env) 3520 ω μ x 3635 ω' μ' x
        (64 * ((L + 31) / 32) + 2 * min left L + 1800) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat L ∧ ω'[6] = UInt64.ofNat (min left L) ∧
      ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 left ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 (L + min left L) ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (S + 8 ≤ a ∧ a < S + 24 ∨ S + 72 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + L + min left L) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - min left L) ∧
      μ'.readN r (L + min left L) = μ.readN ptr0 (L + min left L) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ c ∈ chunks s', c.addr + 32 = r ∧ c.used = true ∧ c.size = (L + min left L + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
        ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 3520 ω μ x (64 * ((L + 31) / 32) + 1400) := by
  generalize hcdef : min left L = c at *
  have hc1 : 1 ≤ c ∧ c ≤ left ∧ c ≤ L := by omega
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpm, hcpu, hcpq⟩ := hK cp hcpK
  have hu : usable s q = (L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨hp0, -, hpT⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  -- the loop's head, and finish_grow to realloc
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m32, m0, fr1, rd1, wr1⟩ :=
    lh (p := p) (P := P) (R := refineContractK cap env) x ω μ S L left q ⟨by omega, by omega⟩ h1 h5 h7 h8 h10
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ (by omega) s24 (fun a h1 h2 => hst a (by omega) (by omega))
  rw [hcdef] at a6 a10 m0
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (S - 40) (S + 48) L q (L + c) 88 L (L + c)
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 72 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcqm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (S - 40) q 1 (L + c) pb S0 S1 H2
      ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr (Exhausts.of_realloc ((run1.trans (run2.trans (run3.trans run4))).mono (by omega)) e7 hR)
  have hR1 : realloc (growTo pb) hb s q 1 ((L + c + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hcp' := keep3 cp hcpm hcpu hcpq
  have hcpr : cp.addr + 32 ≠ r := hfr cp hcpm hcpu hcpq
  have hcpne : cp ≠ cr := fun e => hcpr (by rw [e]; exact hcra)
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (S - 40) (S + 48) (L + c) r 88 3600 L (L + c)
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 48 ∨ S + 72 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  have hS50 : ∀ a, S ≤ a → a < 4294967296 → (S + 8 ≤ a ∧ a < S + 32 ∨ S + 72 ≤ a) →
      μ5.read a = μ.read a :=
    fun a h1 h2 h3 => (hS51 a h1 h2 (by omega)).trans (fr1 a h2 (by omega) (by omega))
  -- read_vec: the call of the reader
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2g (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 S rd r (L + c) L c ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega) (by omega)
      cres (by rw [show S + 56 = S + 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m0)
      (by rw [Memory.readN_congr (fun j hj => hS50 _ (by omega) (by omega) (by omega))]; exact s16)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hhigh : ∀ a, a < 4294967296 → S + 72 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans (hS50 a (by omega) h0 (Or.inr h1))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha => by
    have hca := ha
    unfold InData at hca
    rw [h63 a (by omega), kp3 a ⟨cp, hcpm, hcpu, hcpq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, r + L ≤ a → a < r + L + c → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact heap_writable H3 hcrm hcru ⟨by omega, by rw [hcrs]; omega⟩
  have hdq : r + L + c + 24 ≤ ptr0 + L ∨ ptr0 + L + c + 24 ≤ r + L := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' cr hcrm hcpne with h' | h' <;> omega
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_low (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 90 3635 S rd (r + L) (ptr0 + L) len c
      d0 d1 d7 d8 d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, hsp.2⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hc1.1 (by omega) hlen.2 (by omega) hdq
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega)) hwq
      (fun a h1 h2 => Memory.readable_of_writable
        (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  -- the results
  have h76 : ∀ a, S ≤ a → a < S + 96 → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr h1) (Or.inl (by omega)) (Or.inr (by omega))
  have h71 : ∀ a, S ≤ a → a < S + 96 → (a < S + 24 ∨ S + 32 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) →
      (a < S + 48 ∨ S + 72 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (h76 a h1 h2).trans ((fr6 a (by omega) h3 h4).trans (hS51 a h1 (by omega) h5))
  have hlowh : ∀ a, a < 2147483648 → (a < r + L ∨ r + L + c ≤ a) → μ7.read a = μ3.read a :=
    fun a h2 h3 => (fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans (h63 a h2)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [wr7, wr36]
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  refine Or.inl ⟨ω7, μ7, s', r, run17.mono (by omega), by rw [r1, d1], by rw [r5, d5], by rw [r6, d6], r7,
    ?_, ?_, ?_, ?_, rR0, rR8, ?_,
    ctx_congr_data H3 hcrm (fun a h1 h2 => hlowh a h1 (by rw [hcrs] at h2; omega)) wr73,
    ⟨cr, hcrm, hcra, hcru, hcrs⟩, ?_⟩
  · rw [Memory.readN_congr (fun j hj => h71 _ (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact m32
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact dn
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact dq
  · intro a h0 h1 h2
    exact (fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))).trans
      ((fr6 a h0 (by omega) (by omega)).trans (hS50 a (by omega) h0 (by omega)))
  · rw [readN_split, readN_split, rbuf]
    congr 1
    · rw [Memory.readN_congr (fun j hj => hlowh _ (by omega) (by omega))]
      rw [readN_prefix (by omega) dat3, Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega)))]
      exact hdat
    · exact Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)
  · intro d hd
    obtain ⟨hdm, hdu, hdq'⟩ := hK d hd
    have hdm' := keep3 d hdm hdu hdq'
    have hdr : d.addr + 32 ≠ r := hfr d hdm hdu hdq'
    have hdne : d ≠ cr := fun e => hdr (by rw [e]; exact hcra)
    refine ⟨hdm', hdu, hdr, fun a ha => ?_⟩
    have hdis := data_disj H3.wf hdm' hcrm hdne ha
    rw [hcrs] at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hdm hdu).2.2
    rw [hlowh a (by omega) (by omega), kp3 a ⟨d, hdm, hdu, hdq', ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))

/-- **`read_vec`'s chunk loop, the payload in the heap** (from 3520 to `read_vec`'s return t): as
    `loop`, on `HeapCtx` under `refineContractK cap`, with the protected chunks `K` (allocated, none
    q's, one holding the payload ptr0 … ptr0 + L + left). Either the loop returns to t with the `Vec`
    `{cap L + left, ptr q', len L + left}` at O, q' holding the payload's first L + left octets and
    being the data of an allocated chunk of exactly ⌈(L + left)/32⌉ + 1 units, the context kept for
    the final state, every protected chunk still allocated, not q''s, with its data, and memory from
    S + 96 up kept off the reader and O; or the run reaches a failed `realloc` (`Exhausts`). -/
theorem loop_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    (hb : Nat) (s : State) (K : Chunk → Prop) (S O rd q L left ptr0 len ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ c ∈ chunks s, c.addr + 32 = q ∧ c.used = true ∧ c.size = (L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ c, K c ∧ c.addr + 32 ≤ ptr0 ∧ ptr0 + L + left ≤ c.addr + 32 * c.size)
    (hS : S0 + 360 ≤ S ∧ S + 96 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat left)
    (hL : 1 ≤ L) (hl1 : 1 ≤ left) (hn : L + left < 1073741760) (hlen : left ≤ len ∧ len < 4294967296)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 O)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 rd) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q)
    (s88 : μ.readN (S + 88) 8 = Num.encodeLE 8 ret) (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 v5)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : S + 96 ≤ rd ∧ rd + 16 ≤ S1) (hO : S + 96 ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + L)) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hdat : μ.readN q L = μ.readN ptr0 L) :
    (∃ ω' μ' s' q', FreeStepsH p (refineContractK cap env) 3520 ω μ x t ω' μ' x (loopSteps L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN q' (L + left) = μ.readN ptr0 (L + left) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + L + left) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - left) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ c ∈ chunks s', c.addr + 32 = q' ∧ c.used = true ∧ c.size = (L + left + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → S + 96 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 3520 ω μ x (loopSteps L left) := by
  induction left using Nat.strongRecOn generalizing ω μ s q L len with
  | _ left ih =>
  have hX : 64 * ((L + 31) / 32) ≤ 2 * L + 62 := by omega
  have hS1 := H.hS1
  rcases pass_heap (p := p) (P := P) env cap hcap1 hcap x ω μ hb s K S rd q L left ptr0 len pb S0 S1 H hcq hK hpay
      hS hsp h1 h5 h7 h8 h10 hL hl1 hn hlen s16 s24 hrd hR0 hR8 hdat with
    ⟨ω1, μ1, s', r, run1, a1, a5, a6, a7, m32, m40, m24, fr1, rR0, rR8, dat1, H1, hc1, hK1⟩ | hex
  rotate_left
  · exact Or.inr (hex.mono (by unfold loopSteps; omega))
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  generalize hcdef : min left L = c at *
  have hc : 1 ≤ c ∧ c ≤ left ∧ c ≤ L ∧ (c < left → c = L) := by omega
  have hS1r : ∀ a, S ≤ a → a < S + 96 → (S + 8 ≤ a ∧ a < S + 24 ∨ S + 72 ≤ a) → μ1.read a = μ.read a :=
    fun a h1 h2 h3 => fr1 a (by omega) h3 (Or.inl (by omega))
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + L + left → μ1.read a = μ.read a := fun a h1 h2 =>
    (hK1 cp hcpK).2.2.2 a ⟨by omega, by omega⟩
  have hrd1 : ∀ a, S ≤ a → a < S + 96 → μ1.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (H1.st a (by omega) (by omega))
  rcases Classical.em (c < left) with hlt | hlt
  · -- the back edge, and the rest of the loop
    have hcL : c = L := hc.2.2.2 hlt
    obtain ⟨ω2, run2, b1, b5, b7, b8, b10, -⟩ :=
      Services.Bootstrap.Decode.VecU8.v5 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 S L c left
        (L + c) ⟨by omega, by omega⟩ a1 a5 a6 a7 ⟨hlt, by omega⟩ (by omega) (by omega) m32 m40 hrd1
    have hrec := ih (left - c) (by omega) ω2 μ1 s' r (L + c) (len - c) H1 hc1
      (fun d hd => ⟨(hK1 d hd).1, (hK1 d hd).2.1, (hK1 d hd).2.2.1⟩) ⟨cp, hcpK, hcp1, by omega⟩
      b1 b5 b7 b8 b10 (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s16) m24
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s88)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s80)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s72)
      (by rw [← Nat.add_assoc]; exact rR0) rR8
      (by rw [dat1, Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))])
    have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
    have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
    have hsteps : 64 * ((L + 31) / 32) + 2 * c + 1800 + (10 + loopSteps (L + c) (left - c)) ≤
        loopSteps L left := by
      subst hcL; unfold loopSteps; omega
    rcases hrec with ⟨ω', μ', s'', q', run', z0, z1, z5, z6, zO, zO8, zO16, zdat, zR0, zR8, zH, zc, zK, zfr⟩ | hex
    · refine Or.inl ⟨ω', μ', s'', q', (run1.trans (run2.trans run')).mono hsteps, z0, z1, z5, z6,
        by rw [← show L + c + (left - c) = L + left by omega]; exact zO, zO8,
        by rw [← show L + c + (left - c) = L + left by omega]; exact zO16, ?_,
        by rw [← show ptr0 + (L + c) + (left - c) = ptr0 + L + left by omega]; exact zR0,
        by rw [← show len - c - (left - c) = len - left by omega]; exact zR8, zH,
        by rw [show L + left = L + c + (left - c) by omega]; exact zc, fun d hd => ?_,
        fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (by omega)) h2)⟩
      · rw [show L + left = L + c + (left - c) by omega, zdat]
        exact Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))
      · obtain ⟨z1', z2', z3', z4'⟩ := zK d hd
        exact ⟨z1', z2', z3', fun a ha => (z4' a ha).trans ((hK1 d hd).2.2.2 a ha)⟩
    · exact Or.inr ((Exhausts.pre (run1.trans run2) hex).mono (by omega))
  · -- the last chunk: the exit
    have hcl : c = left := by omega
    subst hcl
    obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := hc1
    obtain ⟨hr0, -, hrT⟩ := chunk_in H1.wf hcrm hcru
    have hb1 := H1.hb0
    have hbT1 := H1.hbT
    obtain ⟨ω2, μ2, run2, z0, z1, z5, z6, zO, zO8, zO16, fr2, rd2, wr2⟩ :=
      v3g (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 S O r (L + c) L c ret t v5 v6
        ⟨by omega, by omega⟩ (by omega) (Or.inr hO.1) a1 a5 a6 a7 (by omega) (by omega) (by omega) (by omega)
        hv5 hv6 m32 m40 m24
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s88)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s80)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s72)
        hret hjt hbt hrd1 (fun a h1 h2 => H1.st a (by omega) (by omega))
    have hlowh : ∀ a, a < 2147483648 → μ2.read a = μ1.read a := fun a h2 =>
      fr2 a (by omega) (Or.inl (by omega))
    have run12 := run1.trans run2
    refine Or.inl ⟨ω2, μ2, s', r, run12.mono (by unfold loopSteps; omega), z0, z1, z5, z6, zO, zO8, zO16,
      ?_, ?_, ?_, ctx_congr_data H1 hcrm (fun a h1 _ => hlowh a h1) wr2, ⟨cr, hcrm, hcra, hcru, hcrs⟩,
      fun d hd => ?_, ?_⟩
    · rw [Memory.readN_congr (fun j hj => hlowh _ (by omega))]; exact dat1
    · rw [Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega))]; exact rR0
    · rw [Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega))]; exact rR8
    · obtain ⟨k1, k2, k3, k4⟩ := hK1 d hd
      refine ⟨k1, k2, k3, fun a ha => ?_⟩
      have hca := ha
      unfold InData at hca
      have := (chunk_in H1.wf k1 k2).2.2
      exact (hlowh a (by omega)).trans (k4 a ha)
    · intro a h0 h1 h2 h3
      exact (fr2 a h0 h3).trans (fr1 a h0 (Or.inr (by omega)) h2)

/-- **Reading more than 16384 octets into a fresh `Vec<u8>`, the payload in the heap** (3473, the
    whole of `read_vec`): as `vec_u8_heap`, for 16384 < n < 2³⁰ − 64, with the stack pointer at least
    S0 + 456 (the `realloc` wrapper's frames below `read_vec`'s). The first 16384 octets go into the
    block of the model's `alloc` of 512 units; then `read_vec`'s loop (`loop_heap`) grows the buffer
    with `realloc` to exactly L + min(left, L) octets per pass until all n are read. Either `read_vec`
    returns to t with the `Vec` `{cap n, ptr q, len n}` at O (the capacity is exactly n: each
    `finish_grow` asks for the octets read so far plus the next chunk), q holding the n payload
    octets and being the data of an allocated chunk of ⌈n/32⌉ + 1 units that is no allocated chunk of
    `s`, the context kept for the final state `s'`, every allocated chunk of `s` kept with its data,
    the reader advanced, the stack from sp up kept off the reader and O, memory below 196608 and the
    access of everything from S0 up kept; or the run reaches a failed allocator call (`Exhausts`):
    the first chunk's `alloc` or one of the `realloc`s fails.

    *Not stated:* that the globals below the allocator (`Glob`) are kept, as `vec_u8_heap` states;
    `ReallocCall.realloc_call` does not record it. -/
theorem vec_u8_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + n ≤ c.addr + 32 * c.size)
    (hS : S0 + 456 ≤ sp ∧ sp ≤ S1) (hsp : 2147484104 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 16384 < n ∧ n < 1073741760) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 3473 ω μ x t ω' μ' x
        (34000 + loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q n = μ.readN ptr n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 3473 ω μ x (34000 + loopSteps 16384 (n - 16384)) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, -, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hrd64 : rd < 18446744073709551616 := by omega
  have hO64 : O < 18446744073709551616 := by omega
  have hret64 : ret < 18446744073709551616 := by omega
  -- the frame and the call of finish_grow for the first chunk
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m80, m88, m64, m96, fr1, rd1,
      wr1⟩ := v1g (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n len ret v5 v6
    ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 hret64 hv5 hv6 hO64 (by omega) hnl (by omega) (by omega)
    (Or.inr hrd.1) (rd8' (by omega) hR8)
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hst a (by omega) (by omega))
  rw [show min n 16384 = 16384 by omega] at a6 a10 m96
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 136) (sp - 48) 16384 88 0 16384
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by decide)
      (by omega) (by omega) ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 136 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω2 μ2 s (sp - 136) 16384 1 pb S0 S1 H2 b1 b7
      b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s1, ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by unfold loopSteps; omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne := hfresh cp hcpm hcpu
  obtain ⟨hqb, -, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT'
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  have hF : ∀ a, sp - 136 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 136) (sp - 48) 16384 q 88 3600 0 16384
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by decide) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS5 : ∀ a, sp - 96 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 96) rd q 16384 ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) hrd64
      (by rw [show sp - 96 + 48 = sp - 48 by omega]; exact cres)
      (by rw [show sp - 96 + 56 = sp - 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  -- the read of the first chunk
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans
      (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, q ≤ a → a < q + 16384 → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩
  have hdq : q + 16384 + 24 ≤ ptr ∨ ptr + 16384 + 24 ≤ q := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_low (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 90 3635 (sp - 96) rd q ptr len 16384 d0 d1
      d7 d8 d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hlen (by omega) hdq
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega)) hwq
      (fun a h1 h2 => Memory.readable_of_writable
        (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  have hS7 : ∀ a, sp - 96 ≤ a → a < sp → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
  have hS61 : ∀ a, sp - 96 ≤ a → a < sp → (a < sp - 72 ∨ sp - 64 ≤ a) → (a < sp - 56 ∨ sp - 48 ≤ a) →
      (a < sp - 48 ∨ sp - 24 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h3' h4 =>
    (hS7 a h1 h2).trans ((fr6 a (by omega) (by omega) (by omega)).trans (hS5 a h1 (by omega) h4))
  have h7hi : ∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))).trans (hhigh a h0 h1)
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 16384 ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans (h63 a h1)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [wr7, wr36]
  have H7 : HeapCtx env pb S0 S1 μ7 s1 :=
    ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr73
  have kd7 : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ7.read a = μ.read a := by
    intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  -- the back edge
  obtain ⟨ω8, run8, z1, z5, z7, z8, z10, -⟩ :=
    Services.Bootstrap.Decode.VecU8.v5 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (sp - 96) 0 16384
      n 16384 ⟨by omega, by omega⟩ (by rw [r1, d1]) (by rw [r5, d5]) (by rw [r6, d6]) r7 ⟨by omega, by omega⟩
      (by omega) (by omega)
      (by rw [show sp - 96 + 32 = sp - 64 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m64)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dn)
      (fun a h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (by rw [wr36]; exact H3.st a (by omega) (by omega)))
  have run18 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8))))))
  -- the loop
  have hK : ∀ d, (d ∈ chunks s ∧ d.used = true) → d ∈ chunks s1 ∧ d.used = true ∧ d.addr + 32 ≠ q := by
    intro d ⟨hd, hu⟩
    refine ⟨keep d hd hu, hu, fun e => hfresh d hd hu ?_⟩
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    exact Tiles.addr_inj ht d (keep d hd hu) _ hnew (by simp only; omega)
  have hrest := loop_heap (p := p) (P := P) env cap hcap1 hcap x ω8 μ7 0 s1 (fun d => d ∈ chunks s ∧ d.used = true)
    (sp - 96) O rd q 16384 (n - 16384) ptr (len - 16384) ret t v5 v6 pb S0 S1 H7
    ⟨_, hnew, by simp only; omega, rfl, rfl⟩ hK ⟨cp, ⟨hcpm, hcpu⟩, hcp1, by omega⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ z1 z5 z7 z8 z10 (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
    (by rw [show sp - 96 + 8 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
    (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m80)
    (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dq)
    (by rw [show sp - 96 + 88 = sp - 8 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m8)
    (by rw [show sp - 96 + 80 = sp - 16 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m16)
    (by rw [show sp - 96 + 72 = sp - 24 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m24)
    hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr rR0 rR8
    (by rw [rbuf, Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩),
          Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)])
  rcases hrest with ⟨ω', μ', s', q', run', y0, y1, y5, y6, yO, yO8, yO16, ydat, yR0, yR8, yH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, yK, yfr⟩ | hex
  · have hn' : 16384 + (n - 16384) = n := by omega
    rw [hn'] at yO yO16 ydat hcfs
    have runAll := run18.trans run'
    obtain ⟨hfb, -, -⟩ := chunk_in yH.wf hcfm hcfu
    have hyb := yH.hb0
    have hcf : cf = ⟨q' - 32, (n + 31) / 32 + 1, true⟩ := by
      obtain ⟨ca, cs, cu⟩ := cf
      simp only at hcfa hcfu hcfs
      rw [hcfu, hcfs]; congr 1; omega
    refine Or.inl ⟨q', s', ω', μ', runAll.mono (by omega), y0, by rw [y1]; congr 1; omega, y5, y6, yO, yO8,
      yO16, ?_, by rw [← show ptr + 16384 + (n - 16384) = ptr + n by omega]; exact yR0,
      by rw [← show len - 16384 - (n - 16384) = len - n by omega]; exact yR8, yH,
      fun c hc hu => (yK c ⟨hc, hu⟩).1, hcf ▸ hcfm, ?_, ?_, FreeStepsH.pagesOut H.bd runAll, ?_, ?_, ?_⟩
    · rw [ydat]; exact Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)
    · intro d hd hu e
      have := (yK d ⟨hd, hu⟩).2.2.1
      rw [e] at this; simp only at this; omega
    · intro c hc hu a ha
      exact ((yK c ⟨hc, hu⟩).2.2.2 a ha).trans (kd7 c hc hu a ha)
    · intro a h0 h1 h2 h3
      exact (yfr a h0 (by omega) h2 h3).trans (h7hi a h0 h1 h2)
    · intro a ha'
      obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd runAll
      refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
      unfold Memory.readable
      rw [kp _ (Or.inl (by unfold pageSize; omega))]
    · intro a ha'
      obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd runAll
      unfold Memory.writable
      rw [kp _ (Or.inr (by unfold pageSize; omega))]
  · exact Or.inr ((Exhausts.pre run18 hex).mono (by omega))

end Services.Bootstrap.Decode.VecU8
