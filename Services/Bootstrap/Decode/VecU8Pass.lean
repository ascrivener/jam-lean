import Services.Bootstrap.Decode.VecU8Loop
import Services.Bootstrap.Decode.ReallocOk
import Services.Bootstrap.Decode.VecU8Small

/-!
# One pass of `read_vec`'s chunk loop

`pass_ok` composes the steps of one pass of the loop at 3520 (`VecU8Loop`) with the allocator's
`realloc` (`ReallocOk.realloc_wrap_cases_hdata`) and the reader, when the model's `realloc`
returns a block: from L octets read into a buffer q of ⌈L/32⌉ units, the pass grows the buffer to
r of ⌈(L + c)/32⌉ units, c = min(left, L), and reads the next c octets into it.
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.ReallocOk Services.Bootstrap.Decode.AllocOk

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem readN_split (μ : Memory) (a n m : Nat) : μ.readN a (n + m) = μ.readN a n ++ μ.readN (a + n) m := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, Nat.add_assoc]

theorem readN_prefix {μ μ' : Memory} {a b n m : Nat} (hnm : n ≤ m) (h : μ'.readN a m = μ.readN b m) :
    μ'.readN a n = μ.readN b n := by
  rw [show m = n + (m - n) by omega, readN_split, readN_split] at h
  exact (List.append_inj h (by simp [Memory.readN])).1

/-- An allocated chunk of a well-formed heap lies above the base, inside the allocated space and
    below the top. -/
theorem chunk_in {s : State} {c : Chunk} (hwf : WF s) (hc : c ∈ chunks s) (hu : c.used = true) :
    s.base ≤ c.addr ∧ c.addr + 32 * c.size ≤ s.base + 32 * s.allocated ∧
      c.addr + 32 * c.size ≤ s.base + 1073741824 := by
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  have hsp := hwf.2.2.2.2.2.2.2; unfold SpaceOk at hsp
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  exact ⟨(ht.mem_lt _ hc).1, (hsp _ hc).1 hu, htop ▸ (ht.mem_lt _ hc).2.1⟩

/-- The usable size of a chunk's data address is its size less one unit. -/
theorem usable_of_chunk {s : State} {c : Chunk} (hc : c ∈ chunks s) : usable s (c.addr + 32) = c.size - 1 := by
  unfold usable; rw [Nat.add_sub_cancel, chunks_hdr c hc, wordSize_sizeWord]

/-- **One pass of the loop, `realloc` succeeding** (3520 … 3635): with L ≥ 1 octets read into the
    buffer q (an allocated chunk of ⌈L/32⌉ + 1 units; S + 24 holds q, S + 16 the reader rd) and
    `left` ≥ 1 to go (ω₅ = ω₇ = ω₈ = L, ω₁₀ = left), and the model's `realloc` of q to
    ⌈(L + c)/32⌉ units, c = min(left, L), giving `(r, s', _)`: the pass reaches 3635 (the reader's
    return) with ω₅ = L, ω₆ = c, ω₇ = 0 (`Ok`), S + 32 holding left, S + 40 the capacity L + c and
    S + 24 the buffer r, whose first L + c octets are the payload's; the reader advanced by c; the
    heap holding `s'` (r an allocated chunk of ⌈(L + c)/32⌉ + 1 units), its pages some h' that bound
    its allocated space. -/
theorem pass_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (b : Bool)
    (S rd q r L left ptr0 len pb h : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    (hcq : ∃ c ∈ chunks s, c.addr + 32 = q ∧ c.used = true ∧ c.size = (L + 31) / 32 + 1)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ h + 14)
    (hR : realloc (growTo pb) hb s q 1 ((L + min left L + 31) / 32) = some (r, s', b))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hHT : s.base + 32 * s.allocated ≤ 4096 * h)
    (hS : S0 + 360 ≤ S ∧ S + 96 ≤ S1) (hSb : 4096 * pb ≤ S0) (hS1 : S1 < 4294967296)
    (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat left)
    (hL : 1 ≤ L) (hl1 : 1 ≤ left) (hn : L + left < 1073741760) (hlen : left ≤ len ∧ len < 4294967296)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 rd) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q)
    (hrd : S + 96 ≤ rd ∧ rd + 16 ≤ S1)
    (hptr : S + 96 ≤ ptr0 ∧ ptr0 + L + left + 16 < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + L)) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hra : ∀ a, ptr0 + L ≤ a → a < ptr0 + L + left → μ.readable a = true)
    (hdat : μ.readN q L = μ.readN ptr0 L) :
    ∃ ω' μ' h', FreeStepsH p (refineContract env) 3520 ω μ x 3635 ω' μ' x
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
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (∃ c ∈ chunks s', c.addr + 32 = r ∧ c.used = true ∧ c.size = (L + min left L + 31) / 32 + 1) ∧
      s'.base = s.base ∧ HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧
      h ≤ h' ∧ h' ≤ pb ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' := by
  generalize hcdef : min left L = c at *
  have hc1 : 1 ≤ c ∧ c ≤ left ∧ c ≤ L := by omega
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  have hu : usable s q = (L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, hqT, -⟩ := chunk_in hwf hcqm hcqu
  have hA : s.allocated < 2147483648 := by omega
  have hba : s.base % 8 = 0 := by have := hwf.2.1; omega
  -- the loop's head
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m32, m0, fr1, rd1, wr1⟩ :=
    lh (p := p) (P := P) (R := refineContract env) x ω μ S L left q ⟨by omega, by omega⟩ h1 h5 h7 h8 h10
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ (by omega) s24 (fun a h1 h2 => hst a (by omega) (by omega))
  rw [hcdef] at a6 a10 m0
  -- finish_grow, to realloc
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3 (p := p) (P := P) (R := refineContract env) x ω1 μ1 (S - 40) (S + 48) L q (L + c) 88 L (L + c)
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 72 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => hlow a (by omega) (Or.inl (by omega))
  have hl2 : rdN μ2 206848 1 = 0 := by
    rw [rdN_frame (fun j hj => hlow _ (by omega) (Or.inl (by omega)))]; exact hl
  -- realloc
  obtain ⟨ω3, μ3, datMin, -, run3, cl3, hst3, stk3, e0, e1, e5, e6, hsome, -⟩ :=
    realloc_wrap_cases_hdata (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω2 μ2 s (S - 40) q 1
      (L + c) pb h hwf rep2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (fun h => absurd h (by omega)) hbd h48 hhb hbs
      hcost b1 b7 b9 b10 (by decide) (by decide) (by omega) (by omega) (by omega) hba hb0 hbT hA hfo hl2
      hHTs hHT ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp wr12)
      (fun a h1 h2 => by rw [wr12]; exact hst a h1 h2)
  have hR' : realloc (growTo pb) hb s q ((1 + 31) / 32) ((L + c + 31) / 32) = some (r, s', b) := hR
  obtain ⟨e7, rep3, wf3, fo3, hbase3, h', hp3, hHT3, hph, hpb⟩ := hsome r s' b hR'
  have dat3 := datMin r s' b hR' (by
    obtain ⟨cr, hcrm, hcra, hcru, -⟩ := realloc_chunk hwf hbT ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR
    have := (chunk_in wf3 hcrm hcru).1; omega)
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := realloc_chunk hwf hbT ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR
  obtain ⟨hr0, hrT, hrT'⟩ := chunk_in wf3 hcrm hcru
  rw [hcrs] at hrT hrT'
  have run4 := realloc_ret (p := p) (P := P) (R := refineContract env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContract env) x ω3 μ3 (S - 40) (S + 48) (L + c) r 88 3600 L (L + c)
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (hst3 a (by omega) (by omega)))
      (fun a h1 h2 => hst3 a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 48 ∨ S + 72 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  have hS50 : ∀ a, S ≤ a → a < 4294967296 → (S + 8 ≤ a ∧ a < S + 32 ∨ S + 72 ≤ a) →
      μ5.read a = μ.read a :=
    fun a h1 h2 h3 => (hS51 a h1 h2 (by omega)).trans (fr1 a h2 (by omega) (by omega))
  -- read_vec: the call of the reader
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2g (p := p) (P := P) (R := refineContract env) x ω5 μ5 S rd r (L + c) L c ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega) (by omega)
      cres (by rw [show S + 56 = S + 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m0)
      (by rw [Memory.readN_congr (fun j hj => hS50 _ (by omega) (by omega) (by omega))]; exact s16)
      (fun a h1 h2 => by rw [wr5]; exact hst3 a (by omega) (by omega))
  have hhigh : ∀ a, a < 4294967296 → S + 72 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans (hS50 a (by omega) h0 (Or.inr h1))
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  have pg6 := FreeStepsH.pagesOut hbd run16
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, r + L ≤ a → a < r + L + c → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact HeapPages.wrAt hp3 hpb hst3 a (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_any (p := p) (P := P) (R := refineContract env) x ω6 μ6 90 3635 S rd (r + L) (ptr0 + L) len c
      d0 d1 d7 d8 d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, hsp.2⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hc1.1 (by omega) hlen.2 (by omega) (by omega)
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega)) hwq
      (fun a h1 h2 => by rw [pg6.readable (Or.inr (by omega))]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  -- the results
  have h76 : ∀ a, S ≤ a → a < S + 96 → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr h1) (Or.inl (by omega)) (Or.inr (by omega))
  have h71 : ∀ a, S ≤ a → a < S + 96 → (a < S + 24 ∨ S + 32 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) →
      (a < S + 48 ∨ S + 72 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (h76 a h1 h2).trans ((fr6 a (by omega) h3 h4).trans (hS51 a h1 (by omega) h5))
  have hlowh : ∀ a, A0 ≤ a → a < 2147483648 → (a < r + L ∨ r + L + c ≤ a) → μ7.read a = μ3.read a :=
    fun a h1 h2 h3 => (fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans
      ((fr6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega))))
  have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase3]; exact hbT
  have hb0' : 206864 ≤ s'.base := by rw [hbase3]; exact hb0
  have rep7 : Rep μ7 s' := Rep.congr_data rep3 wf3 hb0' hbT' hcrm (lo := r + L) (hi := r + L + c)
    (by omega) (by rw [hcrs]; omega) hlowh
  have run17 := run16.trans run7
  have wr7' : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [wr7, wr36]
  refine ⟨ω7, μ7, h', run17.mono (by omega), by rw [r1, d1], by rw [r5, d5], by rw [r6, d6], r7, ?_, ?_, ?_,
    ?_, rR0, rR8, ?_, rep7, wf3, fo3, ?_, ⟨cr, hcrm, hcra, hcru, hcrs⟩, hbase3,
    HeapPages.of_eq hp3 wr7', hHT3, hph, hpb, fun a h1 h2 => by rw [wr7']; exact hst3 a h1 h2,
    FreeStepsH.pagesOut hbd run17⟩
  · rw [Memory.readN_congr (fun j hj => h71 _ (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact m32
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact dn
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact dq
  · intro a h0 h1 h2
    exact (fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))).trans
      ((fr6 a h0 (by omega) (by omega)).trans (hS50 a (by omega) h0 (by omega)))
  · rw [readN_split, readN_split, rbuf, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]
    congr 1
    rw [Memory.readN_congr (fun j hj => hlowh _ (by unfold A0; omega) (by omega) (by omega))]
    rw [readN_prefix (by omega) dat3, Memory.readN_congr (fun j hj => hlow _ (by omega) (by omega))]
    exact hdat
  · rw [rdN_frame (fun j hj => hlowh _ (by unfold A0; omega) (by omega) (by omega))]; exact cl3

/-- **One pass of the loop, `realloc` failing** (3520 … 33055): as `pass_ok`, but the model's
    `realloc` gives `none`: the pass reaches `finish_grow`'s return point from `realloc` (33055) with
    ω₇ = 0 (null), memory still holding `s`, the heap's pages as they were. -/
theorem pass_fail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State)
    (S q L left pb h : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    (hcq : ∃ c ∈ chunks s, c.addr + 32 = q ∧ c.used = true ∧ c.size = (L + 31) / 32 + 1)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ h + 14)
    (hR : realloc (growTo pb) hb s q 1 ((L + min left L + 31) / 32) = none)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hHT : s.base + 32 * s.allocated ≤ 4096 * h)
    (hS : S0 + 360 ≤ S ∧ S + 96 ≤ S1) (hSb : 4096 * pb ≤ S0) (hS1 : S1 < 4294967296)
    (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat left)
    (hL : 1 ≤ L) (hl1 : 1 ≤ left) (hn : L + left < 1073741760)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 3520 ω μ x 33055 ω' μ' x (64 * ((L + 31) / 32) + 1400) ∧
      ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb h := by
  generalize hcdef : min left L = c at *
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  have hu : usable s q = (L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, hqT, -⟩ := chunk_in hwf hcqm hcqu
  have hA : s.allocated < 2147483648 := by omega
  have hba : s.base % 8 = 0 := by have := hwf.2.1; omega
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m32, m0, fr1, rd1, wr1⟩ :=
    lh (p := p) (P := P) (R := refineContract env) x ω μ S L left q ⟨by omega, by omega⟩ h1 h5 h7 h8 h10
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ (by omega) s24 (fun a h1 h2 => hst a (by omega) (by omega))
  rw [hcdef] at a6 a10
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3 (p := p) (P := P) (R := refineContract env) x ω1 μ1 (S - 40) (S + 48) L q (L + c) 88 L (L + c)
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 72 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => hlow a (by omega) (Or.inl (by omega))
  have hl2 : rdN μ2 206848 1 = 0 := by
    rw [rdN_frame (fun j hj => hlow _ (by omega) (Or.inl (by omega)))]; exact hl
  obtain ⟨ω3, μ3, -, -, run3, -, -, -, e0, -, -, -, -, hnone⟩ :=
    realloc_wrap_cases_hdata (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω2 μ2 s (S - 40) q 1
      (L + c) pb h hwf rep2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (fun h => absurd h (by omega)) hbd h48 hhb hbs
      hcost b1 b7 b9 b10 (by decide) (by decide) (by omega) (by omega) (by omega) hba hb0 hbT hA hfo hl2
      hHTs hHT ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp wr12)
      (fun a h1 h2 => by rw [wr12]; exact hst a h1 h2)
  obtain ⟨e7, rep3, hp3⟩ := hnone hR
  rw [hu] at run3
  have run4 := realloc_ret (p := p) (P := P) (R := refineContract env) x ω3 μ3 (by rw [e0, b0])
  exact ⟨ω3, μ3, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), e7, rep3, hp3⟩

/-- The step bound of the loop from L octets read with `left` to go. -/
def loopSteps (L left : Nat) : Nat := 2 * L + 8 * left + 2000 * (left / L) + 2000

/-- **`read_vec`'s chunk loop** (from 3520 to `read_vec`'s return t): with L ≥ 1 octets of the
    payload read into the buffer q (an allocated chunk of ⌈L/32⌉ + 1 units) and `left` ≥ 1 to go,
    as in `pass_ok`, and `read_vec`'s frame at S (O at S + 8, the reader rd at S + 16, the saved ω₀,
    ω₅, ω₆ at S + 88, S + 80, S + 72), the loop either

    * returns to t (ω₁ = S + 96, ω₀, ω₅, ω₆ restored) with the `Vec` `{cap L + left, ptr q',
      len L + left}` at O, q' holding the payload's first L + left octets, the reader advanced by
      `left`, and the heap holding the model's state after the passes' `realloc`s; or
    * reaches `finish_grow`'s return point from a `realloc` (33055) with ω₇ = 0, the model's
      `realloc` having given `none` from the state memory holds.

    *Setting:* this assumes the payload lies at or above the stack frame, which the decode loop
    does not satisfy (there the payload is inside an allocated heap chunk). A heap-payload version
    needs `realloc` to keep other chunks' data, which is not yet proved. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State)
    (S O rd q L left ptr0 len ret t v5 v6 pb h : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    (hcq : ∃ c ∈ chunks s, c.addr + 32 = q ∧ c.used = true ∧ c.size = (L + 31) / 32 + 1)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ h) (hhb : h ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ h + 14)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * h) (hHT : s.base + 32 * s.allocated ≤ 4096 * h)
    (hS : S0 + 360 ≤ S ∧ S + 96 ≤ S1) (hSb : 4096 * pb ≤ S0) (hS1 : S1 < 4294967296)
    (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (hp : HeapPages μ 48 pb h) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
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
    (hptr : S + 96 ≤ ptr0 ∧ ptr0 + L + left + 16 < 4294967296) (hpr : ptr0 + L + left ≤ rd ∨ rd + 16 ≤ ptr0)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + L)) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hra : ∀ a, ptr0 + L ≤ a → a < ptr0 + L + left → μ.readable a = true)
    (hdat : μ.readN q L = μ.readN ptr0 L) :
    (∃ ω' μ' s' q' h', FreeStepsH p (refineContract env) 3520 ω μ x t ω' μ' x (loopSteps L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN q' (L + left) = μ.readN ptr0 (L + left) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + L + left) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - left) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (∃ c ∈ chunks s', c.addr + 32 = q' ∧ c.used = true ∧ c.size = (L + left + 31) / 32 + 1) ∧
      s'.base = s.base ∧ HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧
      h ≤ h' ∧ h' ≤ pb ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → S + 96 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ' s'' q'' n'', FreeStepsH p (refineContract env) 3520 ω μ x 33055 ω' μ' x (loopSteps L left) ∧
      ω'[7] = UInt64.ofNat 0 ∧ realloc (growTo pb) hb s'' q'' 1 n'' = none ∧ Rep μ' s'' ∧ WF s'') := by
  induction left using Nat.strongRecOn generalizing ω μ s q L len h with
  | _ left ih =>
  have hX : 64 * ((L + 31) / 32) ≤ 2 * L + 62 := by omega
  cases hRr : realloc (growTo pb) hb s q 1 ((L + min left L + 31) / 32) with
  | none =>
    obtain ⟨ω', μ', run, e7, rep', -⟩ :=
      pass_fail (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s S q L left pb h hwf hrep hfo hl
        hcq hbd h48 hhb hbs hcost hRr hb0 hbT hHTs hHT hS hSb hS1 hsp hp hst h1 h5 h7 h8 h10 hL hl1 hn s24
    exact Or.inr ⟨ω', μ', s, q, _, run.mono (by unfold loopSteps; omega), e7, hRr, rep', hwf⟩
  | some res =>
    obtain ⟨r, s', b⟩ := res
    obtain ⟨ω1, μ1, h', run1, a1, a5, a6, a7, m32, m40, m24, fr1, rR0, rR8, dat1, rep1, wf1, fo1, cl1, hc1,
        hbase1, hp1, hHT1, hhh, hpb1, hst1, pg1⟩ :=
      pass_ok (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s s' b S rd q r L left ptr0 len pb h
        hwf hrep hfo hl hcq hbd h48 hhb hbs hcost hRr hb0 hbT hHTs hHT hS hSb hS1 hsp hp hst h1 h5 h7 h8 h10
        hL hl1 hn hlen s16 s24 hrd ⟨hptr.1, hptr.2⟩ hR0 hR8 hra hdat
    generalize hcdef : min left L = c at *
    have hc : 1 ≤ c ∧ c ≤ left ∧ c ≤ L ∧ (c < left → c = L) := by omega
    have hS1r : ∀ a, S ≤ a → a < S + 96 → (S + 8 ≤ a ∧ a < S + 24 ∨ S + 72 ≤ a) → μ1.read a = μ.read a :=
      fun a h1 h2 h3 => fr1 a (by omega) h3 (Or.inl (by omega))
    have hpay : ∀ a, ptr0 ≤ a → a < ptr0 + L + left → μ1.read a = μ.read a := fun a h1 h2 =>
      fr1 a (by omega) (Or.inr (by omega)) (by omega)
    have hrd1 : ∀ a, S ≤ a → a < S + 96 → μ1.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (hst1 a (by omega) (by omega))
    by_cases hlt : c < left
    · -- the back edge, and the rest of the loop
      have hcL : c = L := hc.2.2.2 hlt
      obtain ⟨ω2, run2, b1, b5, b7, b8, b10, -⟩ :=
        Services.Bootstrap.Decode.VecU8.v5 (p := p) (P := P) (R := refineContract env) x ω1 μ1 S L c left (L + c) ⟨by omega, by omega⟩
          a1 a5 a6 a7 ⟨hlt, by omega⟩ (by omega) (by omega) m32 m40 hrd1
      have hb0' : 206864 ≤ s'.base := by rw [hbase1]; exact hb0
      have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase1]; exact hbT
      have hrec := ih (left - c) (by omega) ω2 μ1 s' r (L + c) (len - c) h' wf1 rep1 fo1 cl1 hc1
        (by omega) hpb1 (by omega) hb0' hbT' (by omega) hHT1 hp1 hst1 b1 b5 b7 b8 b10 (by omega) (by omega)
        (by omega) ⟨by omega, by omega⟩
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s16) m24
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s88)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s80)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s72)
        ⟨hptr.1, by omega⟩ (by omega)
        (by rw [← Nat.add_assoc]; exact rR0) rR8
        (fun a h1 h2 => by rw [pg1.readable (Or.inr (by omega))]; exact hra a (by omega) (by omega))
        (by rw [dat1, Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))])
      have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
      have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
      have hsteps : 64 * ((L + 31) / 32) + 2 * c + 1800 + (10 + loopSteps (L + c) (left - c)) ≤
          loopSteps L left := by
        subst hcL; unfold loopSteps; omega
      rcases hrec with ⟨ω', μ', s'', q', h'', run', z0, z1, z5, z6, zO, zO8, zO16, zdat, zR0, zR8, zrep, zwf, zfo,
          zcl, zc, zbase, zp, zHT, zhh, zpb, zst, zpg, zfr⟩ |
        ⟨ω', μ', s'', q'', n'', run', z7, zR, zrep, zwf⟩
      · refine Or.inl ⟨ω', μ', s'', q', h'', (run1.trans (run2.trans run')).mono hsteps, z0, z1, z5, z6,
          by rw [← show L + c + (left - c) = L + left by omega]; exact zO, zO8,
          by rw [← show L + c + (left - c) = L + left by omega]; exact zO16, ?_,
          by rw [← show ptr0 + (L + c) + (left - c) = ptr0 + L + left by omega]; exact zR0,
          by rw [← show len - c - (left - c) = len - left by omega]; exact zR8, zrep, zwf, zfo, zcl,
          by rw [show L + left = L + c + (left - c) by omega]; exact zc, zbase.trans hbase1, zp, zHT,
          Nat.le_trans hhh zhh, zpb, zst, pg1.trans zpg, fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans
            (fr1 a h0 (Or.inr (by omega)) h2)⟩
        rw [show L + left = L + c + (left - c) by omega, zdat]
        exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
      · exact Or.inr ⟨ω', μ', s'', q'', n'', (run1.trans (run2.trans run')).mono hsteps, z7, zR, zrep, zwf⟩
    · -- the last chunk: the exit
      have hcl : c = left := by omega
      subst hcl
      obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := hc1
      obtain ⟨hr0, hrT, hrT'⟩ := chunk_in wf1 hcrm hcru
      rw [hcrs] at hrT hrT'
      obtain ⟨ω2, μ2, run2, z0, z1, z5, z6, zO, zO8, zO16, fr2, rd2, wr2⟩ :=
        v3g (p := p) (P := P) (R := refineContract env) x ω1 μ1 S O r (L + c) L c ret t v5 v6
          ⟨by omega, by omega⟩ (by omega) (Or.inr hO.1) a1 a5 a6 a7 (by omega) (by omega) (by omega) (by omega)
          hv5 hv6 m32 m40 m24
          (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
          (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s88)
          (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s80)
          (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s72)
          hret hjt hbt hrd1 (fun a h1 h2 => hst1 a (by omega) (by omega))
      have hlowh : ∀ a, A0 ≤ a → a < 2147483648 → μ2.read a = μ1.read a := fun a h1 h2 =>
        fr2 a (by omega) (Or.inl (by omega))
      have hb0' : 206864 ≤ s'.base := by rw [hbase1]; exact hb0
      have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase1]; exact hbT
      have run12 := run1.trans run2
      have wr2' : ∀ a, μ2.writable a = μ1.writable a := wr2
      refine Or.inl ⟨ω2, μ2, s', r, h', run12.mono (by unfold loopSteps; omega), z0, z1, z5, z6, zO, zO8, zO16,
        ?_, ?_, ?_, rep1.congr_lock wf1 hb0' hbT' (fun a h1 h2 _ => hlowh a h1 h2), wf1, fo1, ?_,
        ⟨cr, hcrm, hcra, hcru, hcrs⟩, hbase1, HeapPages.of_eq hp1 wr2', hHT1, hhh, hpb1,
        fun a h1 h2 => by rw [wr2']; exact hst1 a h1 h2, FreeStepsH.pagesOut hbd run12, ?_⟩
      · rw [Memory.readN_congr (fun j hj => hlowh _ (by unfold A0; omega) (by omega))]; exact dat1
      · rw [Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega))]; exact rR0
      · rw [Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega))]; exact rR8
      · rw [rdN_frame (fun j hj => hlowh _ (by unfold A0; omega) (by omega))]; exact cl1
      · intro a h0 h1 h2 h3
        exact (fr2 a h0 h3).trans (fr1 a h0 (Or.inr (by omega)) h2)

/-- **Reading more than 16384 octets into a fresh `Vec<u8>`** (3473, the whole of `read_vec`): as
    `vec_u8_small`, for 16384 < n < 2³⁰ − 64. The first chunk of 16384 octets goes into q, the model's
    `alloc` of 512 units; then the loop (`loop`) doubles the buffer through `realloc` until all n
    octets are read. Either `read_vec` returns to t with the `Vec` `{cap n, ptr q', len n}` at O,
    q' holding the n payload octets and the heap the model's state after the `realloc`s, or it
    reaches `finish_grow`'s return point from a `realloc` that the model fails (33055, ω₇ = 0).

    *Setting:* this assumes the payload lies at or above the stack frame, which the decode loop
    does not satisfy (there the payload is inside an allocated heap chunk). A heap-payload version
    needs `realloc` to keep other chunks' data, which is not yet proved. -/
theorem vec_u8_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp O rd ptr len n ret t v5 v6 q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 512 s = some (q, s1))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hS : S0 + 456 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) (hS1 : S1 < 4294967296)
    (hsp : 2147484104 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 16384 < n ∧ n < 1073741760) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hptr : sp ≤ ptr ∧ ptr + n + 16 < 4294967296) (hpr : ptr + n ≤ rd ∨ rd + 16 ≤ ptr)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true) :
    (∃ ω' μ' s' q' h', FreeStepsH p (refineContract env) 3473 ω μ x t ω' μ' x
        (34000 + loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q' n = μ.readN ptr n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (∃ c ∈ chunks s', c.addr + 32 = q' ∧ c.used = true ∧ c.size = (n + 31) / 32 + 1) ∧
      s'.base = s.base ∧ HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧
      ph ≤ h' ∧ h' ≤ pb ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ' s'' q'' n'', FreeStepsH p (refineContract env) 3473 ω μ x 33055 ω' μ' x
        (34000 + loopSteps 16384 (n - 16384)) ∧
      ω'[7] = UInt64.ofNat 0 ∧ realloc (growTo pb) hb s'' q'' 1 n'' = none ∧ Rep μ' s'' ∧ WF s'') := by
  have h' : alloc (growTo pb) hb 1 ((16384 + 31) / 32) s = some (q, s1) := h
  obtain ⟨hbase, hcm, hq0, hqT, -⟩ := alloc_block hwf hbT h'
  have hwf' : WF s1 := alloc_wf hwf h'
  have hfo' : FirstOk s1 := alloc_first hwf hfo h'
  have hrd64 : rd < 18446744073709551616 := by omega
  have hO64 : O < 18446744073709551616 := by omega
  have hret64 : ret < 18446744073709551616 := by omega
  -- the frame and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m80, m88, m64, m96, fr1, rd1,
      wr1⟩ := v1g (p := p) (P := P) (R := refineContract env) x ω μ sp O rd n len ret v5 v6 ⟨by omega, hsp.2.1⟩
    h0 h1 h5 h6 h7 h8 h9 hret64 hv5 hv6 hO64 (by omega) hnl (by omega) (by omega) (Or.inr hrd.1)
    (rd8' (by omega) hR8)
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hst a (by omega) (by omega))
  rw [show min n 16384 = 16384 by omega] at a6 a10 m96
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1 (p := p) (P := P) (R := refineContract env) x ω1 μ1 (sp - 136) (sp - 48) 16384 88 0 16384
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by decide)
      (by omega) (by omega) ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  -- alloc
  have hlow : ∀ a, a < 4294967296 → (a < sp - 136 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => hlow a (by omega) (Or.inl (by omega))
  have hl2 : rdN μ2 206848 1 = 0 := by rw [rdN_frame (fun j hj => hlow _ (by omega) (Or.inl (by omega)))]; exact hl
  obtain ⟨ω3, μ3, run3, rep3, -, e7, cl3, ⟨h3, hp3, hHT3, hph, hpb⟩, hst3, stk3, e0, e1, e5, e6⟩ :=
    alloc_ok (p := p) (P := P) (S0 := S0) (S1 := S1) env x ω2 μ2 s s1 (sp - 136) 16384 1 q pb ph hwf rep2 hbd h48
      hhb hbs hcost h' b1 b7 b8 (by decide) (by decide) (by omega) (by omega) (by omega) hb0 hbT hA hfo hl2 hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp wr12) (fun a h1 h2 => by rw [wr12]; exact hst a h1 h2) hHT
  have run4 := alloc_ret (p := p) (P := P) (R := refineContract env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  have hF : ∀ a, sp - 136 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContract env) x ω3 μ3 (sp - 136) (sp - 48) 16384 q 88 3600 0 16384
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by decide) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (hst3 a (by omega) (by omega)))
      (fun a h1 h2 => hst3 a (by omega) (by omega))
  have hS5 : ∀ a, sp - 96 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2 (p := p) (P := P) (R := refineContract env) x ω5 μ5 (sp - 96) rd q 16384 ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) hrd64
      (by rw [show sp - 96 + 48 = sp - 48 by omega]; exact cres)
      (by rw [show sp - 96 + 56 = sp - 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact hst3 a (by omega) (by omega))
  -- the read of the first chunk
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  have pg6 := FreeStepsH.pagesOut hbd run16
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, q ≤ a → a < q + 16384 → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact HeapPages.wrAt hp3 hpb hst3 a (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_any (p := p) (P := P) (R := refineContract env) x ω6 μ6 90 3635 (sp - 96) rd q ptr len 16384 d0 d1 d7 d8
      d9 (by decide) jte_44 bs_3635 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega) hlen (by omega) (by omega)
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega)) hwq
      (fun a h1 h2 => by rw [pg6.readable (Or.inr (by omega))]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  have hS7 : ∀ a, sp - 96 ≤ a → a < sp → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
  have hS61 : ∀ a, sp - 96 ≤ a → a < sp → (a < sp - 72 ∨ sp - 64 ≤ a) → (a < sp - 56 ∨ sp - 48 ≤ a) →
      (a < sp - 48 ∨ sp - 24 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h3' h4 =>
    (hS7 a h1 h2).trans ((fr6 a (by omega) (by omega) (by omega)).trans (hS5 a h1 (by omega) h4))
  have h7hi : ∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))).trans (hhigh a h0 h1)
  -- the back edge
  obtain ⟨ω8, run8, z1, z5, z7, z8, z10, -⟩ :=
    Services.Bootstrap.Decode.VecU8.v5 (p := p) (P := P) (R := refineContract env) x ω7 μ7 (sp - 96) 0 16384 n
      16384 ⟨by omega, by omega⟩ (by rw [r1, d1]) (by rw [r5, d5]) (by rw [r6, d6]) r7 ⟨by omega, by omega⟩
      (by omega) (by omega)
      (by rw [show sp - 96 + 32 = sp - 64 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m64)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dn)
      (fun a h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (by rw [wr36]; exact hst3 a (by omega) (by omega)))
  have hb0' : 206864 ≤ s1.base := by rw [hbase]; exact hb0
  have hbT' : s1.base + 1073741824 < 2147483648 := by rw [hbase]; exact hbT
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [wr7, wr36]
  have hlowh : ∀ a, A0 ≤ a → a < 2147483648 → (a < q ∨ q + 16384 ≤ a) → μ7.read a = μ3.read a :=
    fun a h1 h2 h3 => (fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans
      ((fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega))))
  have rep7 : Rep μ7 s1 := Rep.congr_data rep3 hwf' hb0' hbT' hcm (lo := q) (hi := q + 16384) (by simp; omega)
    (by simp; omega) hlowh
  have run18 := (run16.trans run7).trans run8
  have hrest := loop (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω8 μ7 s1 (sp - 96) O rd q 16384
    (n - 16384) ptr (len - 16384) ret t v5 v6 pb h3 hwf' rep7 hfo'
    (by rw [rdN_frame (fun j hj => hlowh _ (by unfold A0; omega) (by omega) (by omega))]; exact cl3)
    ⟨_, hcm, by simp only; omega, rfl, rfl⟩ hbd (by omega) hpb hbs (by omega) hb0' hbT' (by omega) hHT3
    ⟨by omega, by omega⟩ hSb hS1 ⟨by omega, by omega⟩ (HeapPages.of_eq hp3 wr73)
    (fun a h1 h2 => by rw [wr73]; exact hst3 a h1 h2) z1 z5 z7 z8 z10 (by omega) (by omega) (by omega)
    ⟨by omega, by omega⟩
    (by rw [show sp - 96 + 8 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
    (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m80)
    (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dq)
    (by rw [show sp - 96 + 88 = sp - 8 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m8)
    (by rw [show sp - 96 + 80 = sp - 16 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m16)
    (by rw [show sp - 96 + 72 = sp - 24 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m24)
    hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr ⟨by omega, by omega⟩ (by omega) rR0 rR8
    (fun a h1 h2 => by rw [(FreeStepsH.pagesOut hbd (run16.trans run7)).readable (Or.inr (by omega))]; exact hra a (by omega) (by omega))
    (by rw [rbuf, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega)),
          Memory.readN_congr (fun j hj => h7hi _ (by omega) (by omega) (by omega))])
  rcases hrest with ⟨ω', μ', s', q', h'', run', y0, y1, y5, y6, yO, yO8, yO16, ydat, yR0, yR8, yrep, ywf, yfo,
      ycl, yc, ybase, yp, yHT, yhh, ypb, yst, ypg, yfr⟩ | ⟨ω', μ', s'', q'', n'', run', y7, yR, yrep, ywf⟩
  · have hn' : 16384 + (n - 16384) = n := by omega
    rw [hn'] at yO yO16 ydat yc
    refine Or.inl ⟨ω', μ', s', q', h'', (run18.trans run').mono (by omega), y0, by rw [y1]; congr 1; omega,
      y5, y6, yO, yO8, yO16, ?_, by rw [← show ptr + 16384 + (n - 16384) = ptr + n by omega]; exact yR0,
      by rw [← show len - 16384 - (n - 16384) = len - n by omega]; exact yR8, yrep, ywf, yfo, ycl,
      yc, ybase.trans hbase, yp, yHT, Nat.le_trans hph yhh, ypb, yst,
      (FreeStepsH.pagesOut hbd run18).trans ypg, fun a h0 h1 h2 h3 => (yfr a h0 (by omega) h2 h3).trans
        (h7hi a h0 h1 h2)⟩
    rw [ydat]; exact Memory.readN_congr (fun j hj => h7hi _ (by omega) (by omega) (by omega))
  · exact Or.inr ⟨ω', μ', s'', q'', n'', (run18.trans run').mono (by omega), y7, yR, yrep, ywf⟩

end Services.Bootstrap.Decode.VecU8
