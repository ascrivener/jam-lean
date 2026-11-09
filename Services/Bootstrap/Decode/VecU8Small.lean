import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.Decode.AllocOk
import Services.Bootstrap.Alloc.Pages

/-!
# Reading 1 … 16384 octets into a fresh `Vec<u8>`

`vec_u8_small` composes the steps of `read_vec` (3473) for one chunk (`VecU8.v1` … `v3`,
`finish_grow`'s `g1`, `g2`) with the allocator's `alloc` (`AllocOk.alloc_ok`) and the reader: the
`Vec` `{cap n, ptr q, len n}` at O holds the n octets, q is the model's `alloc` of ⌈n/32⌉ units, and
the heap holds the model's state after it. The payload stays readable across the `alloc` because a
run under the refine contract keeps every page outside the heap's (`Alloc.FreeStepsH.pagesOut`).
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.AllocOk

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The block `alloc` returns**: for a well-formed heap, a successful `alloc` of r units at q leaves
    the base, makes ⟨q − 32, r + 1, used⟩ a chunk, and puts q, with its r usable units, inside the
    allocated space, above the base. -/
theorem alloc_block {grow : Grow} {hb r q : Nat} {s s' : State} (hwf : WF s)
    (hbT : s.base + 1073741824 < 2147483648) (h : alloc grow hb 1 r s = some (q, s')) :
    s'.base = s.base ∧ ⟨q - 32, r + 1, true⟩ ∈ chunks s' ∧ s.base + 32 ≤ q ∧
      q + 32 * r ≤ s'.base + 32 * s'.allocated ∧ q + 32 * r < 2147483648 := by
  have hwf' : WF s' := alloc_wf hwf h
  have hb' : s'.base = s.base := by
    have h' := h
    rw [alloc_one hwf.1] at h'
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := alloc1_eq h'
    simp
  obtain ⟨pre, post, S, -, -, hcs'⟩ := alloc_chunks hwf h
  have hc : (⟨q - 32, r + 1, true⟩ : Chunk) ∈ chunks s' := by rw [hcs']; simp
  have hsp := hwf'.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp _ hc).1 rfl
  have ht := hwf'.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt _ hc
  have hb0 : s'.base ≠ 0 := hwf'.1
  have htop : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  dsimp only at h1 hm
  refine ⟨hb', hc, by omega, by omega, by omega⟩

theorem rd8' {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- The reader for n octets, 1 ≤ n ≤ 16384, either size: `read_ok` below 16, `read_big_sp` from 16. -/
theorem read_any {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs)
    (μ : Memory) (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + n + 24 ≤ sp - 88) (hptr : sp ≤ ptr ∧ ptr + n + 16 < 4294967296)
    (hn : 1 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrf : sp ≤ rd) (hbr : buf + n + 16 ≤ rd)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (2 * n + 400) ∧ ReadOkBig ω ω' μ μ' sp rd buf ptr len n := by
  by_cases hs : n < 16
  · obtain ⟨ω', μ', run, ok⟩ := read_ok (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9
      hret hjt hbt ⟨by omega, hsp.2.1⟩ hrd ⟨hbuf.1, by omega⟩ ⟨by omega, by omega⟩ hs hnl hlen (Or.inr hrf)
      (by omega) (Or.inr (by omega)) (by omega) (by omega) hwf hwr hwb hra hR0 hR8
    obtain ⟨o0, o1, -, -, -, o5, o6, -, o7, oR0, oR8, obuf, ofr, ord, owr⟩ := ok
    exact ⟨ω', μ', run.mono (by omega), o0, o1, o5, o6, o7, oR0, oR8, obuf, ofr, ord, owr⟩
  · exact read_big_sp (p := p) (P := P) (R := R) x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9 hret hjt hbt hsp
      hrd ⟨hbuf.1, by omega⟩ ⟨by omega, hptr.2⟩ (by omega) hnl hlen (Or.inr hrf) (by omega) (Or.inr hptr.1)
      (by omega) (by omega) hwf hwr hwb hra hR0 hR8

/-- **Reading 1 … 16384 octets into a fresh `Vec<u8>`** (3473, one chunk): with ω₇ = O, ω₈ = rd (the
    reader `{ptr, len}`), ω₉ = n ≤ len, and the model's `alloc` (the host's `growTo pb`) returning q for
    ⌈n/32⌉ units, `read_vec` returns with `{cap n, ptr q, len n}` at O and the n octets from ptr at q.
    The reader is advanced by n. The heap holds the model's state after the `alloc`, with q's block
    allocated; the page entries outside the heap's are kept; at sp and above, memory changes only in
    the reader and O.

    Assumed: a well-formed, initialized heap (as `realloc_wrap_cases`), the stack [S0, S1) writable
    above the heap's bound, sp in it with 320 octets below, and the reader, O and the payload at or
    above sp.

    *Setting:* this assumes the payload lies at or above the stack frame, which the decode loop
    does not satisfy (there the payload is inside an allocated heap chunk). The loop uses the
    heap-payload version, `VecU8.vec_u8_heap`. -/
theorem vec_u8_small {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp O rd ptr len n ret t v5 v6 q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (q, s'))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) (hS1 : S1 < 4294967296)
    (hsp : 2147483968 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 16384) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hptr : sp ≤ ptr ∧ ptr + n + 16 < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 3473 ω μ x t ω' μ' x (2 * n + 1100) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q n = μ.readN ptr n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (⟨q - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) := by
  obtain ⟨hbase, hcm, hq0, hqT, -⟩ := alloc_block hwf hbT h
  have hwf' : WF s' := alloc_wf hwf h
  have hfo' : FirstOk s' := alloc_first hwf hfo h
  have hr32 : n ≤ 32 * ((n + 31) / 32) := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hO64 : O < 18446744073709551616 := by omega
  have hret64 : ret < 18446744073709551616 := by omega
  -- the frame and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m80, m88, m64, m96, fr1, rd1,
      wr1⟩ := v1 (p := p) (P := P) (R := refineContract env) x ω μ sp O rd n len ret v5 v6 ⟨by omega, hsp.2.1⟩
    h0 h1 h5 h6 h7 h8 h9 hret64 hv5 hv6 hO64 hn hnl (by omega) (by omega) (Or.inr hrd.1) (rd8' (by omega) hR8)
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1 (p := p) (P := P) (R := refineContract env) x ω1 μ1 (sp - 136) (sp - 48) n 88 0 n ⟨by omega, by omega⟩
      a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by decide) (by omega) (by omega)
      ⟨hn.1, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  -- alloc
  have hlow : ∀ a, a < 4294967296 → (a < sp - 136 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rep2 : Rep μ2 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => hlow a (by omega) (Or.inl (by omega))
  have hl2 : rdN μ2 206848 1 = 0 := by rw [rdN_frame (fun j hj => hlow _ (by omega) (Or.inl (by omega)))]; exact hl
  obtain ⟨ω3, μ3, run3, rep3, -, e7, cl3, ⟨h', hp3, hHT3, hph, hpb⟩, hst3, stk3, e0, e1, e5, e6⟩ :=
    alloc_ok (p := p) (P := P) (S0 := S0) (S1 := S1) env x ω2 μ2 s s' (sp - 136) n 1 q pb ph hwf rep2 hbd h48 hhb
      hbs hcost h b1 b7 b8 (by decide) (by decide) (by omega) (by omega) (by omega) hb0 hbT hA hfo hl2 hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp wr12) (fun a h1 h2 => by rw [wr12]; exact hst a h1 h2) hHT
  have run4 := alloc_ret (p := p) (P := P) (R := refineContract env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  have hF : ∀ a, sp - 136 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContract env) x ω3 μ3 (sp - 136) (sp - 48) n q 88 3600 0 n
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by decide) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_43 bs_3600
      (fun a h1 h2 => Memory.readable_of_writable (hst3 a (by omega) (by omega)))
      (fun a h1 h2 => hst3 a (by omega) (by omega))
  -- the frame S = sp − 96 in μ5
  have hS5 : ∀ a, sp - 96 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d0, d1, d5, d6, d7, d8, d9, dq, dn, fr6, rd6, wr6⟩ :=
    v2 (p := p) (P := P) (R := refineContract env) x ω5 μ5 (sp - 96) rd q n ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) hrd64
      (by rw [show sp - 96 + 48 = sp - 48 by omega]; exact cres)
      (by rw [show sp - 96 + 56 = sp - 48 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 96 + 16 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact hst3 a (by omega) (by omega))
  -- the read
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have run16 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))
  have pg6 := FreeStepsH.pagesOut hbd run16
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hwq : ∀ a, q ≤ a → a < q + n → μ6.writable a = true := fun a h1 h2 => by
    rw [wr36]; exact HeapPages.wrAt hp3 hpb hst3 a (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨ω7, μ7, run7, r0, r1, r5, r6, r7, rR0, rR8, rbuf, fr7, rd7, wr7⟩ :=
    read_any (p := p) (P := P) (R := refineContract env) x ω6 μ6 90 3635 (sp - 96) rd q ptr len n d0 d1 d7 d8 d9
      (by decide) jte_44 bs_3635 ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, hptr.2⟩ hn.1 hnl hlen (by omega) (by omega)
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact hst3 a (by omega) (by omega)) hwq
      (fun a h1 h2 => by rw [pg6.readable (Or.inr (by omega))]; exact hra a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
  -- the return
  have hS7 : ∀ a, sp - 96 ≤ a → a < sp → μ7.read a = μ6.read a := fun a h1 h2 =>
    fr7 a (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
  have hS61 : ∀ a, sp - 96 ≤ a → a < sp → (a < sp - 72 ∨ sp - 64 ≤ a) → (a < sp - 56 ∨ sp - 48 ≤ a) →
      (a < sp - 48 ∨ sp - 24 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h3' h4 =>
    (hS7 a h1 h2).trans ((fr6 a (by omega) (by omega) (by omega)).trans (hS5 a h1 (by omega) h4))
  obtain ⟨ω8, μ8, run8, z0, z1, z5, z6, zO, zO8, zO16, fr8, rd8, wr8⟩ :=
    v3 (p := p) (P := P) (R := refineContract env) x ω7 μ7 (sp - 96) O q n ret t v5 v6 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) (by rw [r1, d1]) (by rw [r5, d5]) (by rw [r6, d6]) r7 (by omega) (by omega)
      hv5 hv6
      (by rw [show sp - 96 + 32 = sp - 64 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m64)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dn)
      (by rw [Memory.readN_congr (fun j hj => hS7 _ (by omega) (by omega))]; exact dq)
      (by rw [show sp - 96 + 8 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
      (by rw [show sp - 96 + 88 = sp - 8 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m8)
      (by rw [show sp - 96 + 80 = sp - 16 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m16)
      (by rw [show sp - 96 + 72 = sp - 24 by omega, Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m24)
      hret hjt hbt
      (fun a h1 h2 => by rw [rd7]; exact Memory.readable_of_writable (by rw [wr36]; exact hst3 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr7, wr36]; exact hst3 a (by omega) (by omega))
  -- the heap after the read and the return
  have hlowh : ∀ a, A0 ≤ a → a < 2147483648 → (a < q ∨ q + n ≤ a) → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (fr8 a (by omega) (by omega)).trans ((fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans
      ((fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))))
  have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase]; exact hbT
  have hb0' : 206864 ≤ s'.base := by rw [hbase]; exact hb0
  have rep8 : Rep μ8 s' := Rep.congr_data rep3 hwf' hb0' hbT' hcm (lo := q) (hi := q + n) (by simp; omega)
    (by simp; omega) hlowh
  have run18 := run16.trans (run7.trans run8)
  have wr8' : ∀ a, μ8.writable a = μ3.writable a := fun a => by rw [wr8, wr7, wr36]
  refine ⟨ω8, μ8, run18.mono (by omega), z0, by rw [z1]; congr 1; omega, z5, z6, zO, zO8, zO16, ?_, ?_, ?_, rep8,
    hwf', hfo', ?_, hcm, ⟨h', HeapPages.of_eq hp3 wr8', hHT3, hph, hpb⟩,
    fun a h1 h2 => by rw [wr8']; exact hst3 a h1 h2, FreeStepsH.pagesOut hbd run18, ?_⟩
  · rw [Memory.readN_congr (fun j hj => (fr8 _ (by omega) (by omega)).trans rfl), rbuf]
    exact Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega))]; exact rR0
  · rw [Memory.readN_congr (fun j hj => fr8 _ (by omega) (by omega))]; exact rR8
  · rw [rdN_frame (fun j hj => hlowh _ (by unfold A0; omega) (by omega) (by omega))]; exact cl3
  · intro a h0 h1 h2 h3
    rw [fr8 a h0 h3, fr7 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega))]; exact hhigh a h0 h1

end Services.Bootstrap.Decode.VecU8
