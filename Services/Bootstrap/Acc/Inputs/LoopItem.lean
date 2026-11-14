import Services.Bootstrap.Acc.Inputs.Loop

/-!
# One item of `Vec<AccumulateItem>::decode`, as the loop sees it

`ItemOk env cap pb N enc Rep`: the item decode (45126, returning through 2044 to 45168) turns the
reader's octets `enc` into a 184-octet stack slot whose octets satisfy `Rep`, or exhausts the
allocator. In the style of T1's `ElemOkAF` (`Decode/LoopA.lean`). Instances: a transfer (`tr_call`),
an operand with a work output or a work error (`item_op_ok`, `item_op_err`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A piece of a read is a read. -/
theorem readN_drop_take (μ : Memory) (a n k m : Nat) (h : k + m ≤ n) :
    ((μ.readN a n).drop k).take m = μ.readN (a + k) m := by
  have e : μ.readN a n = μ.readN a k ++ (μ.readN (a + k) m ++ μ.readN (a + k + m) (n - k - m)) := by
    rw [← PVM.Memory.readN_split, ← PVM.Memory.readN_split]; congr 1; omega
  rw [e, List.drop_append_of_le_length (by simp), List.drop_eq_nil_of_le (by simp), List.nil_append,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-- **One item decodes into the loop's stack slot** (see the module doc): from 45126 with the loop's
    frame base sp (ω₁), the slot at sp + 88 (ω₇), the reader rd (ω₈) holding `enc` inside an allocated
    chunk, and return address 2044, either the run reaches 45168 with the slot's first word not −2, its
    184 octets satisfying `Rep` for every memory agreeing on the item's fresh chunks, the context for a
    new state keeping every allocated chunk and its data, and the reader past `enc`; or it exhausts the
    allocator (45975). -/
def ItemOk {X : Type} (env : HeapHost X) (cap pb : Nat) (p : ByteArray) (P : Program) (N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : X) (ω : Regs) (μ : Memory) (hb : Nat) (s : State) (sp rd ip rlen S0 S1 : Nat),
    HeapCtxC env.code pb S0 S1 μ s →
    ω[0] = UInt64.ofNat 2044 → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 88) → ω[8] = UInt64.ofNat rd →
    2147483960 + 424 ≤ sp → sp % 8 = 0 → S0 + 864 ≤ sp → sp + 480 ≤ rd → rd + 16 ≤ S1 →
    μ.readN rd 8 = Num.encodeLE 8 ip → μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen →
    enc.length ≤ rlen → rlen < 4294967296 → μ.readN ip enc.length = enc →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧ ip + enc.length ≤ c.addr + 32 * c.size) →
    (∃ s' ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45168 ω' μ' x N ∧
      ω'[0] = UInt64.ofNat 2044 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 88) 8 ≠ 18446744073709551614 ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN (sp + 88) 184) μ'') ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + enc.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - enc.length) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 88 ∨ sp + 272 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x N)

/-- A deferred transfer's encoding (GP v0.8.0 Appendix C): the tag 1, then ℰ₄(s), ℰ₄(d), ℰ₈(a), the
    128-octet memo m and ℰ₈(g). -/
def encTr (src dst amt gas : Nat) (m : List UInt8) : List UInt8 :=
  1 :: (Num.encodeLE 4 src ++ Num.encodeLE 4 dst ++ Num.encodeLE 8 amt ++ m ++ Num.encodeLE 8 gas)

/-- A transfer's 184-octet slot (`tr_call`): −1 at + 0, m at + 8, a at + 136, g at + 144, s at + 152,
    d at + 156. -/
def RepTr (src dst amt gas : Nat) (m : List UInt8) (bs : List UInt8) (_ : Memory) : Prop :=
  Num.decodeLE (bs.take 8) = 18446744073709551615 ∧ (bs.drop 8).take 128 = m ∧
    Num.decodeLE ((bs.drop 136).take 8) = amt ∧ Num.decodeLE ((bs.drop 144).take 8) = gas ∧
    Num.decodeLE ((bs.drop 152).take 4) = src ∧ Num.decodeLE ((bs.drop 156).take 4) = dst

theorem encTr_length (src dst amt gas : Nat) (m : List UInt8) (hm : m.length = 128) :
    (encTr src dst amt gas m).length = 153 := by
  simp [encTr, hm]

/-- **A deferred transfer is an `ItemOk` item**: `tr_call` (stack only) and the return to 45168. -/
theorem itemOk_tr {X : Type} (env : HeapHost X) (cap pb : Nat) {p : ByteArray} {P : Program} [HasCode p P]
    [HasCodeA p P] (src dst amt gas : Nat) (m : List UInt8) (hs : src < 4294967296) (hd : dst < 4294967296)
    (ha : amt < 18446744073709551616) (hg : gas < 18446744073709551616) (hm : m.length = 128) :
    ItemOk env cap pb p P 3821 (encTr src dst amt gas m) (RepTr src dst amt gas m) := by
  intro x ω μ hb s sp rd ip rlen S0 S1 H h0 h1 h7 h8 hsp hsp8 hSTk hrdsp hrdS hR0 hR8 hrl hrl32 henc hsrc
  rw [encTr_length _ _ _ _ _ hm] at hrl henc hsrc ⊢
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  -- the fields, from the encoding
  have piece : ∀ k n, k + n ≤ 153 → μ.readN (ip + k) n = ((encTr src dst amt gas m).drop k).take n :=
    fun k n h => by rw [← readN_drop_take μ ip 153 k n h, henc]
  have f1 : rdN μ ip 1 = 1 := by unfold rdN; rw [show ip = ip + 0 by rfl, piece 0 1 (by omega)]; rfl
  have fs : rdN μ (ip + 1) 4 = src := by
    unfold rdN; rw [piece 1 4 (by omega)]; simp [encTr, List.drop_append, List.take_append, List.drop_eq_nil_of_le, List.take_of_length_le, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hs]
  have fd : rdN μ (ip + 5) 4 = dst := by
    unfold rdN; rw [piece 5 4 (by omega)]; simp [encTr, List.drop_append, List.take_append, List.drop_eq_nil_of_le, List.take_of_length_le, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hd]
  have fa : rdN μ (ip + 9) 8 = amt := by
    unfold rdN; rw [piece 9 8 (by omega)]; simp [encTr, List.drop_append, List.take_append, List.drop_eq_nil_of_le, List.take_of_length_le, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt ha]
  have fm : μ.readN (ip + 17) 128 = m := by
    rw [piece 17 128 (by omega)]; simp [encTr, List.drop_append, List.take_append, List.drop_eq_nil_of_le, List.take_of_length_le, hm]
  have fg : rdN μ (ip + 145) 8 = gas := by
    unfold rdN; rw [piece 145 8 (by omega)]; simp [encTr, List.drop_append, List.take_append, List.drop_eq_nil_of_le, List.take_of_length_le, hm, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hg]
  obtain ⟨ω1, μ1, r1, e0, e1, e5, e6, o0, o8, o136, o144, o152, o156, R0, R8, fr, rdf, wrf⟩ :=
    tr_call (p := p) (P := P) (R := env.rel cap) x ω μ sp (sp + 88) rd ip rlen h1 h7 h8 hR0 hR8 hrl hrl32 f1
      ⟨by omega, by omega⟩
      (fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      ⟨by omega, by omega, hsp8⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inl (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have lo : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha' =>
    fr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have slot : ∀ k n, k + n ≤ 184 → ((μ1.readN (sp + 88) 184).drop k).take n = μ1.readN (sp + 88 + k) n :=
    fun k n h => readN_drop_take μ1 (sp + 88) 184 k n h
  refine Or.inl ⟨s, ω1, μ1, (r1.trans (lp_ret_tr (p := p) (P := P) (R := env.rel cap) x ω1 μ1
      (by rw [e0, h0]))).mono (by omega), by rw [e0, h0], e1, e5, e6, by rw [o0]; decide,
    HeapCtxC.keep_hi H lo wrf, fun c hc _ => hc, fun c hc hu a ha' => ?_, ⟨[], by simp, fun μ'' _ => ?_⟩,
    R0, R8, fun a h0 hs h1 h2 => fr a h0 (Or.inr hs) (by omega) h2⟩
  · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
    unfold InDataA at ha'
    exact lo a (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := slot 0 8 (by omega); simp only [List.drop_zero, Nat.add_zero] at this
      rw [this]; exact o0
    · rw [slot 8 128 (by omega), o8, fm]
    · rw [slot 136 8 (by omega)]; unfold rdN at o136 fa; rw [Nat.add_assoc, o136, fa]
    · rw [slot 144 8 (by omega)]; unfold rdN at o144 fg; rw [Nat.add_assoc, o144, fg]
    · rw [slot 152 4 (by omega)]; unfold rdN at o152 fs; rw [Nat.add_assoc, o152, fs]
    · rw [slot 156 4 (by omega)]; unfold rdN at o156 fd; rw [Nat.add_assoc, o156, fd]

/-- Peeling a read: a read of A ⌢ B is a read of A, then of B. -/
theorem readN_app (μ : Memory) (a : Nat) (A B : List UInt8)
    (h : μ.readN a (A.length + B.length) = A ++ B) :
    μ.readN a A.length = A ∧ μ.readN (a + A.length) B.length = B := by
  rw [PVM.Memory.readN_split] at h
  exact List.append_inj h (by simp)

/-- Equal words are equal octets. -/
theorem readN8_of_rdN {μ μ' : Memory} {o i : Nat} (h : rdN μ' o 8 = rdN μ i 8) : μ'.readN o 8 = μ.readN i 8 := by
  unfold rdN at h
  have e1 := encodeLE_decodeLE (μ'.readN o 8)
  have e2 := encodeLE_decodeLE (μ.readN i 8)
  simp only [PVM.Memory.length_readN] at e1 e2
  rw [← e1, ← e2, h]

/-- Four equal words are 32 equal octets. -/
theorem Words4.readN {μ μ' : Memory} {o i : Nat} (w : Words4 μ' o μ i) : μ'.readN o 32 = μ.readN i 32 := by
  obtain ⟨w0, w1, w2, w3⟩ := w
  have sp : ∀ (ν : Memory) (a : Nat), ν.readN a 32 =
      ν.readN a 8 ++ (ν.readN (a + 8) 8 ++ (ν.readN (a + 16) 8 ++ ν.readN (a + 24) 8)) := fun ν a => by
    rw [← PVM.Memory.readN_split, ← PVM.Memory.readN_split, ← PVM.Memory.readN_split]
  rw [sp μ' o, sp μ i, readN8_of_rdN w0, readN8_of_rdN w1, readN8_of_rdN w2, readN8_of_rdN w3]

/-- The chunk a `Vec<u8>` of n octets at ptr lives in: none for n = 0, else ptr's block. -/
def blk (n ptr : Nat) : List Chunk := if n = 0 then [] else [⟨ptr - 32, (n + 31) / 32 + 1, true⟩]

/-- **What `VAlloc` allocates is fresh**: the block is in the new state, used and distinct from every
    allocated chunk of the old one. -/
theorem VAlloc.blk_mem {pb hb n ptr : Nat} {s s' : State} (va : VAlloc pb hb n ptr s s') :
    ∀ c ∈ blk n ptr, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c := by
  rcases va with ⟨rfl, -, -⟩ | ⟨hpos, -, hnew, hfresh⟩
  · simp [blk]
  · have hne : n ≠ 0 := by omega
    intro c hc
    simp only [blk, hne, ↓reduceIte, List.mem_singleton] at hc
    subst hc; exact ⟨hnew, rfl, hfresh⟩

/-- **The n octets at ptr lie in the block's data**, for a block allocated in some well-formed state. -/
theorem blk_read {code : ByteArray} {pb n ptr S0 S1 : Nat} {s : State} {μ : Memory}
    (H : HeapCtxC code pb S0 S1 μ s) (hc : ∀ c ∈ blk n ptr, c ∈ chunks s) :
    ∀ μ1 μ2 : Memory, (∀ c ∈ blk n ptr, ∀ a, InDataA c a → μ1.read a = μ2.read a) →
      μ1.readN ptr n = μ2.readN ptr n := by
  intro μ1 μ2 h
  by_cases hne : n = 0
  · subst hne; simp [PVM.Memory.readN]
  · have hm := hc ⟨ptr - 32, (n + 31) / 32 + 1, true⟩ (by simp [blk, hne])
    obtain ⟨c1, c2, c3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hm rfl
    dsimp only at c1 c2 c3
    have := H.hb0
    exact PVM.Memory.readN_congr fun j hj => h ⟨ptr - 32, (n + 31) / 32 + 1, true⟩ (by simp [blk, hne]) (ptr + j)
      ⟨by dsimp only; omega, by dsimp only; omega⟩

end Services.Bootstrap.Acc
