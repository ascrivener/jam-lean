import Services.Bootstrap.Refine.DecodeVecN
import Services.Bootstrap.Refine.DecodeVec2C

/-!
# `Vec<Instruction>::decode`, every batch, the slots' chunks seen: the batch step

`BInv` is the state at 562 after the batches covering the first L of the n elements: the length L equal to the
capacity, the buffer q in its chunk of exactly L slots, slot j < L satisfying `reps j` with its chunks, the reader
past the first L encodings, the count Rc before the last batch and that batch b at S + 8 and S + 16 (Rc − b = n − L),
the heap of the call's start kept. `batch_step` runs one more batch, of b' = min(n − L, L) elements: the grow
(`w1G`, `g3x`, `realloc_call`, `g2r`, `v2gG`; the first L slots copied by `realloc`) and the element loop
(`loopAFCd_lowFD` at d = L). This is `DecodeVec2C.vec_twoC`'s second batch with 70 replaced by L. GP v0.8.0
Appendix B.4 (Ψ_R running bootstrap's code); `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVecNC

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop Services.Bootstrap.Refine.DecodeVec

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

/-- The buffer chunk of L slots at q. -/
abbrev bufC (q L : Nat) : Chunk := ⟨q - 32, (232 * L + 31) / 32 + 1, true⟩

/-- **The state at 562 after the batches covering the first L elements** (see the module doc). μ0, s0: the memory
    and heap at the call's start; out: the word at S. -/
structure BInv (env : RefineHost.Env) (pb : Nat) (gl : Nat → UInt8) (S rd P0 Lt : Nat) (es : List (List UInt8))
    (reps : Nat → List Chunk → List UInt8 → Memory → Prop) (cp : Chunk) (μ0 : Memory) (s0 : State)
    (L Rc b q : Nat) (ω : Regs) (μ : Memory) (s : State) : Prop where
  hL : 1 ≤ L ∧ L ≤ es.length
  hRb : b ≤ Rc ∧ Rc - b = es.length - L ∧ Rc < 4294967296
  r1 : ω[1] = UInt64.ofNat S
  r7 : ω[7] = UInt64.ofNat L
  m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 Rc
  m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 b
  m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd
  m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q
  m40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L
  m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q
  m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 L
  rP : μ.readN rd 8 = Num.encodeLE 8 (P0 + (es.take L).flatten.length)
  rL : μ.readN (rd + 8) 8 = Num.encodeLE 8 (Lt - (es.take L).flatten.length)
  heap : HeapCtx env pb S0 S1 μ s
  cbm : bufC q L ∈ chunks s
  el : ∃ csOf : Nat → List Chunk,
    (∀ j, j < L → (∀ c ∈ csOf j, c ∈ chunks s ∧ c.used = true ∧ c ≠ bufC q L ∧ c ≠ cp) ∧
      ∀ μ'' : Memory, (∀ c ∈ csOf j, ∀ a, InData c a → μ''.read a = μ.read a) →
        reps j (csOf j) (μ.readN (q + 232 * j) 232) μ'') ∧
    (∀ j j', j < L → j' < L → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j')
  keep : ∀ c ∈ chunks s0, c.used = true → c ∈ chunks s ∧ ∀ a, InData c a → μ.read a = μ0.read a
  fresh0 : ∀ d ∈ chunks s0, d.used = true → d ≠ bufC q L
  lo : ∀ a, S ≤ a → a < S + 8 → μ.read a = μ0.read a
  hi : ∀ a, a < 4294967296 → S + 528 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ.read a = μ0.read a
  glob : ∀ a, Glob a → μ.read a = gl a
  tab : μ.readN 67476 100 = Decode.Tag.table
  rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true

/-- `es.take (L + b)` is `es.take L` followed by the batch `(es.drop L).take b`. -/
theorem take_add' (es : List (List UInt8)) (L b : Nat) : es.take (L + b) = es.take L ++ (es.drop L).take b :=
  List.take_add ..

/-- **One more batch** (562 … 562): from `BInv` after L < n elements, the next batch of b' = min(n − L, L): the
    buffer grown to L + b' slots by `realloc` (the first L slots copied) and the batch decoded into slots
    L … L + b' − 1, giving `BInv` after L + b' elements. Or an allocation fails. The batch is below 128 elements
    (the decode loop's `OkFD`) and the buffer below 2³⁰ octets (`realloc_call`'s range). -/
theorem batch_step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat} (gl : Nat → UInt8)
    (x : RefineCtx) (S rd P0 Lt : Nat) (es : List (List UInt8)) (reps : Nat → List Chunk → List UInt8 → Memory → Prop)
    (cp : Chunk) (Ns : Nat → Nat) (μ0 : Memory) (s0 : State)
    (hel : ∀ j (hj : j < es.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd (Ns j) es[j] (reps j))
    (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hS : S0 + 2104 ≤ S ∧ S + 552 + 24 ≤ rd ∧ rd + 16 ≤ S1 ∧ S % 8 = 0)
    (hcp : cp ∈ chunks s0 ∧ cp.used = true)
    (hcpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a) (hP0 : 206864 ≤ P0)
    (hLt : es.flatten.length ≤ Lt ∧ Lt < 4294967296) (pay : μ0.readN P0 es.flatten.length = es.flatten)
    (hbig : 232 * es.length < 1073741760)
    (L Rc b q : Nat) (ω : Regs) (μ : Memory) (s : State)
    (I : BInv env pb gl S rd P0 Lt es reps cp μ0 s0 L Rc b q ω μ s) (hLn : L < es.length)
    (hb128 : min (es.length - L) L < 128) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (q' N : Nat),
      FreeStepsH p (refineContractK cap0 env) 562 ω μ x 562 ω' μ' x N ∧
      BInv env pb gl S rd P0 Lt es reps cp μ0 s0 (L + min (es.length - L) L) (es.length - L)
        (min (es.length - L) L) q' ω' μ' s') ∨
    ∃ N, Exhausts env cap0 pb p P 562 ω μ x N := by
  obtain ⟨hS0, hSr, hrS, hS8⟩ := hS
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm0, hcpu⟩ := hcp
  obtain ⟨hL1, hLn'⟩ := I.hL
  obtain ⟨hbR, hRb, hRc⟩ := I.hRb
  obtain ⟨n, hN⟩ : ∃ n, es.length = n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = n - L := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = min m L := ⟨_, rfl⟩
  rw [hN, ← hm, ← hb']
  rw [hN] at hLn hbig hb128 hRb
  rw [← hm, ← hb'] at hb128
  have hb'1 : 1 ≤ b' ∧ b' ≤ m ∧ b' ≤ L := by omega
  have H := I.heap
  have hst := H.st
  obtain ⟨hcbm, -⟩ : bufC q L ∈ chunks s ∧ True := ⟨I.cbm, trivial⟩
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H.wf hcbm rfl
  simp only [bufC] at hq0 hqT
  have hbT := H.hbT
  have hb0 := H.hb0
  -- the batch
  let es2 := (es.drop L).take b'
  have hl2 : es2.length = b' := by simp [es2]; omega
  have hg2 : ∀ j (hj : j < es2.length), es2[j] = es[L + j]'(by simp [es2] at hj; omega) := fun j hj => by
    simp [es2, List.getElem_take, List.getElem_drop]
  have hflat : es.flatten = (es.take L).flatten ++ es2.flatten ++ (es.drop (L + b')).flatten := by
    rw [← List.flatten_append, ← List.flatten_append, ← take_add', List.take_append_drop]
  generalize hf1 : (es.take L).flatten.length = f1
  generalize hf2 : es2.flatten.length = f2
  have hfll : f1 + f2 ≤ es.flatten.length := by
    rw [hflat]; simp only [List.length_append]; omega
  have htk : (es.take (L + b')).flatten.length = f1 + f2 := by
    rw [take_add', List.flatten_append, List.length_append, hf1]; exact congrArg (f1 + ·) hf2
  -- the cp data, unchanged since μ0
  obtain ⟨hcpm, hcpd0⟩ := I.keep cp hcpm0 hcpu
  -- 1. the next batch's grow
  obtain ⟨ω3, μ3, run3, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m32, fr3, rd3, wr3⟩ :=
    w1G (p := p) (P := P) (R := refineContractK cap0 env) x ω μ S Rc b L q ⟨by omega, by omega, hS8⟩
      (by omega) hRc ⟨hL1, by omega⟩ (by omega) I.r1 I.r7 I.m8 I.m16 I.m32 I.m40
      (fun a h1 h2 => hst a (by omega) (by omega))
  simp only [hRb, ← hm, ← hb'] at a5 a6 a10 m8 m16
  obtain ⟨ω4, μ4, run4, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr4, rd4, wr4⟩ :=
    g3x (p := p) (P := P) (R := refineContractK cap0 env) x ω3 μ3 (S - 40) (S + 296) L q (L + b') 8 14 m (L + b')
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨hL1, by omega⟩ ⟨by omega, by omega⟩ ⟨by decide, by decide⟩ (by omega)
      (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
  have hlow4 : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a h =>
    (fr4 a (by omega) (Or.inl (by omega))).trans (fr3 a (by omega) (Or.inl (by omega)))
  have H4 : HeapCtx env pb S0 S1 μ4 s := Decode.GrowOne.ctx_high H hlow4 (fun a => by rw [wr4, wr3])
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  -- `realloc`
  rcases Decode.ReallocCall.realloc_call (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω4 μ4 s (S - 40) q 8
      (232 * (L + b')) pb S0 S1 H4 ⟨_, hcbm, by simp only [bufC]; omega, rfl⟩ (by omega) (by omega) hba b1 b7 b9 b10
      (by decide) (by decide) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s3, bb, ω5, μ5, hR, run5, e7, H5, dat5, keep5, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp5, stk5, ro5, wr5, e0, e1,
      e5, e6, gl5, base5, frr⟩ |
    ⟨hR, ω5, μ5, run5, e7, -, -, e0, -, -, -, -⟩
  rotate_left
  · have run6 := Decode.VecU8.realloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (by rw [e0, b0])
    exact Or.inr ⟨_, Exhausts.of_realloc (run3.trans (run4.trans (run5.trans run6))) e7 hR⟩
  have run6 := Decode.VecU8.realloc_ret (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (by rw [e0, b0])
  have hcrE : cr = bufC r (L + b') := by
    cases cr; simp only [bufC] at hcra hcru hcrs ⊢; subst hcru hcrs; congr 1; omega
  subst hcrE
  obtain ⟨hr0, -, hrT⟩ := Decode.VecU8.chunk_in H5.wf hcrm rfl
  simp only [bufC] at hr0 hrT
  have hb5 := H5.hb0
  have hbT5 := H5.hbT
  have hst5 := H5.st
  obtain ⟨ω6, μ6, run6', c0, c1, c5, c6, cres, cres8, cres16, fr6, rd6, wr6⟩ :=
    Decode.VecU8.g2r (p := p) (P := P) (R := refineContractK cap0 env) x ω5 μ5 (S - 40) (S + 296) (232 * (L + b'))
      r 14 607 m (L + b') ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk5 _ (by omega) (by omega))]; exact n8)
      ⟨by decide, by decide, by decide⟩ jte_6 bs_607
      (fun a h1 h2 => Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => hst5 a (by omega) (by omega))
  have k63 : ∀ a, a < 4294967296 → S ≤ a → (a < S + 296 ∨ S + 320 ≤ a) → μ6.read a = μ3.read a :=
    fun a h0 h1 h2 => (fr6 a h0 h2).trans ((stk5 a h0 (by omega)).trans (fr4 a h0 (Or.inr (by omega))))
  have r63 : ∀ a l, S ≤ a → a + l ≤ 4294967296 → (a + l ≤ S + 296 ∨ S + 320 ≤ a) → μ6.readN a l = μ3.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => k63 _ (by omega) (by omega) (by omega))
  obtain ⟨ω7, μ7, run7, d1, d5, d32, d40, d48, fr7, rd7, wr7⟩ :=
    v2gG (p := p) (P := P) (R := refineContractK cap0 env) x ω6 μ6 S (L + b') b' r L ⟨by omega, by omega, hS8⟩
      (by omega) ⟨hb'1.1, by omega⟩ (by omega) ⟨hL1, by omega⟩ (by rw [c1]; congr 1; omega) c6 cres
      (by rw [show S + 304 = S + 296 + 8 by omega]; exact cres8)
      (by rw [r63 _ _ (by omega) (by omega) (by omega)]; exact m16)
      (by rw [r63 _ _ (by omega) (by omega) (by omega)]; exact m32)
      (fun a h1 h2 => by rw [rd6]; exact Memory.readable_of_writable (hst5 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr6]; exact hst5 a (by omega) (by omega))
  have hk73 : ∀ a, a < 4294967296 → S ≤ a → (a < S + 32 ∨ S + 56 ≤ a) → (a < S + 296 ∨ S + 320 ≤ a) →
      μ7.read a = μ3.read a := fun a h0 h1 h2 h3 => (fr7 a h0 h2).trans (k63 a h0 h1 h3)
  have r7m : ∀ a l, S ≤ a → a + l ≤ 4294967296 →
      (S + 24 ≤ a ∧ a + l ≤ S + 32 ∨ S + 56 ≤ a ∧ a + l ≤ S + 296 ∨ S + 320 ≤ a) → μ7.readN a l = μ.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj =>
      (hk73 _ (by omega) (by omega) (by omega) (by omega)).trans (fr3 _ (by omega) (by omega)))
  have hlow7 : ∀ a, a < 2147483648 → μ7.read a = μ5.read a := fun a h =>
    (fr7 a (by omega) (Or.inl (by omega))).trans (fr6 a (by omega) (Or.inl (by omega)))
  have H7 : HeapCtx env pb S0 S1 μ7 s3 := Decode.GrowOne.ctx_high H5 hlow7 (fun a => by rw [wr7, wr6])
  have run37 := run3.trans (run4.trans (run5.trans (run6.trans (run6'.trans run7))))
  obtain ⟨tab7, rtab7⟩ := ExitRun.ro_keep H run37 (a := 67476) (l := 100) (by omega)
  -- the payload's chunk
  have ainj : ∀ c ∈ chunks s, ∀ d ∈ chunks s, c.addr = d.addr → c = d := by
    have ht := H.wf.2.2.2.1; unfold TilesOk at ht; exact Tiles.addr_inj ht
  have hne2q : ∀ c ∈ chunks s, c ≠ bufC q L → c.addr + 32 ≠ q :=
    fun c hc hne e => hne (ainj _ hc _ hcbm (by simp only [bufC]; omega))
  have hcpne : cp ≠ bufC q L := I.fresh0 cp hcpm0 hcpu
  have hcp3 : cp ∈ chunks s3 := keep5 cp hcpm hcpu (hne2q cp hcpm hcpne)
  have hcpd7 : ∀ a, InData cp a → μ7.read a = μ0.read a := fun a ha => by
    have ha' := ha; unfold InData at ha'
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
    rw [hlow7 a (by omega), kp5 a ⟨cp, hcpm, hcpu, hne2q cp hcpm hcpne, ha⟩, hlow4 a (by omega), hcpd0 a ha]
  have pay2 : μ7.readN (P0 + f1) f2 = es2.flatten := by
    rw [Memory.readN_congr (fun j hj => hcpd7 _ (hcpd _ (by omega) (by omega))),
      Decode.Loop.readN_sub μ0 P0 es.flatten.length f1 f2 _ pay hfll, hflat, ← hf1, ← hf2,
      List.append_assoc, List.drop_left]
    exact List.take_left' rfl
  have hr8 : r % 8 = 0 := by
    have ht := H5.wf.2.2.2.1; unfold TilesOk at ht
    have := Decode.VecKey336.tiles_mod _ _ ht _ hcrm
    simp only [bufC] at this
    have := H5.wf.2.1
    omega
  have hR1 : realloc (growTo pb) hb s q 1 ((232 * (L + b') + 31) / 32) = some (r, s3, bb) := hR
  have hfr := Decode.VecU8.realloc_fresh H.wf ⟨_, hcbm, by simp only [bufC]; omega, rfl⟩ (by omega) hR1
  have hncr : ∀ c ∈ chunks s, c.used = true → c ≠ bufC q L → c ≠ bufC r (L + b') := fun c hc hu hne e =>
    hfr c hc hu (hne2q c hc hne) (by rw [e]; simp only [bufC]; omega)
  have hcpcr : cp ≠ bufC r (L + b') := hncr cp hcpm hcpu hcpne
  have hapart := PassLoop.chunk_apart H5.wf hcp3 hcrm hcpcr
  simp only [bufC] at hapart
  obtain ⟨hcp0, -, hcpT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
  have hflat1 : 1 ≤ es.flatten.length := by
    have h0 := off_lt es 0 (by omega)
    have h1 := hne 0 (by omega)
    omega
  have hcpP0 := hcpd P0 (Nat.le_refl _) (by omega)
  unfold InData at hcpP0
  have hcpE : P0 + es.flatten.length ≤ cp.addr + 32 * cp.size := by
    have := hcpd (P0 + es.flatten.length - 1) (by omega) (by omega)
    unfold InData at this; omega
  have ok2 : OkFD (S - 56) rd (P0 + f1) (Lt - f1) es2 L r :=
    ⟨by omega, ⟨by rcases hapart with h | h <;> omega, by omega⟩, hr8, by omega,
      fun j hj => by rw [hg2 j hj]; exact hne _ _, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega⟩
  have hoff0 : off es2 0 = 0 := by simp [off]
  have inv7 : InvAFCd env pb (S - 56) rd (P0 + f1) (Lt - f1) es2 (fun j => reps (L + j)) L 0 r cp
      (bufC r (L + b')) ω7 μ7 s3 :=
    ⟨by rw [d1]; congr 1; omega, by rw [hl2, Nat.sub_zero]; exact d5,
      by rw [show S - 56 + 80 = S + 24 by omega, r7m _ _ (by omega) (by omega) (by omega)]; exact I.m24,
      by rw [show S - 56 + 96 = S + 40 by omega, hl2]; exact d40,
      by rw [show S - 56 + 104 = S + 48 by omega]; exact d48,
      by rw [show S - 56 + 112 = S + 56 by omega, r7m _ _ (by omega) (by omega) (by omega), Nat.add_zero]; exact I.m56,
      by rw [r7m _ _ (by omega) (by omega) (by omega), I.rP, hoff0, Nat.add_zero, hf1],
      by rw [r7m _ _ (by omega) (by omega) (by omega), I.rL, hoff0, Nat.sub_zero, hf1],
      by rw [hf2]; exact pay2, tab7.trans I.tab,
      ⟨fun _ => [], fun j hj => absurd hj (Nat.not_lt_zero _), fun j j' hj => absurd hj (Nat.not_lt_zero _)⟩,
      fun a h1 h2 => H7.st a (by omega) (by omega), fun a h1 h2 => H7.st a (by omega) (by omega),
      fun a h1 h2 => by rw [rtab7 a h1 h2]; exact I.rt a h1 h2, H7, ⟨hcp3, hcpu⟩,
      fun a h1 h2 => hcpd a (by omega) (by rw [hf2] at h2; omega), ⟨hcrm, rfl⟩,
      fun a h1 h2 => ⟨by simp only [bufC]; omega, by simp only [bufC]; omega⟩⟩
  have hg7 : ∀ a, Glob a → μ7.read a = gl a := fun a ha => by
    have hg' := ha; unfold Glob at hg'
    rw [hlow7 a (by omega), gl5 a ha, hlow4 a (by omega), I.glob a ha]
  have hel2 : ∀ j (hj : j < es2.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd
      (Ns (L + j)) es2[j] (reps (L + j)) := fun j hj => by rw [hg2 j hj]; exact hel _ _
  -- 2. the batch
  rcases loopAFCd_lowFD (p := p) (P := P) env cap0 pb gl (S - 56) rd (P0 + f1) (Lt - f1) (fun j => Ns (L + j)) x
      es2 (fun j => reps (L + j)) L r cp _ ok2 (by omega) hel2 es2.length 0 ω7 μ7 s3
      (by omega) (by omega) inv7 hg7 with
    ⟨ω8, μ8, s4, run8, inv8, fr8, low8, b88', w7', csOf2, el2, fresh2⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, Exhausts.pre run37 hx⟩
  obtain ⟨fr8a, fr8b, fr8c, fr8d, fr8e, fr8f⟩ := fr8
  have hF : S - 56 + 56 = S := by omega
  have hlow8 : ∀ a, a < 2147483648 → μ8.read a = μ7.read a → True := fun _ _ _ => trivial
  have r87 : ∀ a l, S ≤ a → a + l ≤ S + 24 → μ8.readN a l = μ7.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => low8 _ (by omega) (by omega))
  have r73 : ∀ a l, S ≤ a → a + l ≤ S + 32 → μ7.readN a l = μ3.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => hk73 _ (by omega) (by omega) (by omega) (by omega))
  have hoff2 : off es2 es2.length = f2 := by rw [← hf2]; simp [off]
  -- the chunks kept from s through `realloc`
  have hk1 : ∀ c ∈ chunks s, c.used = true → c ≠ bufC q L →
      c ∈ chunks s4 ∧ ∀ a, InData c a → μ8.read a = μ.read a := fun c hc hu hne => by
    have hc3 := keep5 c hc hu (hne2q c hc hne)
    have hc' := hncr c hc hu hne
    refine ⟨fr8b c hc3 hu, fun a ha => ?_⟩
    have ha' := ha; unfold InData at ha'
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
    have hdj := Decode.VecU8.data_disj H5.wf hc3 hcrm hc' ha
    simp only [bufC] at hdj
    rw [fr8c c hc3 hu a ha (by omega), hlow7 a (by omega), kp5 a ⟨c, hc, hu, hne2q c hc hne, ha⟩, hlow4 a (by omega)]
  -- the first L slots, copied by `realloc`
  have hu2 : usable s q = (232 * L + 31) / 32 := by
    have := Decode.VecU8.usable_of_chunk hcbm
    simp only [bufC] at this
    rw [show q - 32 + 32 = q by omega] at this
    rw [this]; omega
  rw [hu2, Nat.min_eq_left (by omega)] at dat5
  have slot1 : ∀ j, j < L → μ8.readN (r + 232 * j) 232 = μ.readN (q + 232 * j) 232 := fun j hj => by
    have e5 := Decode.VecKey336.readN_sub336 (i := 232 * j) (m := 232)
      (Decode.VecU8.readN_prefix (n := 232 * L) (by omega) dat5) (by omega)
    rw [Memory.readN_congr (fun i hi =>
      (fr8c _ hcrm rfl _ ⟨by simp only [bufC]; omega, by simp only [bufC]; omega⟩ (by omega)).trans
        (hlow7 _ (by omega))), e5, Memory.readN_congr (fun i hi => hlow4 _ (by omega))]
  obtain ⟨csOf1, el1a, el1b⟩ := I.el
  have tab8 : μ8.readN 67476 100 = Decode.Tag.table :=
    (Memory.readN_congr (fun j hj => (fr8d _ (by omega)).1)).trans (tab7.trans I.tab)
  have rt8 : ∀ a, 67476 ≤ a → a < 67576 → μ8.readable a = true := fun a h1 h2 => by
    rw [(fr8d a (by omega)).2, rtab7 a h1 h2]; exact I.rt a h1 h2
  refine Or.inl ⟨ω8, μ8, s4, r, _, run37.trans run8, ⟨⟨by omega, by omega⟩, ⟨hb'1.2.1, by omega, by omega⟩,
    by rw [inv8.r1, hF], by rw [w7', hl2], by rw [r87 _ _ (by omega) (by omega), r73 _ _ (by omega) (by omega)]; exact m8,
    by rw [r87 _ _ (by omega) (by omega), r73 _ _ (by omega) (by omega)]; exact m16,
    by have := inv8.m24; rwa [show S - 56 + 80 = S + 24 by omega] at this,
    by rw [show S + 32 = S - 56 + 88 by omega]; exact b88',
    by have := inv8.m40; rwa [show S - 56 + 96 = S + 40 by omega, hl2] at this,
    by have := inv8.m48; rwa [show S - 56 + 104 = S + 48 by omega] at this,
    by have := inv8.m56; rwa [show S - 56 + 112 = S + 56 by omega, hl2] at this,
    by have := inv8.rP; rw [hoff2] at this; rw [htk, ← Nat.add_assoc]; exact this,
    by have := inv8.rL; rw [hoff2] at this; rw [htk, show Lt - (f1 + f2) = Lt - f1 - f2 by omega]; exact this,
    inv8.heap, fr8b _ hcrm rfl,
    ⟨fun j => if j < L then csOf1 j else csOf2 (j - L), fun j hj => ?_, fun j j' hj hj' hne c hc => ?_⟩,
    fun c hc hu => ?_, fun d hd hu => ?_, fun a h0 h1 => ?_, fun a h0 h1 h2 => ?_, fun a ha => ?_,
    tab8, rt8⟩⟩
  · by_cases hjL : j < L
    · simp only [hjL, ↓reduceIte]
      obtain ⟨hcs, hrep⟩ := el1a j hjL
      refine ⟨fun c hc => ?_, fun μ'' hag => ?_⟩
      · obtain ⟨hc2, hcu, hcb, hcp'⟩ := hcs c hc
        exact ⟨(hk1 c hc2 hcu hcb).1, hcu, hncr c hc2 hcu hcb, hcp'⟩
      · rw [slot1 j hjL]
        exact hrep μ'' (fun c hc a ha =>
          (hag c hc a ha).trans ((hk1 c (hcs c hc).1 (hcs c hc).2.1 (hcs c hc).2.2.1).2 a ha))
    · simp only [hjL, ↓reduceIte]
      obtain ⟨hcs, hrep⟩ := el2.1 (j - L) (by rw [hl2]; omega)
      refine ⟨fun c hc => hcs c hc, fun μ'' hag => ?_⟩
      have := hrep μ'' hag
      simp only at this
      rw [show L + (j - L) = j by omega] at this
      exact this
  · by_cases hjL : j < L <;> by_cases hjL' : j' < L <;> simp only [hjL, hjL', ↓reduceIte] at hc ⊢
    · exact el1b j j' hjL hjL' hne c hc
    · intro hc'
      obtain ⟨hc2, hcu, hcb, -⟩ := (el1a j hjL).1 c hc
      exact fresh2 (j' - L) (Nat.zero_le _) (by rw [hl2]; omega) c hc' c
        (keep5 c hc2 hcu (hne2q c hc2 hcb)) hcu rfl
    · intro hc'
      obtain ⟨hc2, hcu, hcb, -⟩ := (el1a j' hjL').1 c hc'
      exact fresh2 (j - L) (Nat.zero_le _) (by rw [hl2]; omega) c hc c
        (keep5 c hc2 hcu (hne2q c hc2 hcb)) hcu rfl
    · exact el2.2 (j - L) (j' - L) (by rw [hl2]; omega) (by rw [hl2]; omega) (by omega) c hc
  · obtain ⟨hc1, hd1⟩ := I.keep c hc hu
    have hcb := I.fresh0 c hc hu
    obtain ⟨hc4, hd4⟩ := hk1 c hc1 hu hcb
    exact ⟨hc4, fun a ha => (hd4 a ha).trans (hd1 a ha)⟩
  · exact hncr d (I.keep d hd hu).1 hu (I.fresh0 d hd hu)
  · rw [low8 a (by omega) (by omega), hk73 a (by omega) h0 (by omega) (by omega), fr3 a (by omega) (by omega)]
    exact I.lo a h0 h1
  · rw [fr8a a (by omega) h0 h2, hk73 a h0 (by omega) (by omega) (by omega), fr3 a h0 (by omega)]
    exact I.hi a h0 h1 h2
  · have hg' := ha; unfold Glob at hg'
    rw [fr8e a ha, hg7 a ha]

end Services.Bootstrap.Refine.DecodeVecNC
