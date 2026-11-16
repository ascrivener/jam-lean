import Services.Bootstrap.Acc.ItemsLoop.OutDec
import Services.Bootstrap.Acc.ItemsLoop.OpSeg

/-!
# The operand arm from the item's log line to row 8 (7009 → 8013, R2)

After the item's log line (7009) with a work output out (its capacity at sp + 288, not −1; its
pointer and length at sp + 296 / sp + 304): the decode's reader is set up (`op_ok_pre`), the decode
runs (`OutDecH`, R3), and
- a decode error goes to the `panic` at 15361 (`od_fail`; spec `onWorkItem`'s `none => panic`);
- a decoded (is, item) with no instructions sets up the empty results `Vec` { 0, 8, 0 } (`od_ok0`);
- otherwise the results `Vec` gets capacity n = |is|: `alloc(144·n, 8)` (`od_okn`, `alloc_callG`),
  null → the trap 15364 (heap exhaustion), else { n, r, 0 } (`od_alloc`);
and the package hash is copied to sp + 512, reaching row 8 at 8013 (`At8013`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.InstrLoop Services.Bootstrap.Acc.Handlers.HeapKeep
open JAM.Codec (fixed)

/-- A slot's buffers are among `vecFree`'s. -/
theorem mem_vecFree {B : InstrRep} {μ : Memory} {b c m k q : Nat} (hk : k < m) (hq : q ∈ B.foot (slot μ b k)) :
    q ∈ vecFree B μ b c m :=
  List.mem_append_left _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hq⟩)

/-- Four equal words make an equal 32-octet read. -/
theorem readN32_of_words {μ μ' : Memory} {a a' : Nat}
    (h0 : rdN μ' a' 8 = rdN μ a 8) (h1 : rdN μ' (a' + 8) 8 = rdN μ (a + 8) 8)
    (h2 : rdN μ' (a' + 16) 8 = rdN μ (a + 16) 8) (h3 : rdN μ' (a' + 24) 8 = rdN μ (a + 24) 8) :
    μ'.readN a' 32 = μ.readN a 32 := by
  have e : ∀ (ν : Memory) (x : Nat), ν.readN x 32 =
      ν.readN x 8 ++ (ν.readN (x + 8) 8 ++ (ν.readN (x + 16) 8 ++ ν.readN (x + 24) 8)) := by
    intro ν x
    rw [show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, PVM.Memory.readN_split, PVM.Memory.readN_split,
      PVM.Memory.readN_split]
  rw [e, e, Handlers.KeyEnc.readN_enc μ' a' 8, Handlers.KeyEnc.readN_enc μ' (a' + 8) 8, Handlers.KeyEnc.readN_enc μ' (a' + 16) 8, Handlers.KeyEnc.readN_enc μ' (a' + 24) 8,
    Handlers.KeyEnc.readN_enc μ a 8, Handlers.KeyEnc.readN_enc μ (a + 8) 8, Handlers.KeyEnc.readN_enc μ (a + 16) 8, Handlers.KeyEnc.readN_enc μ (a + 24) 8]
  unfold rdN at h0 h1 h2 h3
  rw [h0, h1, h2, h3]

/-- A word holding a two-octet read starts with those two octets. -/
theorem readN2_of_word {μ μ' : Memory} {a a' : Nat} (h : rdN μ' a' 8 = rdN μ a 2) :
    μ'.readN a' 2 = μ.readN a 2 := by
  have e := readN_drop_take μ' a' 8 0 2 (by omega)
  simp only [List.drop_zero, Nat.add_zero] at e
  rw [← e, Handlers.KeyEnc.readN_enc μ' a' 8]
  unfold rdN at h
  rw [h]
  have : (Num.encodeLE 8 (Num.decodeLE (μ.readN a 2))).take 2 = Num.encodeLE 2 (Num.decodeLE (μ.readN a 2)) := by
    simp [Num.encodeLE]
  rw [this]
  have := PVM.encodeLE_decodeLE (μ.readN a 2)
  rw [PVM.Memory.length_readN] at this
  exact this

/-- **`VecOwn` survives a frame that keeps every allocated chunk with its data.** -/
theorem VecOwn.keep {B : InstrRep} {μ μ' : Memory} {st st' : State} {b c : Nat} {is : List Spec.Instr}
    (V : VecOwn B μ st b c is)
    (hk : ∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    VecOwn B μ' st' b c is ∧ vecFree B μ' b c is.length = vecFree B μ b c is.length := by
  have hsl : ∀ k, k < is.length → slot μ' b k = slot μ b k := by
    intro k hkl
    obtain ⟨-, d, hd, hdu, hda, hde⟩ := V.slots (List.ne_nil_of_length_pos (by omega))
    unfold slot
    exact Memory.readN_congr fun j hj => (hk d hd hdu).2 _ ⟨by omega, by
      have : 232 * k + 232 ≤ 232 * is.length := by omega
      omega⟩
  have hvf : vecFree B μ' b c is.length = vecFree B μ b c is.length := by
    unfold vecFree
    rw [flatMap_range_congr is.length fun k hkl => by rw [hsl k hkl]]
  refine ⟨⟨fun k hkl => ?_, by rw [hvf]; exact V.nodup, fun q hq => ?_, fun hne => ?_⟩, hvf⟩
  · rw [hsl k hkl]
    refine B.frame _ _ μ μ' st (V.rep k hkl) fun q hq => ?_
    obtain ⟨d, hd, hdu, hda⟩ := V.owned q (mem_vecFree hkl hq)
    exact ⟨d, hd, hdu, hda, (hk d hd hdu).2⟩
  · rw [hvf] at hq
    obtain ⟨d, hd, hdu, hda⟩ := V.owned q hq
    exact ⟨d, (hk d hd hdu).1, hdu, hda⟩
  · obtain ⟨h0, d, hd, hdu, hda, hde⟩ := V.slots hne
    exact ⟨h0, d, (hk d hd hdu).1, hdu, hda, hde⟩

/-- **The state at row 8 (8013)** after the decode, against the state s₁ at 7009 (memory μ₁, allocator
    state st₁): the decoded instructions is in the `Vec` { c, b } (`VecOwn` for st₂, fresh buffers), b in
    ω₆; the results `Vec` at sp + 448: empty { 0, 8, 0 } if is = [], else { |is|, r, 0 } with r the data of a
    fresh allocated chunk of 144·|is| octets; the item at sp + 176, the package copied to sp + 512, the
    work output's capacity at sp + 128 and pointer at sp + 104; the rest of the memory from sp up, the
    statics and the octets below 196608 kept. -/
structure At8013 (env : AccEnv) (B : InstrRep) (pb S0 S1 sp cp ptr : Nat) (st₁ : State) (μ₁ : Memory)
    (is : List Spec.Instr) (item b c rp : Nat) (st₂ : State) (s₂ : St Stream) : Prop where
  pc : s₂.i = 8013
  r1 : s₂.ω[1] = UInt64.ofNat sp
  r6 : s₂.ω[6] = UInt64.ofNat b
  H : HeapCtxC env.code pb S0 S1 s₂.μ st₂
  keep : ∀ d ∈ chunks st₁, d.used = true → d ∈ chunks st₂ ∧ ∀ a, InData d a → s₂.μ.read a = μ₁.read a
  V : VecOwn B s₂.μ st₂ b c is
  hb8 : b % 8 = 0
  hb : b + 232 * is.length < 2 ^ 64
  fresh : ∀ q ∈ vecFree B s₂.μ b c is.length, ∀ d ∈ chunks st₁, d.used = true → d.addr + 32 ≠ q
  res : (is = [] ∧ rdN s₂.μ (sp + 448) 8 = 0 ∧ rp = 8) ∨
    (is ≠ [] ∧ rdN s₂.μ (sp + 448) 8 = is.length ∧
      (⟨rp - 32, (144 * is.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks st₂ ∧
      (∀ d ∈ chunks st₁, d.used = true → d.addr + 32 ≠ rp) ∧ rp ∉ vecFree B s₂.μ b c is.length)
  m456 : rdN s₂.μ (sp + 456) 8 = rp
  m464 : rdN s₂.μ (sp + 464) 8 = 0
  m240 : rdN s₂.μ (sp + 240) 8 = c
  m248 : rdN s₂.μ (sp + 248) 8 = is.length
  m176 : s₂.μ.readN (sp + 176) 2 = fixed 2 item
  m128 : rdN s₂.μ (sp + 128) 8 = cp
  m104 : rdN s₂.μ (sp + 104) 8 = ptr
  pkg : s₂.μ.readN (sp + 512) 32 = μ₁.readN (sp + 312) 32
  frame : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 104 ∨ sp + 112 ≤ a) → (a < sp + 128 ∨ sp + 136 ≤ a) →
    (a < sp + 176 ∨ sp + 184 ≤ a) → (a < sp + 240 ∨ sp + 256 ≤ a) → (a < sp + 448 ∨ sp + 472 ≤ a) →
    (a < sp + 512 ∨ sp + 544 ≤ a) → (a < sp + 1144 ∨ sp + 1160 ≤ a) → (a < sp + 1568 ∨ sp + 1600 ≤ a) →
    s₂.μ.read a = μ₁.read a
  glob : ∀ a, Glob a → s₂.μ.read a = μ₁.read a
  lo : ∀ a, a < 196608 → s₂.μ.read a = μ₁.read a ∧ s₂.μ.readable a = μ₁.readable a

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The operand arm from 7009 to row 8 (8013)** (see the module doc): an early ☇ (the decode's
    `ExhaustsP`, or the results' allocation failing at 15364); or a decode error and the run ends ☇ at
    15361; or `decode (Dec.output C) out = some (is, item)` and the run reaches 8013 in `At8013`, keeping
    the context. Named hypothesis: `OutDecH` (R3). -/
theorem op_dec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (B : InstrRep)
    (C : Spec.Consts) {Ab : St Stream → Prop} {pb S0 S1 : Nat} (cap : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hAb2 : ∀ s : St Stream, s.i = 15364 → Ab s)
    (hOD : OutDecH B C p env pb S0 S1)
    (s₁ : St Stream) (st₁ : State) (sp cp ptr : Nat) (out : List UInt8)
    (hi : s₁.i = 7009) (h1 : s₁.ω[1] = UInt64.ofNat sp) (H : HeapCtxC env.code pb S0 S1 s₁.μ st₁)
    (hstk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1) (hsp : 2147483992 ≤ sp ∧ sp % 8 = 0)
    (m288 : rdN s₁.μ (sp + 288) 8 = cp) (hcp : cp ≠ 18446744073709551615)
    (m296 : rdN s₁.μ (sp + 296) 8 = ptr) (m304 : rdN s₁.μ (sp + 304) 8 = out.length)
    (hout : s₁.μ.readN ptr out.length = out)
    (hrd : ∀ a, ptr ≤ a → a < ptr + out.length → s₁.μ.readable a = true)
    (hpo : ptr + out.length ≤ 2147483648) :
    Aborts p (KeepCtx (accContractS env)) Ab s₁ s₁.c ∨
    (Spec.decode (Spec.Dec.output C) out = none ∧ Ends p (KeepCtx (accContractS env)) s₁ .panic s₁.c) ∨
    ∃ is item, Spec.decode (Spec.Dec.output C) out = some (is, item) ∧
      ∃ b c rp st₂ s₂, Reaches p (KeepCtx (accContractS env)) s₁ s₂ ∧ s₂.c = s₁.c ∧
        At8013 env B pb S0 S1 sp cp ptr st₁ s₁.μ is item b c rp st₂ s₂ := by
  obtain ⟨i0, ω, μ, cx, f⟩ := s₁
  dsimp only at hi h1 H m288 m296 m304 hout hrd ⊢
  subst hi
  have hS1 := H.hS1
  have hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true := fun a h1 h2 => H.st a (by omega) (by omega)
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf a h1 h2)
  -- 7009 → 7050
  obtain ⟨ω1, μ1, r1, a1, a5, a6, a7, a8, n104, n1144, n1152, fr1, rd1, wr1⟩ :=
    op_ok_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω μ sp cp ptr out.length h1
      ⟨by omega, by omega⟩ m288 hcp m296 m304 hrf hwf
  have lo1 : ∀ a, a < sp → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (.inl (by omega)) (.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 st₁ := HeapCtxC.keep_hi H (fun a ha => lo1 a (by omega)) wr1
  -- the decode, 7050 → 7080
  rcases hOD cx f ω1 μ1 st₁ sp ptr out H1 a1 a5 a7 a8 hstk.1 hstk.2 (by omega) hsp.2 n1144 n1152
      (by rw [Memory.readN_congr fun j hj => lo1 _ (by omega)]; exact hout)
      (fun a h1 h2 => by rw [rd1]; exact hrd a h1 h2) with
    ⟨st₂, ω2, μ2, N2, r2, H2, b1, b5, b6, keep2, fr2, gl2, lo2, res2⟩ | hx
  rotate_left
  · exact .inl (Aborts.prepend (s' := ⟨7050, ω1, μ1, cx, f⟩) ⟨_, r1⟩
      (aborts_of_exhaustsP hAb ⟨7050, ω1, μ1, cx, f⟩ hx))
  have g1 : ω2[1] = UInt64.ofNat sp := b1.trans a1
  have g5 : ω2[5] = UInt64.ofNat 18446744073709551615 := b5.trans a5
  have g6 : ω2[6] = UInt64.ofNat cp := b6.trans a6
  have hwf2 : ∀ a, sp ≤ a → a < sp + 1856 → μ2.writable a = true := fun a h1 h2 => H2.st a (by omega) (by omega)
  have hrf2 : ∀ a, sp ≤ a → a < sp + 1856 → μ2.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf2 a h1 h2)
  -- μ2 against μ: from sp up off the changed words; the heap; the statics; below 196608
  have st2 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 104 ∨ sp + 112 ≤ a) → (a < sp + 1144 ∨ sp + 1160 ≤ a) →
      (a < sp + 1568 ∨ sp + 1600 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 h3 h4 => by
    rw [fr2 a h0 h1 h3 h4, fr1 a h0 h2 h3]
  have kp2 : ∀ d ∈ chunks st₁, d.used = true → d ∈ chunks st₂ ∧ ∀ a, InData d a → μ2.read a = μ.read a :=
    fun d hd hu => ⟨(keep2 d hd hu).1, fun a ha => by
      rw [(keep2 d hd hu).2 a ha, lo1 a (by have := heapC_data_lt H hd ha; omega)]⟩
  have gl2' : ∀ a, Glob a → μ2.read a = μ.read a := fun a ha => by
    rw [gl2 a ha, lo1 a (by unfold Glob at ha; omega)]
  have lo2' : ∀ a, a < 196608 → μ2.read a = μ.read a ∧ μ2.readable a = μ.readable a := fun a ha => by
    rw [(lo2 a ha).1, (lo2 a ha).2, lo1 a (by omega), rd1]; exact ⟨rfl, rfl⟩
  have run2 := r1.trans r2
  unfold OutDecRes at res2
  split at res2
  rotate_left
  · -- a decode error: 7080 → 15361
    next hdec =>
    obtain ⟨ω3, r3⟩ := od_fail (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω2 μ2 sp g1 g5
      ⟨by omega, by omega⟩ res2 hrf2
    exact .inr (.inl ⟨hdec, ends_of_15361 (P := P) ⟨7009, ω, μ, cx, f⟩ (run2.trans r3)⟩)
  next is item hdec =>
  obtain ⟨b, c, e1568, hc, e1576, e1584, e1592, V, hb8, hb, hfr⟩ := res2
  suffices hs : Aborts p (KeepCtx (accContractS env)) Ab ⟨7009, ω, μ, cx, f⟩ cx ∨
      ∃ b c rp st₂ s₂, Reaches p (KeepCtx (accContractS env)) ⟨7009, ω, μ, cx, f⟩ s₂ ∧ s₂.c = cx ∧
        At8013 env B pb S0 S1 sp cp ptr st₁ μ is item b c rp st₂ s₂ by
    rcases hs with h | h
    · exact .inl h
    · exact .inr (.inr ⟨is, item, hdec, h⟩)
  -- the end at 8013, from a run 7080 → 8013 (memory μ3, allocator state st₃)
  have fin : ∀ (rp : Nat) (st₃ : State) (ω3 : Regs) (μ3 : Memory) (N3 : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 7080 ω2 μ2 (cx, f) 8013 ω3 μ3 (cx, f) N3 →
      HeapCtxC env.code pb S0 S1 μ3 st₃ →
      (∀ d ∈ chunks st₂, d.used = true → d ∈ chunks st₃ ∧ ∀ a, InData d a → μ3.read a = μ2.read a) →
      ω3[1] = UInt64.ofNat sp → ω3[6] = UInt64.ofNat b →
      rdN μ3 (sp + 240) 8 = c → rdN μ3 (sp + 128) 8 = cp → rdN μ3 (sp + 176) 8 = rdN μ2 (sp + 1592) 2 →
      rdN μ3 (sp + 248) 8 = is.length → rdN μ3 (sp + 456) 8 = rp → rdN μ3 (sp + 464) 8 = 0 →
      rdN μ3 (sp + 512) 8 = rdN μ2 (sp + 312) 8 → rdN μ3 (sp + 520) 8 = rdN μ2 (sp + 320) 8 →
      rdN μ3 (sp + 528) 8 = rdN μ2 (sp + 328) 8 → rdN μ3 (sp + 536) 8 = rdN μ2 (sp + 336) 8 →
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 128 ∨ sp + 136 ≤ a) → (a < sp + 176 ∨ sp + 184 ≤ a) →
        (a < sp + 240 ∨ sp + 256 ≤ a) → (a < sp + 448 ∨ sp + 472 ≤ a) → (a < sp + 512 ∨ sp + 544 ≤ a) →
        μ3.read a = μ2.read a) →
      (∀ a, Glob a → μ3.read a = μ2.read a) →
      (∀ a, a < 196608 → μ3.read a = μ2.read a ∧ μ3.readable a = μ2.readable a) →
      ((is = [] ∧ rdN μ3 (sp + 448) 8 = 0 ∧ rp = 8) ∨
        (is ≠ [] ∧ rdN μ3 (sp + 448) 8 = is.length ∧
          (⟨rp - 32, (144 * is.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks st₃ ∧
          ∀ d ∈ chunks st₂, d.used = true → d.addr + 32 ≠ rp)) →
      ∃ b c rp st₂ s₂, Reaches p (KeepCtx (accContractS env)) ⟨7009, ω, μ, cx, f⟩ s₂ ∧ s₂.c = cx ∧
        At8013 env B pb S0 S1 sp cp ptr st₁ μ is item b c rp st₂ s₂ := by
    intro rp st₃ ω3 μ3 N3 r3 H3 kp3 h31 h36 m240 m128 m176 m248 m456 m464 p0 p1 p2 p3 fr3 gl3 lo3 res3
    obtain ⟨V3, hvf⟩ := VecOwn.keep V kp3
    refine ⟨b, c, rp, st₃, ⟨8013, ω3, μ3, cx, f⟩, ⟨_, run2.trans r3⟩, rfl, ⟨rfl, h31, h36, H3,
      fun d hd hu => ?_, V3, hb8, hb, ?_, ?_, m456, m464, m240, m248, ?_, m128, ?_, ?_, ?_, ?_, ?_⟩⟩
    · obtain ⟨h2, k2⟩ := kp2 d hd hu
      obtain ⟨h3, k3⟩ := kp3 d h2 hu
      exact ⟨h3, fun a ha => (k3 a ha).trans (k2 a ha)⟩
    · rw [hvf]; exact hfr
    · rcases res3 with ⟨h0, h448, hrp⟩ | ⟨h0, h448, hnew, hfr3⟩
      · exact .inl ⟨h0, h448, hrp⟩
      · refine .inr ⟨h0, h448, hnew, fun d hd hu => hfr3 d (kp2 d hd hu).1 hu, ?_⟩
        rw [hvf]
        intro hq
        obtain ⟨d, hd, hdu, hda⟩ := V.owned rp hq
        exact hfr3 d hd hdu hda
    · rw [readN2_of_word m176]; exact e1592
    · show rdN μ3 (sp + 104) 8 = ptr
      rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega)]
      exact n104
    · show μ3.readN (sp + 512) 32 = μ.readN (sp + 312) 32
      rw [readN32_of_words p0 (by rw [show sp + 512 + 8 = sp + 520 by omega, show sp + 312 + 8 = sp + 320 by omega]; exact p1)
        (by rw [show sp + 512 + 16 = sp + 528 by omega, show sp + 312 + 16 = sp + 328 by omega]; exact p2)
        (by rw [show sp + 512 + 24 = sp + 536 by omega, show sp + 312 + 24 = sp + 336 by omega]; exact p3)]
      exact Memory.readN_congr fun j hj => st2 _ (by omega) (by omega) (by omega) (by omega) (by omega)
    · intro a h0 ha h104 h128 h176 h240 h448 h512 h1144 h1568
      rw [fr3 a h0 ha h128 h176 h240 h448 h512, st2 a h0 ha h104 h1144 h1568]
    · intro a ha; rw [gl3 a ha, gl2' a ha]
    · intro a ha; rw [(lo3 a ha).1, (lo3 a ha).2]; exact lo2' a ha
  have hcp64 : cp < 18446744073709551616 := by rw [← m288]; exact rdN_lt64 _ _
  by_cases hn : is = []
  · ---------------- no instructions: 7080 → 8013
    subst hn
    obtain ⟨ω3, μ3, r3, h31, h36, n240, n128, n176, n248, n448, n456, n464, p0, p1, p2, p3, fr3, rd3, wr3⟩ :=
      od_ok0 (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω2 μ2 sp c g1 g5 ⟨by omega, by omega⟩
        e1568 hc (by rw [e1584]; rfl) hrf2 hwf2
    have lo3 : ∀ a, a < sp → μ3.read a = μ2.read a := fun a ha =>
      fr3 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
    have H3 : HeapCtxC env.code pb S0 S1 μ3 st₂ := HeapCtxC.keep_hi H2 (fun a ha => lo3 a (by omega)) wr3
    exact .inr (fin 8 st₂ ω3 μ3 _ r3 H3
      (fun d hd hu => ⟨hd, fun a ha => lo3 a (by have := heapC_data_lt H2 hd ha; omega)⟩) h31
      (by rw [h36, e1576]) n240 (by rw [n128, g6, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hcp64]) n176 n248 n456
      n464 p0 p1 p2 p3 (fun a h0 _ h1 h2 h3 h4 h5 => fr3 a h0 h1 h2 h3 h4 h5)
      (fun a ha => lo3 a (by unfold Glob at ha; omega))
      (fun a ha => ⟨lo3 a (by omega), by rw [rd3]⟩) (.inl ⟨rfl, n448, rfl⟩))
  ---------------- n ≠ 0 instructions: the results' `with_capacity(n)`
  have hn2 : 232 * is.length < 2147483648 := by
    obtain ⟨-, d, hd, hdu, hda, hde⟩ := V.slots hn
    have := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hd hdu
    have := H2.hbT
    omega
  have hn0 : is.length ≠ 0 := fun h => hn (List.eq_nil_of_length_eq_zero h)
  obtain ⟨ω3, μ3, r3, h30, h31, h37, h38, h36, n240, n128, n176, n248, fr3, rd3, wr3⟩ :=
    od_okn (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω2 μ2 sp c is.length g1 g5
      ⟨by omega, by omega⟩ e1568 hc e1584 hn0 (by omega) hrf2 hwf2
  have lo3 : ∀ a, a < sp → μ3.read a = μ2.read a := fun a ha =>
    fr3 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  have H3 : HeapCtxC env.code pb S0 S1 μ3 st₂ := HeapCtxC.keep_hi H2 (fun a ha => lo3 a (by omega)) wr3
  rcases alloc_callG (p := p) (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap cx ω3 μ3 st₂ sp
      (144 * is.length) 8 pb S0 S1 H3 h31 h37 h38 (by decide) (by decide) (by omega) (by omega)
      ⟨by omega, by omega⟩ with
    ⟨rp, st₃, ω4, μ4, -, run4, H4, keep4, hnew, hfresh, hkg, e7, stk4, f0, f1, f5, f6⟩ |
    ⟨-, ω4, μ4, run4, e7, stk4, f0, f1, f5, f6⟩
  rotate_left
  · -- the allocation failed: 7145 → 15364
    obtain ⟨-, run4S⟩ := FreeStepsH.growS f run4
    obtain ⟨ω5, r5⟩ := od_null (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω4 μ4 e7
    have run := (run2.trans r3).trans ((run4S.trans (od_j240 (p := p) (P := P) _ ω4 μ4 (f0.trans h30))).trans r5)
    exact .inl ⟨⟨15364, ω5, μ4, cx, f⟩, ⟨_, run⟩, hAb2 _ rfl,
      ⟨ω5, μ4, f, trap_run 15364 ⟨(d_15364 (p := p) (P := P)).1, (d_15364 (p := p) (P := P)).2.1⟩ _ ω5 μ4⟩⟩
  obtain ⟨-, run4S⟩ := FreeStepsH.growS f run4
  have kro := HeapHost.keepRO (env := accHeapHost env) H3.bd run4
  obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H4.wf hnew rfl
  dsimp only at Nb1 Nb2 Nb3
  have hb0 := H4.hb0
  have hbT := H4.hbT
  have hrp0 : rp ≠ 0 := by omega
  have hwf4 : ∀ a, sp ≤ a → a < sp + 1856 → μ4.writable a = true := fun a h1 h2 => H4.st a (by omega) (by omega)
  have hrf4 : ∀ a, sp ≤ a → a < sp + 1856 → μ4.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf4 a h1 h2)
  have s248 : rdN μ4 (sp + 248) 8 = is.length := by
    rw [rdN_frame fun j hj => stk4 _ (by omega) (by omega)]; exact n248
  obtain ⟨ω5, μ5, r5, k1, k6, q448, q456, q464, p0, p1, p2, p3, fr5, rd5, wr5⟩ :=
    od_alloc (p := p) (P := P) (R := KeepCtx (accContractS env)) (cx, f) ω4 μ4 sp rp is.length (f1.trans h31) e7
      hrp0 (by omega) ⟨by omega, by omega⟩ s248 hrf4 hwf4
  have lo5 : ∀ a, a < sp → μ5.read a = μ4.read a := fun a ha => fr5 a (by omega) (.inl (by omega)) (.inl (by omega))
  have H5 : HeapCtxC env.code pb S0 S1 μ5 st₃ := HeapCtxC.keep_hi H4 (fun a ha => lo5 a (by omega)) wr5
  have s5 : ∀ k, sp ≤ k → k + 8 ≤ sp + 1856 → (k + 8 ≤ sp + 448 ∨ sp + 472 ≤ k) → (k + 8 ≤ sp + 512 ∨ sp + 544 ≤ k) →
      rdN μ5 k 8 = rdN μ3 k 8 := fun k h0 h1 h2 h3 => by
    rw [rdN_frame fun j hj => fr5 _ (by omega) (by omega) (by omega), rdN_frame fun j hj => stk4 _ (by omega) (by omega)]
  have s3 : ∀ k, sp ≤ k → k + 8 ≤ sp + 128 ∨ (sp + 256 ≤ k ∧ k + 8 ≤ sp + 448) → rdN μ3 k 8 = rdN μ2 k 8 := fun k h0 h1 =>
    rdN_frame fun j hj => fr3 _ (by omega) (by omega) (by omega) (by omega)
  have run := (r3.trans (run4S.trans (od_j240 (p := p) (P := P) _ ω4 μ4 (f0.trans h30)))).trans r5
  refine .inr (fin rp st₃ ω5 μ5 _ run H5 (fun d hd hu => ⟨keep4 d hd hu, fun a ha => ?_⟩) k1
    (by rw [k6, f6, h36, e1576]) (by rw [s5 _ (by omega) (by omega) (by omega) (by omega)]; exact n240)
    (by rw [s5 _ (by omega) (by omega) (by omega) (by omega), n128, g6, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt hcp64])
    (by rw [s5 _ (by omega) (by omega) (by omega) (by omega)]; exact n176)
    (by rw [s5 _ (by omega) (by omega) (by omega) (by omega)]; exact n248) q456 q464
    (by rw [p0, rdN_frame fun j hj => stk4 _ (by omega) (by omega), s3 _ (by omega) (by omega)])
    (by rw [p1, rdN_frame fun j hj => stk4 _ (by omega) (by omega), s3 _ (by omega) (by omega)])
    (by rw [p2, rdN_frame fun j hj => stk4 _ (by omega) (by omega), s3 _ (by omega) (by omega)])
    (by rw [p3, rdN_frame fun j hj => stk4 _ (by omega) (by omega), s3 _ (by omega) (by omega)])
    (fun a h0 ha h1 h2 h3 h4 h5 => by rw [fr5 a h0 h4 h5, stk4 a h0 ha, fr3 a h0 h1 h2 h3]) (fun a ha => ?_)
    (fun a ha => ⟨?_, ?_⟩) (.inr ⟨hn, q448, hnew, fun d hd hu e => ?_⟩))
  · have hd4 := keep4 d hd hu
    rw [lo5 a (by have := heapC_data_lt H4 hd4 ha; omega), HKeepG.data H4.wf H4.hb0 H4.hbT hkg hd4 ha,
      lo3 a (by have := heapC_data_lt H3 hd ha; omega)]
  · have hg := ha; unfold Glob at hg
    rw [lo5 a (by omega), glob_of_hkeepC H4.wf H4.hb0 hkg a ha, lo3 a (by omega)]
  · rw [lo5 a (by omega), kro.2 a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (H3.ro a ha),
      lo3 a (by omega)]
  · have hp := kro.1 (a / pageSize) (.inl (by unfold pageSize; omega))
    rw [rd5]; unfold Memory.readable; rw [hp]; rw [← Memory.readable, rd3]; rfl
  · have ht := H4.wf.2.2.2.1
    unfold TilesOk at ht
    have hd4 := keep4 d hd hu
    have := Tiles.addr_inj ht d hd4 _ hnew (by dsimp only; omega)
    exact hfresh d hd hu this

end Services.Bootstrap.Acc
