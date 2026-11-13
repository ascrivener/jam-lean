import Services.Bootstrap.MemcpyBig

/-!
# Two `memcpy` cases of the key reader with tighter margins

`memcpy_big` keeps source and destination 24 octets apart and the source 8 octets above the caller's
stack pointer. The `[u8; 336]` key reader (GP v0.8.0 §B.7, validator keys) copies a key from S + 65 to
S + 408 (7 octets apart, source misaligned by 1) and from its own frame's base (the source at the stack
pointer) to S + 65 (destination misaligned by 1). `memcpy_s1` and `memcpy_d1` cover these two cases,
through the same steps (`memcpy_shift_loop`, `memcpy_mis_head_1`, `memcpy_mis_end_1`, `memcpy_mid_7`).
-/

namespace Services.Bootstrap.Decode.Key336Memcpy

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- **The misaligned path of `memcpy`, m = 1, source below destination** (68872 … 69129): as
    `memcpy_mis_1` for W ≥ 16, with the source's aligned words A0 … A0 + W + 8 only ending at or below
    the destination. -/
theorem mis1t {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W n' sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 1)) (h2 : ω[2] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d)
    (h12 : ω[12] = UInt64.ofNat W) (h1 : ω[1] = UInt64.ofNat sp)
    (hW : 16 ≤ W ∧ W % 8 = 0) (hA0 : A0 % 8 = 0) (hsp : sp % 8 = 0) (hn' : n' < 4294967296)
    (hb : A0 + W + 16 < 4294967296) (hd : d + W + 16 < 4294967296) (hs : sp + 24 < 4294967296)
    (hdA : A0 + W + 8 ≤ d) (hsA : sp + 24 ≤ A0 ∨ A0 + W + 16 ≤ sp)
    (hsd : sp + 24 ≤ d ∨ d + W ≤ sp)
    (hr : ∀ a, A0 + 1 ≤ a → a < A0 + 1 + W → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, d ≤ a → a < d + W → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68872 ω μ x 69132 ω' μ' x (2 * W + 100) ∧
      MisOk ω ω' μ μ' (A0 + 1) d W n' sp := by
  obtain ⟨k, hk⟩ : ∃ k, W = 8 * (k + 2) := ⟨W / 8 - 2, by omega⟩
  subst hk
  obtain ⟨ω₁, μ₁, pw, run₁, e4, elt, edrop, e6, e3, e11, e10, e1, e0, e2, e12, efr, eT, emf, erd, ewr⟩ :=
    memcpy_mis_head_1 (p := p) (P := P) (R := R) ω μ x A0 d (8 * (k + 2)) sp h0 h2 h10 h11 h12 h1 hW.1 hsp
      (by omega) (by omega) (by omega) (by omega) (fun a h1 h2 => hr a h1 (by omega)) hrs
  have m1 : ∀ a n, a + n < 4294967296 → (a + n ≤ sp ∨ sp + 24 ≤ a) → μ₁.readN a n = μ.readN a n :=
    fun a n h1 h2 => Memory.readN_congr (fun j hj => emf (a + j) (by omega) (by omega))
  obtain ⟨ω₂, μ₂, run₂, s1, ⟨pw₂, f4, flt, fdrop⟩, f6, f3, f11, f1, f10, ffr, fmf, frd, fwr⟩ :=
    memcpy_shift_loop (p := p) (P := P) (R := R) x 1 sp (by decide) k (regsNF ω₁ []) μ₁ pw A0 d e4 elt
      (by rw [edrop, m1 _ _ (by omega) (by omega)]) e6 e3 e11 e10 e1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) eT
      (fun a h1 h2 => by rw [erd]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [ewr]; exact hrs a (by omega) (by omega))
      (fun a h1 h2 => by rw [ewr]; exact hw a h1 (by omega))
  have m2 : ∀ a n, a + n < 4294967296 → (a + n ≤ d ∨ d + 8 * (k + 1) ≤ a) → (a + n ≤ sp + 8 ∨ sp + 16 ≤ a) →
      μ₂.readN a n = μ₁.readN a n :=
    fun a n h1 h2 h3 => Memory.readN_congr (fun j hj => fmf (a + j) (by omega) (by omega) (by omega))
  obtain ⟨ω₃, μ₃, run₃, w3, r8, r9, r10, r11, r1', fr3, mf3, rd3, wr3⟩ :=
    memcpy_mis_end_1 (p := p) (P := P) (R := R) (regsNF ω₂ []) μ₂ x pw₂ (A0 + 8 * (k + 1)) (d + 8 * (k + 1))
      (A0 + 1) (8 * (k + 2)) n' sp f4 flt
      (by rw [fdrop, m2 _ _ (by omega) (by omega) (by omega)])
      f6 f3 f11 ((ffr 0 (by decide)).trans e0) ((ffr 2 (by decide)).trans e2) ((ffr 12 (by decide)).trans e12)
      ((ffr 9 (by decide)).trans ((efr 9 (by decide)).trans h9)) (f10.trans e10) f1
      (by omega) (by omega) hsp (by omega) (by omega) (by omega) hn' (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [frd, erd]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr, ewr]; exact hrs a h1 h2)
      (fun a h1 h2 => by rw [fwr, ewr]; exact hw a (by omega) (by omega))
  have m3 : ∀ a n, a + n < 4294967296 → (a + n ≤ d + 8 * (k + 1) ∨ d + 8 * (k + 1) + 8 ≤ a) →
      (a + n ≤ sp + 16 ∨ sp + 24 ≤ a) → μ₃.readN a n = μ₂.readN a n :=
    fun a n h1 h2 h3 => Memory.readN_congr (fun j hj => mf3 (a + j) (by omega) (by omega) (by omega))
  refine ⟨ω₃, μ₃, ((run₁.trans run₂).trans run₃).mono (by omega), ?_, by rw [r8], r9, by rw [r10, show d + 8 * (k + 1) + 8 = d + 8 * (k + 2) by omega],
    by rw [r11, show d + 8 * (k + 1) + 8 = d + 8 * (k + 2) by omega], r1',
    (fr3 7 (by decide)).trans ((ffr 7 (by decide)).trans (efr 7 (by decide))),
    (fr3 12 (by decide)).trans ((ffr 12 (by decide)).trans (efr 12 (by decide))),
    fun a ha0 ha1 ha2 => (mf3 a ha0 (by omega) (by omega)).trans ((fmf a ha0 (by omega) (by omega)).trans
      (emf a ha0 ha2)),
    fun a => by rw [rd3, frd, erd], fun a => by rw [wr3, fwr, ewr]⟩
  have sp1 := Memory.readN_split μ₃ d (8 * (k + 1)) 8
  have sp2 := Memory.readN_split μ (A0 + 1) (8 * (k + 1)) 8
  rw [show 8 * (k + 1) + 8 = 8 * (k + 2) by omega] at sp1 sp2
  rw [sp1, sp2, m3 _ _ (by omega) (by omega) (by omega), s1, m1 _ _ (by omega) (by omega), w3,
    m2 _ _ (by omega) (by omega) (by omega), m1 _ _ (by omega) (by omega),
    show A0 + 8 * (k + 1) + 1 = A0 + 1 + 8 * (k + 1) by omega]

/-- **`memcpy`'s body, source misaligned by m = 1, below the destination**: as `memcpy_mid_1`, for n' ≥ 16 a
    multiple of 8 and the source ending at least 7 octets below the destination. -/
theorem mid1t {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (s d n' h : Nat) (h2 : ω[2] = UInt64.ofNat h) (h8 : ω[8] = UInt64.ofNat (s - h)) (h9 : ω[9] = UInt64.ofNat (n' + h))
    (h11 : ω[11] = UInt64.ofNat d) (hh : h ≤ s) (hn : 16 ≤ n') (hm : s % 8 = 1) (sp : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp % 8 = 0) (hs : sp + 24 < 4294967296)
    (hb : s + n' + 16 < 4294967296) (hd : d + n' + 16 < 4294967296)
    (hdj : s + n' + 7 ≤ d) (hn8 : n' % 8 = 0) (hsd : sp + 24 ≤ d ∨ d + n' ≤ sp)
    (hss : sp + 24 + 8 ≤ s ∨ s + n' + 16 ≤ sp)
    (hr : ∀ a, s ≤ a → a < s + n' → μ.readable a = true) (hw : ∀ a, d ≤ a → a < d + n' → μ.writable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68780 ω μ x 68857 ω' μ' x (2 * n' + 220) ∧ MidOk ω ω' μ μ' s d n' sp := by
  have hand7 : ∀ a, Exec.bitwise (fun x1 x2 => x1 && x2) a 7 = a % 8 := fun a => by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  obtain ⟨k, hk⟩ : ∃ k, n' / 8 * 8 = 8 * (k + 1) := ⟨n' / 8 - 1, by omega⟩
  rw [show ω = regsNF ω [] from rfl]
  have stA : ∃ ω₁, FreeStepsH p R 68780 (regsNF ω []) μ x 68872 ω₁ μ x 6 ∧
      ω₁[0] = UInt64.ofNat (s - 1 + 1) ∧ ω₁[2] = UInt64.ofNat 1 ∧ ω₁[9] = UInt64.ofNat n' ∧
      ω₁[10] = UInt64.ofNat (d + 8 * (k + 1)) ∧ ω₁[11] = UInt64.ofNat d ∧ ω₁[12] = UInt64.ofNat (8 * (k + 1)) ∧
      ω₁[1] = UInt64.ofNat sp := by
    refine ⟨?ω₁, ?run, ?post⟩
    case run => pvm_go [h2, h8, h9, h11, hand7, bitwise_and_not7, hk, hm, show s - h + h = s by omega]
    case post =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none, h1, h2, h8, h9, h11, hk, hm, show s - h + h = s by omega,
        show s - 1 + 1 = s by omega, Nat.add_sub_cancel]
  obtain ⟨ω₁, run₁, a0, a2, a9, a10, a11, a12, a1⟩ := stA
  obtain ⟨ω₂, μ₂, run₂, w2, r8, r9, r10, r11, r1', r7, r12, mf, rd, wr⟩ :=
    mis1t (p := p) (P := P) (R := R) ω₁ μ x (s - 1) d (8 * (k + 1)) n' sp a0 a2 a9 a10 a11 a12 a1
      (by omega) (by omega) hsp (by omega) (by omega) (by omega) hs (by omega) (by omega) (by omega)
      (fun a h1 h2 => hr a (by omega) (by omega)) hrs (fun a h1 h2 => hw a h1 (by omega))
  rw [show s - 1 + 1 = s by omega] at w2 r8
  rcases Nat.eq_zero_or_pos (n' % 8) with ht | ht
  · obtain ⟨ω₃, run₃, c1⟩ : ∃ ω₃, FreeStepsH p R 69132 (regsNF ω₂ []) μ₂ x 68857 ω₃ μ₂ x 2 ∧ ω₃[1] = ω₂[1] := by
      generalize μ₂ = M
      refine ⟨?ω₃a, ?run, ?post⟩
      case run => pvm_go [r9, r10, r11, ht]
      case post => simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
          PVM.getD_some', List.lookup_nil, Option.getD_none]
    refine ⟨ω₃, μ₂, (run₁.trans (run₂.trans run₃)).mono (by omega), ?_, c1.trans (r1'.trans h1.symm),
      fun a ha0 ha1 ha2 => mf a ha0 (by omega) ha2, rd, wr⟩
    rw [show n' = 8 * (k + 1) by omega, w2]
  · omega

/-- **`memcpy` of n ≥ 16 octets, destination aligned, source misaligned by 1 and below it** (68729): as
    `memcpy_big`, with the source only 7 octets below the destination. -/
theorem memcpy_s1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp dst src n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat dst) (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hn : 16 ≤ n)
    (hs : src + n + 16 < 4294967296) (hd : dst + n + 16 < 4294967296)
    (hda : dst % 8 = 0) (hsa : src % 8 = 1) (hn8 : n % 8 = 0)
    (hdj : src + n + 7 ≤ dst) (hfd : sp ≤ dst ∨ dst + n ≤ sp - 48)
    (hfs : sp + 8 ≤ src ∨ src + n + 16 ≤ sp - 48)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68729 ω μ x t ω' μ' x (2 * n + 320) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN dst n = μ.readN src n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω₁, run₁, e2, e7, e8, e9, e11, e1, efr⟩ := memcpy_entry (p := p) (P := P) (R := R) ω μ x sp dst src n
    h1 h7 h8 h9 hn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega)) hwf
  generalize hd8def : (8 - dst % 8) % 8 = hd8 at e2 e11 run₁
  have hd87 : hd8 ≤ 7 := by omega
  -- the memory after the entry
  generalize hM1 : (memcpyFrame μ ω sp).writeN dst ((memcpyFrame μ ω sp).readN src hd8) = M1 at run₁
  have mF : ∀ a, a < 4294967296 → (a < sp - 48 + 24 ∨ sp ≤ a) → (memcpyFrame μ ω sp).read a = μ.read a :=
    fun a ha0 ha1 => by
      simp (disch := pvm_arith) only [memcpyFrame, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
        PVM.two32]
  have m1 : ∀ a, a < 4294967296 → (a < dst ∨ dst + hd8 ≤ a) → (a < sp - 48 + 24 ∨ sp ≤ a) → M1.read a = μ.read a :=
    fun a ha0 ha1 ha2 => by
      rw [← hM1, Memory.read_writeN_disjoint _ _ _ _ (by simp [Memory.length_readN]; omega)
        (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega), mF a ha0 ha2]
  have m1r : ∀ a, M1.readable a = μ.readable a := fun a => by
    rw [← hM1]; simp only [memcpyFrame, Memory.readable_writeN]
  have m1w : ∀ a, M1.writable a = μ.writable a := fun a => by
    rw [← hM1]; simp only [memcpyFrame, Memory.writable_writeN]
  have hrM : ∀ a, src + hd8 ≤ a → a < src + hd8 + (n - hd8) → M1.readable a = true :=
    fun a h1 h2 => by rw [m1r]; exact hr a (by omega) (by omega)
  have hwM : ∀ a, dst + hd8 ≤ a → a < dst + hd8 + (n - hd8) → M1.writable a = true :=
    fun a h1 h2 => by rw [m1w]; exact hw a (by omega) (by omega)
  have hrsM : ∀ a, sp - 48 ≤ a → a < sp - 48 + 24 → M1.writable a = true :=
    fun a h1 h2 => by rw [m1w]; exact hwf a h1 (by omega)
  have hmid : ∃ ω₂ μ₂, FreeStepsH p R 68780 (regsNF ω₁ []) M1 x 68857 ω₂ μ₂ x (2 * (n - hd8) + 220) ∧
      MidOk (regsNF ω₁ []) ω₂ M1 μ₂ (src + hd8) (dst + hd8) (n - hd8) (sp - 48) := by
    have hm : (src + hd8) % 8 = 1 := by omega
    exact mid1t (p := p) (P := P) (R := R) (regsNF ω₁ []) _ x (src + hd8) (dst + hd8) (n - hd8) hd8 e2
      (e8.trans (by congr 1; omega)) (e9.trans (by congr 1; omega)) e11 (by omega) (by omega) hm (sp - 48) e1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hrM hwM hrsM
  obtain ⟨ω₂, μ₂, run₂, o1, o2, o3, o4, o5⟩ := hmid
  have m2 : ∀ a k, a + k < 4294967296 → (a + k ≤ dst + hd8 ∨ dst + hd8 + (n - hd8) ≤ a) →
      (a + k ≤ sp - 48 ∨ sp - 48 + 24 ≤ a) → μ₂.readN a k = M1.readN a k :=
    fun a k h1 h2 h3 => Memory.readN_congr (fun j hj => o3 (a + j) (by omega) (by omega) (by omega))
  have stk : ∀ o v, (o = 40 ∧ v = ω[0].toNat) ∨ (o = 32 ∧ v = ω[5].toNat) ∨ (o = 24 ∧ v = ω[6].toNat) →
      μ₂.readN (sp - 48 + o) 8 = Num.encodeLE 8 v := by
    intro o v ho
    rw [m2 _ _ (by omega) (by omega) (by omega), ← hM1, Memory.readN_writeN_disjoint _ _ _ _ _
      (by simp [Memory.length_readN]; omega) (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega)]
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := pvm_arith) only [memcpyFrame, PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
      PVM.Num.length_encodeLE, PVM.two32]
  have s0 := stk 40 _ (Or.inl ⟨rfl, rfl⟩)
  have s5 := stk 32 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have s6 := stk 24 _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have q1 : ω₂[1] = UInt64.ofNat (sp - 48) := o2.trans e1
  have hrs2 : ∀ a, sp - 48 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
    rw [o4, m1r]; exact Memory.readable_of_writable (hwf a h1 h2)
  have stE : ∃ ω₃, FreeStepsH p R 68857 (regsNF ω₂ []) μ₂ x t ω₃ μ₂ x 6 ∧
      ω₃[0] = UInt64.ofNat ret ∧ ω₃[1] = UInt64.ofNat sp ∧ ω₃[5] = ω[5] ∧ ω₃[6] = ω[6] := by
    generalize μ₂ = M at s0 s5 s6 hrs2 ⊢
    refine ⟨?ω₃, ?run, ?post⟩
    case run => pvm_go [q1, s0, s5, s6, hrs2, h0, hret, hjt, hbt]
    case post =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat,
        Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, q1, s0, s5, s6, h0,
        PVM.Num.decodeLE_encodeLE, PVM.u64_toNat_mod, UInt64.ofNat_toNat, UInt64.toNat_ofNat, Nat.mod_mod]
  obtain ⟨ω₃, run₃, c0, c1, c5, c6⟩ := stE
  refine ⟨ω₃, μ₂, ((run₁.trans run₂).trans run₃).mono (by omega), c0, c1, c5, c6, ?_,
    fun a ha0 ha1 ha2 => ?_, fun a => by rw [o4, m1r], fun a => by rw [o5, m1w]⟩
  · have sp1 := Memory.readN_split μ₂ dst hd8 (n - hd8)
    have sp2 := Memory.readN_split μ src hd8 (n - hd8)
    rw [show hd8 + (n - hd8) = n by omega] at sp1 sp2
    rw [sp1, sp2, o1, m2 _ _ (by omega) (by omega) (by omega)]
    congr 1
    · rw [← hM1, Memory.readN_writeN_same _ _ _ _ (Memory.length_readN _ _ _) (by simp [two32]; omega)]
      exact Memory.readN_congr (fun j hj => mF _ (by omega) (by omega))
    · exact Memory.readN_congr (fun j hj => m1 _ (by omega) (by omega) (by omega))
  · rw [o3 a ha0 (by omega) (by omega), m1 a ha0 (by omega) (by omega)]

/-- **`memcpy` of n ≥ 16 octets, destination misaligned by 1, source aligned** (68729): as `memcpy_big`,
    with the source allowed at the caller's stack pointer. -/
theorem memcpy_d1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp dst src n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat dst) (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hn : 16 ≤ n)
    (hs : src + n + 16 < 4294967296) (hd : dst + n + 16 < 4294967296)
    (hda : dst % 8 = 1) (hsa : src % 8 = 0)
    (hdj : dst + n + 24 ≤ src ∨ src + n + 24 ≤ dst) (hfd : sp ≤ dst ∨ dst + n ≤ sp - 48)
    (hfs : sp ≤ src)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68729 ω μ x t ω' μ' x (2 * n + 320) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN dst n = μ.readN src n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω₁, run₁, e2, e7, e8, e9, e11, e1, efr⟩ := memcpy_entry (p := p) (P := P) (R := R) ω μ x sp dst src n
    h1 h7 h8 h9 hn (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega)) hwf
  generalize hd8def : (8 - dst % 8) % 8 = hd8 at e2 e11 run₁
  have hd87 : hd8 ≤ 7 := by omega
  -- the memory after the entry
  generalize hM1 : (memcpyFrame μ ω sp).writeN dst ((memcpyFrame μ ω sp).readN src hd8) = M1 at run₁
  have mF : ∀ a, a < 4294967296 → (a < sp - 48 + 24 ∨ sp ≤ a) → (memcpyFrame μ ω sp).read a = μ.read a :=
    fun a ha0 ha1 => by
      simp (disch := pvm_arith) only [memcpyFrame, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
        PVM.two32]
  have m1 : ∀ a, a < 4294967296 → (a < dst ∨ dst + hd8 ≤ a) → (a < sp - 48 + 24 ∨ sp ≤ a) → M1.read a = μ.read a :=
    fun a ha0 ha1 ha2 => by
      rw [← hM1, Memory.read_writeN_disjoint _ _ _ _ (by simp [Memory.length_readN]; omega)
        (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega), mF a ha0 ha2]
  have m1r : ∀ a, M1.readable a = μ.readable a := fun a => by
    rw [← hM1]; simp only [memcpyFrame, Memory.readable_writeN]
  have m1w : ∀ a, M1.writable a = μ.writable a := fun a => by
    rw [← hM1]; simp only [memcpyFrame, Memory.writable_writeN]
  have hrM : ∀ a, src + hd8 ≤ a → a < src + hd8 + (n - hd8) → M1.readable a = true :=
    fun a h1 h2 => by rw [m1r]; exact hr a (by omega) (by omega)
  have hwM : ∀ a, dst + hd8 ≤ a → a < dst + hd8 + (n - hd8) → M1.writable a = true :=
    fun a h1 h2 => by rw [m1w]; exact hw a (by omega) (by omega)
  have hrsM : ∀ a, sp - 48 ≤ a → a < sp - 48 + 24 → M1.writable a = true :=
    fun a h1 h2 => by rw [m1w]; exact hwf a h1 (by omega)
  have hmid : ∃ ω₂ μ₂, FreeStepsH p R 68780 (regsNF ω₁ []) M1 x 68857 ω₂ μ₂ x (2 * (n - hd8) + 220) ∧
      MidOk (regsNF ω₁ []) ω₂ M1 μ₂ (src + hd8) (dst + hd8) (n - hd8) (sp - 48) := by
    have hm : (src + hd8) % 8 = 7 := by omega
    exact memcpy_mid_7 (p := p) (P := P) (R := R) (regsNF ω₁ []) _ x (src + hd8) (dst + hd8) (n - hd8) hd8 e2
      (e8.trans (by congr 1; omega)) (e9.trans (by congr 1; omega)) e11 (by omega) (by omega) hm (sp - 48) e1
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hrM hwM hrsM
  obtain ⟨ω₂, μ₂, run₂, o1, o2, o3, o4, o5⟩ := hmid
  have m2 : ∀ a k, a + k < 4294967296 → (a + k ≤ dst + hd8 ∨ dst + hd8 + (n - hd8) ≤ a) →
      (a + k ≤ sp - 48 ∨ sp - 48 + 24 ≤ a) → μ₂.readN a k = M1.readN a k :=
    fun a k h1 h2 h3 => Memory.readN_congr (fun j hj => o3 (a + j) (by omega) (by omega) (by omega))
  have stk : ∀ o v, (o = 40 ∧ v = ω[0].toNat) ∨ (o = 32 ∧ v = ω[5].toNat) ∨ (o = 24 ∧ v = ω[6].toNat) →
      μ₂.readN (sp - 48 + o) 8 = Num.encodeLE 8 v := by
    intro o v ho
    rw [m2 _ _ (by omega) (by omega) (by omega), ← hM1, Memory.readN_writeN_disjoint _ _ _ _ _
      (by simp [Memory.length_readN]; omega) (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega)]
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := pvm_arith) only [memcpyFrame, PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
      PVM.Num.length_encodeLE, PVM.two32]
  have s0 := stk 40 _ (Or.inl ⟨rfl, rfl⟩)
  have s5 := stk 32 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have s6 := stk 24 _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have q1 : ω₂[1] = UInt64.ofNat (sp - 48) := o2.trans e1
  have hrs2 : ∀ a, sp - 48 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
    rw [o4, m1r]; exact Memory.readable_of_writable (hwf a h1 h2)
  have stE : ∃ ω₃, FreeStepsH p R 68857 (regsNF ω₂ []) μ₂ x t ω₃ μ₂ x 6 ∧
      ω₃[0] = UInt64.ofNat ret ∧ ω₃[1] = UInt64.ofNat sp ∧ ω₃[5] = ω[5] ∧ ω₃[6] = ω[6] := by
    generalize μ₂ = M at s0 s5 s6 hrs2 ⊢
    refine ⟨?ω₃, ?run, ?post⟩
    case run => pvm_go [q1, s0, s5, s6, hrs2, h0, hret, hjt, hbt]
    case post =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat,
        Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, q1, s0, s5, s6, h0,
        PVM.Num.decodeLE_encodeLE, PVM.u64_toNat_mod, UInt64.ofNat_toNat, UInt64.toNat_ofNat, Nat.mod_mod]
  obtain ⟨ω₃, run₃, c0, c1, c5, c6⟩ := stE
  refine ⟨ω₃, μ₂, ((run₁.trans run₂).trans run₃).mono (by omega), c0, c1, c5, c6, ?_,
    fun a ha0 ha1 ha2 => ?_, fun a => by rw [o4, m1r], fun a => by rw [o5, m1w]⟩
  · have sp1 := Memory.readN_split μ₂ dst hd8 (n - hd8)
    have sp2 := Memory.readN_split μ src hd8 (n - hd8)
    rw [show hd8 + (n - hd8) = n by omega] at sp1 sp2
    rw [sp1, sp2, o1, m2 _ _ (by omega) (by omega) (by omega)]
    congr 1
    · rw [← hM1, Memory.readN_writeN_same _ _ _ _ (Memory.length_readN _ _ _) (by simp [two32]; omega)]
      exact Memory.readN_congr (fun j hj => mF _ (by omega) (by omega))
    · exact Memory.readN_congr (fun j hj => m1 _ (by omega) (by omega) (by omega))
  · rw [o3 a ha0 (by omega) (by omega), m1 a ha0 (by omega) (by omega)]

end Services.Bootstrap.Decode.Key336Memcpy
