import Services.Bootstrap.Reader
import Services.Bootstrap.MemcpyBig

/-!
# Bootstrap's argument reader for reads of 16 octets or more

As `Services.Bootstrap.Reader`, for n ≥ 16: the copy is `memcpy_big`, which uses ω₂, ω₃, ω₄ and
ω₁₂ as scratch, so `ReadOkBig` keeps the rest of `ReadOk`.
-/

namespace Services.Bootstrap

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 8000000

variable {X : Type} {R : HostRel X}

/-- `ReadOk` without ω₂, ω₃, ω₄, ω₁₂ (the large copy's scratch registers). -/
def ReadOkBig (ω ω' : Regs) (μ μ' : Memory) (sp rd buf ptr len n : Nat) : Prop :=
  ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
    μ'.readN rd 8 = Num.encodeLE 8 (ptr + n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - n) ∧
    μ'.readN buf n = μ.readN ptr n ∧
    (∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < buf ∨ buf + n ≤ a) →
      μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **Reading n ≥ 16 octets** (58434): as `read_ok`, through `memcpy_big`. The buffer need only be
    disjoint from the two stack frames [sp − 88, sp) (the reader's 40 octets and `memcpy_big`'s 48 below
    them), so buf = sp is covered, as in the decoders of 32-octet hash fields. The source must lie at or
    above sp, or end 16 octets below the frames, and be 24 octets from the buffer: `memcpy_big`'s own
    margins (`hfs`, `hdj`). -/
theorem read_big_sp {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + n + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + n + 16 < 4294967296)
    (hn : 16 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrf : rd + 16 ≤ sp - 88 ∨ sp ≤ rd) (hbf : buf + n ≤ sp - 88 ∨ sp ≤ buf)
    (hpf : ptr + n + 16 ≤ sp - 88 ∨ sp ≤ ptr) (hbr : buf + n ≤ rd ∨ rd + 16 ≤ buf)
    (hbp : buf + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ buf)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (2 * n + 400) ∧ ReadOkBig ω ω' μ μ' sp rd buf ptr len n := by
  have hrf' : ∀ a, sp - 88 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrr : ∀ a, rd ≤ a → a < rd + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 68729) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 15) (n₂ := 2 * n + 360) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_58434 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_58437 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58440 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58443 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58446 (p := p) (P := P))
    · pvm_simp [h9]
    apply FreeStepsH.step_decode (d_58448 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR8]
    apply FreeStepsH.step_decode (d_58451 (p := p) (P := P))
    · pvm_simp [h9]
    apply FreeStepsH.step_decode (d_58454 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58455 (p := p) (P := P))
    · pvm_simp [h7, hrr, hR0]
    apply FreeStepsH.step_decode (d_58457 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_58459 (p := p) (P := P))
    · pvm_simp [h1, h7, hwf]
    apply FreeStepsH.step_decode (d_58462 (p := p) (P := P))
    · pvm_simp [h8]
    apply FreeStepsH.step_decode (d_58464 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58466 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_58468 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    generalize hM1 : ((((μ.writeN (sp - 40 + 32) (Num.encodeLE 8 ω[0].toNat)).writeN (sp - 40 + 24)
        (Num.encodeLE 8 ω[5].toNat)).writeN (sp - 40 + 16) (Num.encodeLE 8 ω[6].toNat)).writeN
        (sp - 40) (Num.encodeLE 8 ptr)).writeN (sp - 40 + 8) (Num.encodeLE 8 rd) = M1
    have m1 : ∀ a, a < 4294967296 → (a < sp - 40 ∨ sp ≤ a) → M1.read a = μ.read a := fun a ha0 ha1 => by
      rw [← hM1]; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE, PVM.two32]
    have m1r : ∀ a, M1.readable a = μ.readable a := fun a => by rw [← hM1]; simp only [Memory.readable_writeN]
    have m1w : ∀ a, M1.writable a = μ.writable a := fun a => by rw [← hM1]; simp only [Memory.writable_writeN]
    have fr1 : ∀ o v, (o = 0 ∧ v = ptr) ∨ (o = 8 ∧ v = rd) ∨ (o = 16 ∧ v = ω[6].toNat) ∨
        (o = 24 ∧ v = ω[5].toNat) ∨ (o = 32 ∧ v = ω[0].toNat) → M1.readN (sp - 40 + o) 8 = Num.encodeLE 8 v := by
      intro o v ho
      rw [← hM1]
      rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
        PVM.Num.length_encodeLE, PVM.two32, Nat.add_zero]
    refine FreeStepsH.bind_ex2 (memcpy_big (p := p) (P := P) (R := R) x _ M1 2550 58474 (sp - 40) buf ptr n
      (by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'])
      (by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'])
      (by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'])
      (by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'])
      (by simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'])
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1274]) bs_58474 (by omega) hn
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [m1r]; exact hra a h1 h2) (fun a h1 h2 => by rw [m1w]; exact hwb a h1 h2)
      (fun a h1 h2 => by rw [m1w]; exact hwf a (by omega) (by omega))) ?k (by omega)
      (n₁ := 2 * n + 320) (n₂ := 20)
    intro ω₂ μ₂ ⟨g0, g1, g5, g6, gcopy, gfr, grd, gwr⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some'] at g5 g6
    have m2 : ∀ a, a < 4294967296 → (a < buf ∨ buf + n ≤ a) → (a < sp - 40 - 48 ∨ sp - 40 ≤ a) →
        μ₂.read a = M1.read a := gfr
    have fr2 : ∀ o v, (o = 0 ∧ v = ptr) ∨ (o = 8 ∧ v = rd) ∨ (o = 16 ∧ v = ω[6].toNat) ∨
        (o = 24 ∧ v = ω[5].toNat) ∨ (o = 32 ∧ v = ω[0].toNat) → μ₂.readN (sp - 40 + o) 8 = Num.encodeLE 8 v := by
      intro o v ho
      rw [← fr1 o v ho]
      have : o ≤ 32 := by omega
      exact Memory.readN_congr (fun j hj => m2 _ (by omega) (by omega) (by omega))
    have q0 := fr2 0 _ (Or.inl ⟨rfl, rfl⟩)
    have q8 := fr2 8 _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have q16 := fr2 16 _ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    have q24 := fr2 24 _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    have q32 := fr2 32 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    rw [Nat.add_zero] at q0
    have hrd2 : ∀ a, sp - 40 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
      rw [grd, m1r]; exact hrf' a (by omega) h2
    have hwr2 : ∀ a, rd ≤ a → a < rd + 16 → μ₂.writable a = true := fun a h1 h2 => by
      rw [gwr, m1w]; exact hwr a h1 h2
    rw [show ω₂ = regsNF ω₂ [] from rfl]
    refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
    case run₂ =>
      pvm_go [g1, g5, g6, q0, q8, q16, q24, q32, hrd2, hwr2, h0, hret, hjt, hbt]
    case post₂ =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, UInt64.ofNat_toNat,
        PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint,
        PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, PVM.two32]
      · rw [gcopy]; exact Memory.readN_congr (fun j hj => m1 _ (by omega) (by omega))
      · rw [m2 a ha0 ha3 (by omega), m1 a ha0 (by omega)]
      · rw [grd, m1r]
      · rw [gwr, m1w]
  case hle => omega

/-- **Reading n ≥ 16 octets** (58434): `read_big_sp` with the buffer and the source kept 24 octets apart
    from each other and from the stack frames. -/
theorem read_big {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd buf ptr len n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat buf) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 88 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hbuf : 65536 ≤ buf ∧ buf + n + 24 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + n + 24 < 4294967296)
    (hn : 16 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrf : rd + 16 ≤ sp - 88 ∨ sp ≤ rd) (hbf : buf + n + 24 ≤ sp - 88 ∨ sp + 8 ≤ buf)
    (hpf : ptr + n + 24 ≤ sp - 88 ∨ sp + 8 ≤ ptr) (hbr : buf + n ≤ rd ∨ rd + 16 ≤ buf)
    (hbp : buf + n + 24 ≤ ptr ∨ ptr + n + 24 ≤ buf)
    (hwf : ∀ a, sp - 88 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwb : ∀ a, buf ≤ a → a < buf + n → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + n → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (2 * n + 400) ∧ ReadOkBig ω ω' μ μ' sp rd buf ptr len n :=
  read_big_sp x ω μ ret t sp rd buf ptr len n h0 h1 h7 h8 h9 hret hjt hbt hsp hrd ⟨hbuf.1, by omega⟩
    ⟨hptr.1, by omega⟩ hn hnl hlen hrf (by omega) (by omega) hbr hbp hwf hwr hwb hra hR0 hR8

end Services.Bootstrap
