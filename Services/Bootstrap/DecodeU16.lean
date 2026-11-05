import Services.Bootstrap.DecodeU32

/-!
# Bootstrap's `u16` decoder, summarized

The refine entry decodes the core index `c` with a `u16` copy of the decoder at 31894 inlined
into its body: 4642 sets the return address and 4646 … 4676 is the prologue, jumping to the reader
(58434), which returns to the decoder's body at 32166. The body is the `u32` one but for the range
check at the end: it sets ω₇ = [n ≥ 2^16] rather than branching to the error path. So the same
summaries hold, `decodeU16_zero`, `decodeU16_len1` … `decodeU16_len3`, and `decodeU16` for every
n < 2^16 (GP (C), general natural encoding).
-/

namespace Services.Bootstrap

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 8000000

variable {X : Type} {R : HostRel X}

/-- **Decoding ℰ(0)**, the single octet 0 (GP (C)): the prefix test exits at once. -/
theorem decodeU16_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 1 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 32 ≤ sp - 128 ∨ sp ≤ ptr) (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 1 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : n = 0)
    (hb : μ.read ptr = UInt8.ofNat (n)) :
    ∃ ω' μ', FreeStepsH p R 4646 ω μ x t ω' μ' x 500 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 1 := by
  have hrf' : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 11) (n₂ := 489) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_4646 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4649 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4652 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4655 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4658 (p := p) (P := P))
    · pvm_simp [h7]
    apply FreeStepsH.step_decode (d_4660 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4663 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4666 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4669 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4672 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4676 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1484 32166 (sp - 40) rd (sp - 32) ptr len 1
      ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) ?mjt ?mbt (by omega) (by omega) (by omega) (by omega) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mwr ?mwb ?mra ?mR0 ?mR8) ?k ?hle2
      (n₁ := 7 * 1 + 50) (n₂ := 432)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7]
      all_goals (congr 1; omega)
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_741]
    case mbt => exact bs_32166
    case mwf | mwr | mwb | mra =>
      intro a h1 h2
      simp only [Memory.writable_writeN, Memory.readable_writeN]
      first | exact hwf a (by omega) (by omega) | exact hwr a (by omega) (by omega) | exact hra a (by omega) (by omega)
    case mR0 | mR8 =>
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE, List.length_cons,
        List.length_nil, hR0, hR8]
    case k =>
      intro ω₂ μ₂ ⟨g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g2 g3 g4 g5 g6 g12
      -- the prefix octet, now in the buffer at sp − 32
      have hb2 : μ₂.read (sp - 32) = UInt8.ofNat (n) := by
        have := gbuf
        simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, Nat.add_zero, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          List.length_cons, List.length_nil, List.cons.injEq, and_true] at this
        rw [this, hb]
      have hbv : (μ₂.read (sp - 40 + 8)).toNat = n := by
        rw [show sp - 40 + 8 = sp - 32 by omega, hb2, UInt8.toNat_ofNat']; omega
      have hrd2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
        rw [grd]; exact hrf' a h1 h2
      have hwf2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.writable a = true := fun a h1 h2 => by
        rw [gwr]; exact hwf a h1 h2
      have e21 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 31 ≤ a) =>
        Memory.readN_congr (n := 8) (a := a) (fun j hj => gfr (a + j) (by omega) (by omega) (by omega) (by omega))
      have hr0 : μ₂.readN (sp - 40 + 32) 8 = Num.encodeLE 8 ω[0].toNat := by
        rw [e21 _ (by omega) (by omega) (by omega)]
        simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
          PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
      have hr5 : μ₂.readN (sp - 40 + 24) 8 = Num.encodeLE 8 ω[5].toNat := by
        rw [e21 _ (by omega) (by omega) (by omega)]
        simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
          PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
      have hr6 : μ₂.readN (sp - 40 + 16) 8 = Num.encodeLE 8 ω[6].toNat := by
        rw [e21 _ (by omega) (by omega) (by omega)]
        simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
          PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
      have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
      have hand : Exec.bitwise (fun x1 x2 => x1 && x2) (μ₂.read (sp - 40 + 8)).toNat 255 = 0 := by
        rw [bitwise_and_low _ 255 8 (by decide) (by decide)]; omega
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
      case run₂ =>
        apply FreeStepsH.step_decode (d_32166 (p := p) (P := P))
        · pvm_simp [g7]
        apply FreeStepsH.step_decode (d_32186 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32187 (p := p) (P := P))
        · pvm_simp [g1, hrd2, ↓loadI8_read_sx8]
        apply FreeStepsH.step_decode (d_32190 (p := p) (P := P))
        · pvm_simp [hand]
        apply FreeStepsH.step_decode (d_32194 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32230 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32231 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32233 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32235 (p := p) (P := P))
        · pvm_simp [g1, hrd2, hr0]
        apply FreeStepsH.step_decode (d_32238 (p := p) (P := P))
        · pvm_simp [g1, hrd2, hr5]
        apply FreeStepsH.step_decode (d_32241 (p := p) (P := P))
        · pvm_simp [g1, hrd2, hr6]
        apply FreeStepsH.step_decode (d_32244 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_32247 (p := p) (P := P))
        · pvm_simp [h0, hret, hjt, hbt]
        exact FreeStepsH.refl.mono (Nat.zero_le _)
      case post₂ =>
        subst hn
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_,
          fun a => ?_⟩
        all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
          PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, g2, g3, g4, g12]
        · exact gR0
        · exact gR8
        · rw [gfr a ha0 (by omega) ha2 (by omega)]
          simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
            List.length_cons, List.length_nil]
        · simp only [grd, Memory.readable_writeN]
        · simp only [gwr, Memory.writable_writeN]
    case hle2 => omega
  case hle => decide

/-- **Decoding a 1-octet ℰ(n)**, 1 ≤ n < 128 (GP (C), general natural encoding): the octet is n. -/
theorem decodeU16_len1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 1 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 32 ≤ sp - 128 ∨ sp ≤ ptr) (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 1 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 1 ≤ n ∧ n < 128)
    (hb : μ.read ptr = UInt8.ofNat (n)) :
    ∃ ω' μ', FreeStepsH p R 4646 ω μ x t ω' μ' x 500 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 1 := by
  have hrf' : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 11) (n₂ := 489) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_4646 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4649 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4652 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4655 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4658 (p := p) (P := P))
    · pvm_simp [h7]
    apply FreeStepsH.step_decode (d_4660 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4663 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4666 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4669 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4672 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4676 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1484 32166 (sp - 40) rd (sp - 32) ptr len 1
      ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) ?mjt ?mbt (by omega) (by omega) (by omega) (by omega) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mwr ?mwb ?mra ?mR0 ?mR8) ?k ?hle2
      (n₁ := 7 * 1 + 50) (n₂ := 432)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7]
      all_goals (congr 1; omega)
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_741]
    case mbt => exact bs_32166
    case mwf | mwr | mwb | mra =>
      intro a h1 h2
      simp only [Memory.writable_writeN, Memory.readable_writeN]
      first | exact hwf a (by omega) (by omega) | exact hwr a (by omega) (by omega) | exact hra a (by omega) (by omega)
    case mR0 | mR8 =>
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE, List.length_cons,
        List.length_nil, hR0, hR8]
    case k =>
      intro ω₂ μ₂ ⟨g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g2 g3 g4 g5 g6 g12
      -- the prefix octet, now in the buffer at sp − 32
      have hb2 : μ₂.read (sp - 32) = UInt8.ofNat (n) := by
        have := gbuf
        simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, Nat.add_zero, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          List.length_cons, List.length_nil, List.cons.injEq, and_true] at this
        rw [this, hb]
      have hbv : (μ₂.read (sp - 40 + 8)).toNat = n := by
        rw [show sp - 40 + 8 = sp - 32 by omega, hb2, UInt8.toNat_ofNat']; omega
      have hrd2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
        rw [grd]; exact hrf' a h1 h2
      have hwf2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.writable a = true := fun a h1 h2 => by
        rw [gwr]; exact hwf a h1 h2
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₃) (μ₁ := ?μ₃) (n₁ := 16) (n₂ := 416) ?pre2 ?rest2 ?hle3
      case pre2 =>
        apply FreeStepsH.step_decode (d_32166 (p := p) (P := P))
        · pvm_simp [g7]
        apply FreeStepsH.step_decode (d_32186 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32187 (p := p) (P := P))
        · pvm_simp [g1, hrd2, ↓loadI8_read_sx8]
        have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
        have hand : Exec.bitwise (fun x1 x2 => x1 && x2) (μ₂.read (sp - 40 + 8)).toNat 255 = n := by
          rw [bitwise_and_low _ 255 8 (by decide) (by decide)]; omega
        apply FreeStepsH.step_decode (d_32190 (p := p) (P := P))
        · pvm_simp [hand]
        apply FreeStepsH.step_decode (d_32194 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32197 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32201 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32249 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32251 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32254 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32256 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32334 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32337 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_32340 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_32342 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32344 (p := p) (P := P))
        · pvm_simp []
        exact FreeStepsH.refl
      case rest2 =>
        refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1488 32350 (sp - 40) rd (sp - 32)
          (ptr + 1) (len - 1) 0
          ?q0 ?q1 ?q7 ?q8 ?q9 (by decide) ?qjt ?qbt (by omega) (by omega) (by omega) (by omega) (by decide)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?qwf ?qwr ?qwb ?qra ?qR0 ?qR8)
          ?k2 ?hle4 (n₁ := 7 * 0 + 50) (n₂ := 100)
        case q0 | q1 | q7 | q8 | q9 =>
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none, g1, g7]
          all_goals (congr 1; omega)
        case qjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_743]
        case qbt => exact bs_32350
        case qwf | qwb =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwf a (by omega) (by omega)
        case qwr =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwr a (by omega) (by omega)
        case qra =>
          intro a h1 h2
          simp only [Memory.readable_writeN, grd]
          exact hra a (by omega) (by omega)
        case qR0 | qR8 =>
          simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
            List.length_cons, List.length_nil, gR0, gR8]
        case k2 =>
          intro ω₄ μ₄ ⟨f0, f1, f2, f3, f4, f5, f6, f12, f7, fR0, fR8, fbuf, ffr, frd, fwr⟩
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none] at f0 f1 f2 f3 f4 f5 f6 f12
          have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
          -- frame reads: μ₄ agrees with μ₃ on [sp − 40, sp) outside the buffer octet at sp − 32,
          -- and μ₂ with the pre-call memory
          have e43 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 32 + 1 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => ffr (a + j) (by omega) (by omega) (by omega) (by omega))
          have e21 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 31 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => gfr (a + j) (by omega) (by omega) (by omega) (by omega))
          have hr0 : μ₄.readN (sp - 40 + 32) 8 = Num.encodeLE 8 ω[0].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr5 : μ₄.readN (sp - 40 + 24) 8 = Num.encodeLE 8 ω[5].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr6 : μ₄.readN (sp - 40 + 16) 8 = Num.encodeLE 8 ω[6].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr9 : μ₄.readN (sp - 40) 8 = Num.encodeLE 8 (μ₂.read (sp - 40 + 8)).toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hbuf' : μ₄.readN (sp - 32) 0 = Num.encodeLE 0 0 := by simp [Memory.readN, Num.encodeLE]
          have hz : ∀ j, 0 ≤ j → j < 8 → μ₄.read (sp - 32 + j) = UInt8.ofNat 0 := by
            intro j hj1 hj2
            rw [ffr _ (by omega) (by omega) (by omega) (by omega), show sp - 32 + j = sp - 40 + 8 + j by omega,
              Memory.read_writeN_at _ _ _ (by simp [two32]) j (by simp; omega)]
            have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          have hz0 : μ₄.read (sp - 32) = UInt8.ofNat 0 := by simpa using hz 0 (by omega) (by omega)
          have hr8 : μ₄.readN (sp - 40 + 8) 8 = Num.encodeLE 8 (0) := by
            have s1 := Memory.readN_split μ₄ (sp - 32) 0 8
            have s2 := Num.encodeLE_split 0 8 (0)
            simp only [Nat.reduceAdd, Nat.reducePow] at s1 s2
            rw [show sp - 40 + 8 = sp - 32 by omega, s1, s2, hbuf', Nat.div_eq_of_lt (by omega)]
            congr 1
            simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
              List.map_cons, List.map_nil, List.map_append, List.cons_append, Nat.add_zero, Nat.add_assoc,
              Nat.reduceAdd, hz, hz0, Num.encodeLE, Nat.zero_div, Nat.zero_mod]
          have hrd4 : ∀ a, sp - 128 ≤ a → a < sp → μ₄.readable a = true := fun a h1 h2 => by
            rw [frd]; simp only [Memory.readable_writeN]; exact hrd2 a h1 h2
          have handInv : Exec.bitwise (fun x y => x && !y) (μ₂.read (sp - 40 + 8)).toNat
              18446744073709551488 = n := by
            rw [bitwise_andInv_high _ _ 7 (by decide) (by decide)]; omega
          rw [show ω₄ = regsNF ω₄ [] from rfl]
          refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
          case run₂ =>
            apply FreeStepsH.step_decode (d_32350 (p := p) (P := P))
            · pvm_simp [f7]
            apply FreeStepsH.step_decode (d_32370 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32373 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32376 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr8]
            apply FreeStepsH.step_decode (d_32379 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr9, hX]
            apply FreeStepsH.step_decode (d_32381 (p := p) (P := P))
            · pvm_simp [handInv]
            apply FreeStepsH.step_decode (d_32384 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32387 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32390 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32393 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32394 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32397 (p := p) (P := P))
            · pvm_simp [Nat.mod_add_div', hn]
            apply FreeStepsH.step_decode (d_32399 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr0]
            apply FreeStepsH.step_decode (d_32402 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr5]
            apply FreeStepsH.step_decode (d_32405 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr6]
            apply FreeStepsH.step_decode (d_32408 (p := p) (P := P))
            · pvm_simp [f1, g1]
            apply FreeStepsH.step_decode (d_32411 (p := p) (P := P))
            · pvm_simp [h0, hret, hjt, hbt]
            exact FreeStepsH.refl.mono (Nat.zero_le _)
          case post₂ =>
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_,
              fun a => ?_⟩
            all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
              PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, f2, f3, f4, f12, g2, g3, g4, g12]
            · rw [fR0, show ptr + 1 + 0 = ptr + 1 by omega]
            · rw [fR8, show len - 1 - 0 = len - 1 by omega]
            · rw [ffr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
              rw [gfr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
            · simp only [frd, grd, Memory.readable_writeN]
            · simp only [fwr, gwr, Memory.writable_writeN]
        case hle4 => omega
      case hle3 => omega
    case hle2 => omega
  case hle => decide

/-- **Decoding a 2-octet ℰ(n)**, 2^7 ≤ n < 2^14 (GP (C), general natural
    encoding): the prefix octet 2^8 − 2^7 + ⌊n / 2^8⌋, then ℰ_1(n mod 2^8). -/
theorem decodeU16_len2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 2 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 32 ≤ sp - 128 ∨ sp ≤ ptr) (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 2 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 128 ≤ n ∧ n < 16384)
    (hb : μ.read ptr = UInt8.ofNat (128 + n / 256))
    (hrest : μ.readN (ptr + 1) 1 = Num.encodeLE 1 (n % 256)) :
    ∃ ω' μ', FreeStepsH p R 4646 ω μ x t ω' μ' x 500 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 2 := by
  have hrf' : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 11) (n₂ := 489) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_4646 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4649 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4652 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4655 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4658 (p := p) (P := P))
    · pvm_simp [h7]
    apply FreeStepsH.step_decode (d_4660 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4663 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4666 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4669 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4672 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4676 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1484 32166 (sp - 40) rd (sp - 32) ptr len 1
      ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) ?mjt ?mbt (by omega) (by omega) (by omega) (by omega) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mwr ?mwb ?mra ?mR0 ?mR8) ?k ?hle2
      (n₁ := 7 * 1 + 50) (n₂ := 432)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7]
      all_goals (congr 1; omega)
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_741]
    case mbt => exact bs_32166
    case mwf | mwr | mwb | mra =>
      intro a h1 h2
      simp only [Memory.writable_writeN, Memory.readable_writeN]
      first | exact hwf a (by omega) (by omega) | exact hwr a (by omega) (by omega) | exact hra a (by omega) (by omega)
    case mR0 | mR8 =>
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE, List.length_cons,
        List.length_nil, hR0, hR8]
    case k =>
      intro ω₂ μ₂ ⟨g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g2 g3 g4 g5 g6 g12
      -- the prefix octet, now in the buffer at sp − 32
      have hb2 : μ₂.read (sp - 32) = UInt8.ofNat (128 + n / 256) := by
        have := gbuf
        simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, Nat.add_zero, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          List.length_cons, List.length_nil, List.cons.injEq, and_true] at this
        rw [this, hb]
      have hbv : (μ₂.read (sp - 40 + 8)).toNat = 128 + n / 256 := by
        rw [show sp - 40 + 8 = sp - 32 by omega, hb2, UInt8.toNat_ofNat']; omega
      have hrd2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
        rw [grd]; exact hrf' a h1 h2
      have hwf2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.writable a = true := fun a h1 h2 => by
        rw [gwr]; exact hwf a h1 h2
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₃) (μ₁ := ?μ₃) (n₁ := 18) (n₂ := 414) ?pre2 ?rest2 ?hle3
      case pre2 =>
        apply FreeStepsH.step_decode (d_32166 (p := p) (P := P))
        · pvm_simp [g7]
        apply FreeStepsH.step_decode (d_32186 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32187 (p := p) (P := P))
        · pvm_simp [g1, hrd2, ↓loadI8_read_sx8]
        have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
        have hand : Exec.bitwise (fun x1 x2 => x1 && x2) (sx8 (μ₂.read (sp - 40 + 8)).toNat) 255 = 128 + n / 256 := by
          rw [bitwise_and_low _ 255 8 (by decide) (by decide), sx8_mod256 _ hX]; omega
        have hbit64 : Exec.bitwise (fun x1 x2 => x1 && x2) (sx8 (μ₂.read (sp - 40 + 8)).toNat) 64 = 0 := by
          rw [bitwise_and_pow2 _ 64 6 (by decide) (by decide), sx8_div64_mod2 _ hX]; split <;> omega
        apply FreeStepsH.step_decode (d_32190 (p := p) (P := P))
        · pvm_simp [hand]
        apply FreeStepsH.step_decode (d_32194 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32197 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32201 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32249 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32251 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32258 (p := p) (P := P))
        · pvm_simp [hbit64]
        apply FreeStepsH.step_decode (d_32261 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32264 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32267 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32334 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32337 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_32340 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_32342 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32344 (p := p) (P := P))
        · pvm_simp []
        exact FreeStepsH.refl
      case rest2 =>
        refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1488 32350 (sp - 40) rd (sp - 32)
          (ptr + 1) (len - 1) 1
          ?q0 ?q1 ?q7 ?q8 ?q9 (by decide) ?qjt ?qbt (by omega) (by omega) (by omega) (by omega) (by decide)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?qwf ?qwr ?qwb ?qra ?qR0 ?qR8)
          ?k2 ?hle4 (n₁ := 7 * 1 + 50) (n₂ := 100)
        case q0 | q1 | q7 | q8 | q9 =>
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none, g1, g7]
          all_goals (congr 1; omega)
        case qjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_743]
        case qbt => exact bs_32350
        case qwf | qwb =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwf a (by omega) (by omega)
        case qwr =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwr a (by omega) (by omega)
        case qra =>
          intro a h1 h2
          simp only [Memory.readable_writeN, grd]
          exact hra a (by omega) (by omega)
        case qR0 | qR8 =>
          simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
            List.length_cons, List.length_nil, gR0, gR8]
        case k2 =>
          intro ω₄ μ₄ ⟨f0, f1, f2, f3, f4, f5, f6, f12, f7, fR0, fR8, fbuf, ffr, frd, fwr⟩
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none] at f0 f1 f2 f3 f4 f5 f6 f12
          have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
          -- frame reads: μ₄ agrees with μ₃ on [sp − 40, sp) outside the buffer octet at sp − 32,
          -- and μ₂ with the pre-call memory
          have e43 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 32 + 1 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => ffr (a + j) (by omega) (by omega) (by omega) (by omega))
          have e21 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 31 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => gfr (a + j) (by omega) (by omega) (by omega) (by omega))
          have hr0 : μ₄.readN (sp - 40 + 32) 8 = Num.encodeLE 8 ω[0].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr5 : μ₄.readN (sp - 40 + 24) 8 = Num.encodeLE 8 ω[5].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr6 : μ₄.readN (sp - 40 + 16) 8 = Num.encodeLE 8 ω[6].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr9 : μ₄.readN (sp - 40) 8 = Num.encodeLE 8 (sx8 (μ₂.read (sp - 40 + 8)).toNat) := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hbuf' : μ₄.readN (sp - 32) 1 = Num.encodeLE 1 (n % 256) := by
            rw [fbuf]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [Memory.readN_congr (n := 1) (a := ptr + 1)
              (fun j hj => gfr (ptr + 1 + j) (by omega) (by omega) (by omega) (by omega))]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            exact hrest
          have hz : ∀ j, 1 ≤ j → j < 8 → μ₄.read (sp - 32 + j) = UInt8.ofNat 0 := by
            intro j hj1 hj2
            rw [ffr _ (by omega) (by omega) (by omega) (by omega), show sp - 32 + j = sp - 40 + 8 + j by omega,
              Memory.read_writeN_at _ _ _ (by simp [two32]) j (by simp; omega)]
            have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          have hr8 : μ₄.readN (sp - 40 + 8) 8 = Num.encodeLE 8 (n % 256) := by
            have s1 := Memory.readN_split μ₄ (sp - 32) 1 7
            have s2 := Num.encodeLE_split 1 7 (n % 256)
            simp only [Nat.reduceAdd, Nat.reducePow] at s1 s2
            rw [show sp - 40 + 8 = sp - 32 by omega, s1, s2, hbuf', Nat.div_eq_of_lt (by omega)]
            congr 1
            simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
              List.map_cons, List.map_nil, List.map_append, List.cons_append, Nat.add_zero, Nat.add_assoc,
              Nat.reduceAdd, hz, Num.encodeLE, Nat.zero_div, Nat.zero_mod]
          have hrd4 : ∀ a, sp - 128 ≤ a → a < sp → μ₄.readable a = true := fun a h1 h2 => by
            rw [frd]; simp only [Memory.readable_writeN]; exact hrd2 a h1 h2
          have handInv : Exec.bitwise (fun x y => x && !y) (sx8 (μ₂.read (sp - 40 + 8)).toNat)
              18446744073709551552 = n / 256 := by
            rw [bitwise_andInv_high _ _ 6 (by decide) (by decide), sx8_mod64 _ hX]; omega
          rw [show ω₄ = regsNF ω₄ [] from rfl]
          refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
          case run₂ =>
            apply FreeStepsH.step_decode (d_32350 (p := p) (P := P))
            · pvm_simp [f7]
            apply FreeStepsH.step_decode (d_32370 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32373 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32376 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr8]
            apply FreeStepsH.step_decode (d_32379 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr9, hX]
            apply FreeStepsH.step_decode (d_32381 (p := p) (P := P))
            · pvm_simp [handInv]
            apply FreeStepsH.step_decode (d_32384 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32387 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32390 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32393 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32394 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32397 (p := p) (P := P))
            · pvm_simp [Nat.mod_add_div', hn]
            apply FreeStepsH.step_decode (d_32399 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr0]
            apply FreeStepsH.step_decode (d_32402 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr5]
            apply FreeStepsH.step_decode (d_32405 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr6]
            apply FreeStepsH.step_decode (d_32408 (p := p) (P := P))
            · pvm_simp [f1, g1]
            apply FreeStepsH.step_decode (d_32411 (p := p) (P := P))
            · pvm_simp [h0, hret, hjt, hbt]
            exact FreeStepsH.refl.mono (Nat.zero_le _)
          case post₂ =>
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_,
              fun a => ?_⟩
            all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
              PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, f2, f3, f4, f12, g2, g3, g4, g12]
            · rw [fR0, show ptr + 1 + 1 = ptr + 2 by omega]
            · rw [fR8, show len - 1 - 1 = len - 2 by omega]
            · rw [ffr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
              rw [gfr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
            · simp only [frd, grd, Memory.readable_writeN]
            · simp only [fwr, gwr, Memory.writable_writeN]
        case hle4 => omega
      case hle3 => omega
    case hle2 => omega
  case hle => decide

/-- **Decoding a 3-octet ℰ(n)**, 2^14 ≤ n < 2^21 (GP (C), general natural
    encoding): the prefix octet 2^8 − 2^6 + ⌊n / 2^16⌋, then ℰ_2(n mod 2^16). -/
theorem decodeU16_len3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296) (hlen : 3 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 32 ≤ sp - 128 ∨ sp ≤ ptr) (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 3 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : 16384 ≤ n ∧ n < 65536)
    (hb : μ.read ptr = UInt8.ofNat (192 + n / 65536))
    (hrest : μ.readN (ptr + 1) 2 = Num.encodeLE 2 (n % 65536)) :
    ∃ ω' μ', FreeStepsH p R 4646 ω μ x t ω' μ' x 500 ∧ DecodeOk ω ω' μ μ' sp rd ptr len n 3 := by
  have hrf' : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₁) (μ₁ := ?μ₁) (n₁ := 11) (n₂ := 489) ?pre ?rest ?hle
  case pre =>
    apply FreeStepsH.step_decode (d_4646 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4649 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4652 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4655 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4658 (p := p) (P := P))
    · pvm_simp [h7]
    apply FreeStepsH.step_decode (d_4660 (p := p) (P := P))
    · pvm_simp [h1, hwf]
    apply FreeStepsH.step_decode (d_4663 (p := p) (P := P))
    · pvm_simp [h1]
    apply FreeStepsH.step_decode (d_4666 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4669 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4672 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_4676 (p := p) (P := P))
    · pvm_simp []
    exact FreeStepsH.refl
  case rest =>
    refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1484 32166 (sp - 40) rd (sp - 32) ptr len 1
      ?m0 ?m1 ?m7 ?m8 ?m9 (by decide) ?mjt ?mbt (by omega) (by omega) (by omega) (by omega) (by decide) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf ?mwr ?mwb ?mra ?mR0 ?mR8) ?k ?hle2
      (n₁ := 7 * 1 + 50) (n₂ := 432)
    case m0 | m1 | m7 | m8 | m9 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7]
      all_goals (congr 1; omega)
    case mjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_741]
    case mbt => exact bs_32166
    case mwf | mwr | mwb | mra =>
      intro a h1 h2
      simp only [Memory.writable_writeN, Memory.readable_writeN]
      first | exact hwf a (by omega) (by omega) | exact hwr a (by omega) (by omega) | exact hra a (by omega) (by omega)
    case mR0 | mR8 =>
      simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE, List.length_cons,
        List.length_nil, hR0, hR8]
    case k =>
      intro ω₂ μ₂ ⟨g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none] at g0 g1 g2 g3 g4 g5 g6 g12
      -- the prefix octet, now in the buffer at sp − 32
      have hb2 : μ₂.read (sp - 32) = UInt8.ofNat (192 + n / 65536) := by
        have := gbuf
        simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
          List.map_cons, List.map_nil, Nat.add_zero, PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          List.length_cons, List.length_nil, List.cons.injEq, and_true] at this
        rw [this, hb]
      have hbv : (μ₂.read (sp - 40 + 8)).toNat = 192 + n / 65536 := by
        rw [show sp - 40 + 8 = sp - 32 by omega, hb2, UInt8.toNat_ofNat']; omega
      have hrd2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.readable a = true := fun a h1 h2 => by
        rw [grd]; exact hrf' a h1 h2
      have hwf2 : ∀ a, sp - 128 ≤ a → a < sp → μ₂.writable a = true := fun a h1 h2 => by
        rw [gwr]; exact hwf a h1 h2
      rw [show ω₂ = regsNF ω₂ [] from rfl]
      refine FreeStepsH.ex_trans (i₁ := 58434) (ω₁ := ?ω₃) (μ₁ := ?μ₃) (n₁ := 20) (n₂ := 412) ?pre2 ?rest2 ?hle3
      case pre2 =>
        apply FreeStepsH.step_decode (d_32166 (p := p) (P := P))
        · pvm_simp [g7]
        apply FreeStepsH.step_decode (d_32186 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32187 (p := p) (P := P))
        · pvm_simp [g1, hrd2, ↓loadI8_read_sx8]
        have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
        have hand : Exec.bitwise (fun x1 x2 => x1 && x2) (sx8 (μ₂.read (sp - 40 + 8)).toNat) 255 = 192 + n / 65536 := by
          rw [bitwise_and_low _ 255 8 (by decide) (by decide), sx8_mod256 _ hX]; omega
        have hbit64 : Exec.bitwise (fun x1 x2 => x1 && x2) (sx8 (μ₂.read (sp - 40 + 8)).toNat) 64 = 64 := by
          rw [bitwise_and_pow2 _ 64 6 (by decide) (by decide), sx8_div64_mod2 _ hX]; split <;> omega
        have hbit32 : Exec.bitwise (fun x1 x2 => x1 && x2) (sx8 (μ₂.read (sp - 40 + 8)).toNat) 32 = 0 := by
          rw [bitwise_and_pow2 _ 32 5 (by decide) (by decide), sx8_div32_mod2 _ hX]; split <;> omega
        apply FreeStepsH.step_decode (d_32190 (p := p) (P := P))
        · pvm_simp [hand]
        apply FreeStepsH.step_decode (d_32194 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32197 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32201 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32249 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32251 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32258 (p := p) (P := P))
        · pvm_simp [hbit64]
        apply FreeStepsH.step_decode (d_32261 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32269 (p := p) (P := P))
        · pvm_simp [hbit32]
        apply FreeStepsH.step_decode (d_32272 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32275 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32278 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32334 (p := p) (P := P))
        · pvm_simp [g1, hwf2]
        apply FreeStepsH.step_decode (d_32337 (p := p) (P := P))
        · pvm_simp [g1]
        apply FreeStepsH.step_decode (d_32340 (p := p) (P := P))
        · pvm_simp [g6]
        apply FreeStepsH.step_decode (d_32342 (p := p) (P := P))
        · pvm_simp []
        apply FreeStepsH.step_decode (d_32344 (p := p) (P := P))
        · pvm_simp []
        exact FreeStepsH.refl
      case rest2 =>
        refine FreeStepsH.bind_ex2 (read_ok (p := p) (P := P) (R := R) x _ _ 1488 32350 (sp - 40) rd (sp - 32)
          (ptr + 1) (len - 1) 2
          ?q0 ?q1 ?q7 ?q8 ?q9 (by decide) ?qjt ?qbt (by omega) (by omega) (by omega) (by omega) (by decide)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?qwf ?qwr ?qwb ?qra ?qR0 ?qR8)
          ?k2 ?hle4 (n₁ := 7 * 2 + 50) (n₂ := 100)
        case q0 | q1 | q7 | q8 | q9 =>
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none, g1, g7]
          all_goals (congr 1; omega)
        case qjt => simp only [Nat.reduceDiv, Nat.reduceSub, jte_743]
        case qbt => exact bs_32350
        case qwf | qwb =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwf a (by omega) (by omega)
        case qwr =>
          intro a h1 h2
          simp only [Memory.writable_writeN, gwr]
          exact hwr a (by omega) (by omega)
        case qra =>
          intro a h1 h2
          simp only [Memory.readable_writeN, grd]
          exact hra a (by omega) (by omega)
        case qR0 | qR8 =>
          simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
            List.length_cons, List.length_nil, gR0, gR8]
        case k2 =>
          intro ω₄ μ₄ ⟨f0, f1, f2, f3, f4, f5, f6, f12, f7, fR0, fR8, fbuf, ffr, frd, fwr⟩
          simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
            PVM.getD_some', List.lookup_nil, Option.getD_none] at f0 f1 f2 f3 f4 f5 f6 f12
          have hX : (μ₂.read (sp - 40 + 8)).toNat < 256 := UInt8.toNat_lt _
          -- frame reads: μ₄ agrees with μ₃ on [sp − 40, sp) outside the buffer octet at sp − 32,
          -- and μ₂ with the pre-call memory
          have e43 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 32 + 2 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => ffr (a + j) (by omega) (by omega) (by omega) (by omega))
          have e21 := fun a (h1 : sp - 40 ≤ a) (h2 : a + 8 ≤ sp) (h3 : a + 8 ≤ sp - 32 ∨ sp - 31 ≤ a) =>
            Memory.readN_congr (n := 8) (a := a) (fun j hj => gfr (a + j) (by omega) (by omega) (by omega) (by omega))
          have hr0 : μ₄.readN (sp - 40 + 32) 8 = Num.encodeLE 8 ω[0].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr5 : μ₄.readN (sp - 40 + 24) 8 = Num.encodeLE 8 ω[5].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr6 : μ₄.readN (sp - 40 + 16) 8 = Num.encodeLE 8 ω[6].toNat := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [e21 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hr9 : μ₄.readN (sp - 40) 8 = Num.encodeLE 8 (sx8 (μ₂.read (sp - 40 + 8)).toNat) := by
            rw [e43 _ (by omega) (by omega) (by omega)]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
              PVM.Num.length_encodeLE, List.length_cons, List.length_nil]
          have hbuf' : μ₄.readN (sp - 32) 2 = Num.encodeLE 2 (n % 65536) := by
            rw [fbuf]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            rw [Memory.readN_congr (n := 2) (a := ptr + 1)
              (fun j hj => gfr (ptr + 1 + j) (by omega) (by omega) (by omega) (by omega))]
            simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE,
              List.length_cons, List.length_nil]
            exact hrest
          have hz : ∀ j, 2 ≤ j → j < 8 → μ₄.read (sp - 32 + j) = UInt8.ofNat 0 := by
            intro j hj1 hj2
            rw [ffr _ (by omega) (by omega) (by omega) (by omega), show sp - 32 + j = sp - 40 + 8 + j by omega,
              Memory.read_writeN_at _ _ _ (by simp [two32]) j (by simp; omega)]
            have : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
            rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          have hr8 : μ₄.readN (sp - 40 + 8) 8 = Num.encodeLE 8 (n % 65536) := by
            have s1 := Memory.readN_split μ₄ (sp - 32) 2 6
            have s2 := Num.encodeLE_split 2 6 (n % 65536)
            simp only [Nat.reduceAdd, Nat.reducePow] at s1 s2
            rw [show sp - 40 + 8 = sp - 32 by omega, s1, s2, hbuf', Nat.div_eq_of_lt (by omega)]
            congr 1
            simp (disch := pvm_arith) only [Memory.readN, List.range_succ, List.range_zero, List.nil_append,
              List.map_cons, List.map_nil, List.map_append, List.cons_append, Nat.add_zero, Nat.add_assoc,
              Nat.reduceAdd, hz, Num.encodeLE, Nat.zero_div, Nat.zero_mod]
          have hrd4 : ∀ a, sp - 128 ≤ a → a < sp → μ₄.readable a = true := fun a h1 h2 => by
            rw [frd]; simp only [Memory.readable_writeN]; exact hrd2 a h1 h2
          have handInv : Exec.bitwise (fun x y => x && !y) (sx8 (μ₂.read (sp - 40 + 8)).toNat)
              18446744073709551584 = n / 65536 := by
            rw [bitwise_andInv_high _ _ 5 (by decide) (by decide), sx8_mod32 _ hX]; omega
          rw [show ω₄ = regsNF ω₄ [] from rfl]
          refine ⟨?ω', ?μ', ?run₂, ?post₂⟩
          case run₂ =>
            apply FreeStepsH.step_decode (d_32350 (p := p) (P := P))
            · pvm_simp [f7]
            apply FreeStepsH.step_decode (d_32370 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32373 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32376 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr8]
            apply FreeStepsH.step_decode (d_32379 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr9, hX]
            apply FreeStepsH.step_decode (d_32381 (p := p) (P := P))
            · pvm_simp [handInv]
            apply FreeStepsH.step_decode (d_32384 (p := p) (P := P))
            · pvm_simp [f6]
            apply FreeStepsH.step_decode (d_32387 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32390 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32393 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32394 (p := p) (P := P))
            · pvm_simp []
            apply FreeStepsH.step_decode (d_32397 (p := p) (P := P))
            · pvm_simp [Nat.mod_add_div', hn]
            apply FreeStepsH.step_decode (d_32399 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr0]
            apply FreeStepsH.step_decode (d_32402 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr5]
            apply FreeStepsH.step_decode (d_32405 (p := p) (P := P))
            · pvm_simp [f1, g1, hrd4, hr6]
            apply FreeStepsH.step_decode (d_32408 (p := p) (P := P))
            · pvm_simp [f1, g1]
            apply FreeStepsH.step_decode (d_32411 (p := p) (P := P))
            · pvm_simp [h0, hret, hjt, hbt]
            exact FreeStepsH.refl.mono (Nat.zero_le _)
          case post₂ =>
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_,
              fun a => ?_⟩
            all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
              PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, f2, f3, f4, f12, g2, g3, g4, g12]
            · rw [fR0, show ptr + 1 + 2 = ptr + 3 by omega]
            · rw [fR8, show len - 1 - 2 = len - 3 by omega]
            · rw [ffr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
              rw [gfr a ha0 (by omega) ha2 (by omega)]
              simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
                List.length_cons, List.length_nil]
            · simp only [frd, grd, Memory.readable_writeN]
            · simp only [fwr, gwr, Memory.writable_writeN]
        case hle4 => omega
      case hle3 => omega
    case hle2 => omega
  case hle => decide

/-- **The `u16` decoder at 4646**, for every n < 2^16: with ℰ(n) (GP (C)) at the reader's pointer, it
    returns ω₈ = n and ω₇ = 0, advances the reader past ℰ(n), and touches only its stack frames, within
    500 steps. -/
theorem decodeU16 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp rd ptr len : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat rd)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 32 ≤ sp - 128 ∨ sp ≤ ptr) (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (n : Nat) (hn : n < 65536)
    (hlen : (Blob.encodeNat n).length ≤ len ∧ len < 4294967296)
    (hra : ∀ a, ptr ≤ a → a < ptr + (Blob.encodeNat n).length → μ.readable a = true)
    (henc : μ.readN ptr (Blob.encodeNat n).length = Blob.encodeNat n) :
    ∃ ω' μ', FreeStepsH p R 4646 ω μ x t ω' μ' x 500 ∧
      DecodeOk ω ω' μ μ' sp rd ptr len n (Blob.encodeNat n).length := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
    rw [he] at hlen hra henc ⊢
    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      Nat.add_zero, List.cons.injEq, and_true, List.length_cons, List.length_nil, Nat.zero_add] at hlen hra henc ⊢
    obtain ⟨ω', μ', hr, hok⟩ := decodeU16_zero (R := R) (p := p) (P := P) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt hbt
      hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 0 rfl henc
    exact ⟨ω', μ', hr.mono (by decide), hok⟩
  · have : n < 128 ∨ (128 ≤ n ∧ n < 16384) ∨ 16384 ≤ n := by omega
    rcases this with h | h | h
    · rw [encodeNat_of_lt n 0 (by decide) hpos (by simp only [Nat.reduceMul, Nat.reducePow]; omega)
        (by simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]; omega)] at hlen hra henc ⊢
      have hsplit := Memory.readN_split μ ptr 1 0
      have h1r : μ.readN ptr 1 = [μ.read ptr] := by simp [Memory.readN]
      simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.div_one, Nat.mod_one, Nat.zero_add,
        List.length_cons, PVM.Num.length_encodeLE] at hlen hra henc hsplit ⊢
      rw [hsplit, h1r] at henc
      simp only [Num.encodeLE, List.cons_append, List.nil_append, List.cons.injEq] at henc
      obtain ⟨hb, hrest⟩ := henc
      obtain ⟨ω', μ', hr, hok⟩ := decodeU16_len1 (R := R) (p := p) (P := P) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt
        hbt hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, by omega⟩ hb
      exact ⟨ω', μ', hr, hok⟩
    · rw [encodeNat_of_lt n 1 (by decide) hpos (by simp only [Nat.reduceMul, Nat.reducePow]; omega)
        (by simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]; omega)] at hlen hra henc ⊢
      have hsplit := Memory.readN_split μ ptr 1 1
      have h1r : μ.readN ptr 1 = [μ.read ptr] := by simp [Memory.readN]
      simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.div_one, Nat.mod_one, Nat.zero_add,
        List.length_cons, PVM.Num.length_encodeLE] at hlen hra henc hsplit ⊢
      rw [hsplit, h1r] at henc
      simp only [Num.encodeLE, List.cons_append, List.nil_append, List.cons.injEq] at henc
      obtain ⟨hb, hrest⟩ := henc
      obtain ⟨ω', μ', hr, hok⟩ := decodeU16_len2 (R := R) (p := p) (P := P) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt
        hbt hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, by omega⟩ hb hrest
      exact ⟨ω', μ', hr, hok⟩
    · rw [encodeNat_of_lt n 2 (by decide) hpos (by simp only [Nat.reduceMul, Nat.reducePow]; omega)
        (by simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd]; omega)] at hlen hra henc ⊢
      have hsplit := Memory.readN_split μ ptr 1 2
      have h1r : μ.readN ptr 1 = [μ.read ptr] := by simp [Memory.readN]
      simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub, Nat.div_one, Nat.mod_one, Nat.zero_add,
        List.length_cons, PVM.Num.length_encodeLE] at hlen hra henc hsplit ⊢
      rw [hsplit, h1r] at henc
      simp only [Num.encodeLE, List.cons_append, List.nil_append, List.cons.injEq] at henc
      obtain ⟨hb, hrest⟩ := henc
      obtain ⟨ω', μ', hr, hok⟩ := decodeU16_len3 (R := R) (p := p) (P := P) x ω μ ret t sp rd ptr len h0 h1 h7 hret hjt
        hbt hsp hrd hptr hlen hrf hpf hpr hwf hwr hra hR0 hR8 n ⟨by omega, by omega⟩ hb hrest
      exact ⟨ω', μ', hr, hok⟩

end Services.Bootstrap
