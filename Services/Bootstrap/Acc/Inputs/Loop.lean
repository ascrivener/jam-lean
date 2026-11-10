import Services.Bootstrap.Acc.Inputs.ItemCall
import Services.Bootstrap.Acc.Inputs.FinishGrowCall

/-!
# `Vec<AccumulateItem>::decode` (44916), the loop

See the Acc README for the map. With n ≤ 89 items (the temporary bound) the buffer of n·184 octets is
allocated once (`fg_new_call`) and never grown.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **44916 … 45036**, n > 0 items (n ≤ 89): the 480-octet frame (s = sp − 480; ω₀, ω₅, ω₆ at
    s + 472, + 464, + 456), out at s, the reader at s + 48, `Vec { cap 0, ptr 8, len 0 }` at s + 64,
    n at s + 32, and `finish_grow` for n·184 octets (align 8) into s + 272 (return address 2040). -/
theorem lp_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd) (h9 : ω[9] = UInt64.ofNat n) (hn : 0 < n ∧ n ≤ 89)
    (hsp : 65536 + 480 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 480 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 44916 ω μ x 40852 ω' μ' x 60 ∧
      ω'[0] = UInt64.ofNat 2040 ∧ ω'[1] = UInt64.ofNat (sp - 480) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (sp - 480 + 272) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 8 ∧ ω'[12] = UInt64.ofNat 184 ∧
      rdN μ' (sp - 480 + 472) 8 = ω[0].toNat ∧ rdN μ' (sp - 480 + 464) 8 = ω[5].toNat ∧
      rdN μ' (sp - 480 + 456) 8 = ω[6].toNat ∧ rdN μ' (sp - 480) 8 = out ∧ rdN μ' (sp - 480 + 48) 8 = rd ∧
      rdN μ' (sp - 480 + 32) 8 = n ∧ rdN μ' (sp - 480 + 40) 8 = n ∧ rdN μ' (sp - 480 + 56) 8 = 89 ∧
      rdN μ' (sp - 480 + 64) 8 = 0 ∧ rdN μ' (sp - 480 + 72) 8 = 8 ∧ rdN μ' (sp - 480 + 80) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 480 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 480 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hnm : n % 18446744073709551616 = n := by omega
  have hn0 : n ≠ 0 := by omega
  have z : ∀ μ0 : Memory, rdN (μ0.writeN (sp - 480 + 64) [UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0,
      UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0, UInt8.ofNat 0]) (sp - 480 + 64) 8 = 0 := by
    intro μ0; unfold rdN
    rw [PVM.Memory.readN_writeN_same μ0 (sp - 480 + 64) 8 _ rfl (by unfold PVM.two32; omega)]; rfl
  have hmin : (if n < 89 then n else 89) = n := by split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, h9, hnm, hn0, z, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8, h9, hnm, z]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | decide
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (UInt64.toNat_lt _))

/-- 41175: `finish_grow`'s return, through entry 1019 (2040), to 45042. -/
theorem lp_fg_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2040) : FreeStepsH p R 41175 ω μ x 45042 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **45042 … 45122**, the buffer allocated (`Ok`: 0 at s + 272, the pointer q at s + 280): capacity n
    and q stored in the `Vec` (s + 64, + 72), and the first item's decode into the stack slot s + 88
    (ω₈ = the reader, return address 2044). -/
theorem lp_buf {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s rd n q : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat n)
    (m272 : rdN μ (s + 272) 8 = 0) (m280 : rdN μ (s + 280) 8 = q) (m40 : rdN μ (s + 40) 8 = n)
    (m56 : rdN μ (s + 56) 8 = 89) (m48 : rdN μ (s + 48) 8 = rd)
    (hs : 65536 ≤ s ∧ s + 480 < 4294967296) (hn : n < 18446744073709551616)
    (hwf : ∀ a, s ≤ a → a < s + 480 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45042 ω μ x 45126 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 2044 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (s + 88) ∧ ω'[8] = UInt64.ofNat rd ∧
      rdN μ' (s + 64) 8 = n ∧ rdN μ' (s + 72) 8 = q ∧ rdN μ' (s + 56) 8 = q ∧
      (∀ a, a < 4294967296 → (a < s + 56 ∨ s + 64 ≤ a) → (a < s + 64 ∨ s + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 480 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hq : q < 18446744073709551616 := by rw [← m280]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, m272, m280, m40, m56, m48, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | rfl

/-- 47072: a transfer's decode returns, through entry 1021 (2044), to 45168. -/
theorem lp_ret_tr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2044) : FreeStepsH p R 47072 ω μ x 45168 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- 47332: an operand's decode returns, through entry 1021 (2044), to 45168. -/
theorem lp_ret_op {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2044) : FreeStepsH p R 47332 ω μ x 45168 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **45168 … 45186**, an item decoded (its slot's first word not −2): the copy of the 184-octet slot
    s + 88 to s + 272 (return address 2046). -/
theorem lp_chk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s : Nat) (h1 : ω[1] = UInt64.ofNat s) (m88 : rdN μ (s + 88) 8 ≠ 18446744073709551614)
    (hs : 65536 ≤ s ∧ s + 480 < 4294967296) (hrf : ∀ a, s ≤ a → a < s + 480 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 45168 ω μ x 68729 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 2046 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (s + 272) ∧ ω'[8] = UInt64.ofNat (s + 88) ∧ ω'[9] = UInt64.ofNat 184 := by
  have m88' : rdN μ (s + 88) 8 % 18446744073709551616 ≠ 18446744073709551614 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)]; exact m88
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m88', hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | exact UInt64.ofNat_toNat
      | rfl

/-- **45192 … 45097**, the slot copied to s + 272, with len L < cap n: the copy of it to the buffer at
    q + 184·L (return address 2042); q kept at s + 56. -/
theorem lp_step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s n q L : Nat) (h1 : ω[1] = UInt64.ofNat s) (m64 : rdN μ (s + 64) 8 = n) (m72 : rdN μ (s + 72) 8 = q)
    (m80 : rdN μ (s + 80) 8 = L) (hL : L < n) (hq : q + 184 * n < 4294967296)
    (hs : 65536 ≤ s ∧ s + 480 < 4294967296) (hwf : ∀ a, s ≤ a → a < s + 480 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45192 ω μ x 68729 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2042 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat L ∧
      ω'[7] = UInt64.ofNat (q + 184 * L) ∧ ω'[8] = UInt64.ofNat (s + 272) ∧ ω'[9] = UInt64.ofNat 184 ∧
      rdN μ' (s + 56) 8 = q ∧
      (∀ a, a < 4294967296 → (a < s + 56 ∨ s + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 480 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hn : n < 18446744073709551616 := by rw [← m64]; exact rdN_lt64 _ _
  have hne : ¬ (n = L) := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m64, m72, m80, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show L < 18446744073709551616 by omega),
    hne, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | exact UInt64.ofNat_toNat
      | rfl

/-- **45103 … 45122**, the slot copied into the buffer, more items left (count c > 1): len L + 1 at
    s + 80, ω₅ = c − 1, and the next item's decode into s + 88 (return address 2044). -/
theorem lp_next {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s rd L c : Nat) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat L)
    (m48 : rdN μ (s + 48) 8 = rd) (hc : 1 < c ∧ c < 18446744073709551616) (hL : L + 1 < 18446744073709551616)
    (hs : 65536 ≤ s ∧ s + 480 < 4294967296) (hwf : ∀ a, s ≤ a → a < s + 480 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45103 ω μ x 45126 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 2044 ∧ ω'[1] = UInt64.ofNat s ∧ ω'[5] = UInt64.ofNat (c - 1) ∧
      ω'[7] = UInt64.ofNat (s + 88) ∧ ω'[8] = UInt64.ofNat rd ∧
      rdN μ' (s + 80) 8 = L + 1 ∧
      (∀ a, a < 4294967296 → (a < s + 80 ∨ s + 88 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 480 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hc' : (c + 18446744073709551615) % 18446744073709551616 = c - 1 := by omega
  have hc0 : c - 1 ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, m48, hc', hc0, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | exact UInt64.ofNat_toNat
      | rfl

/-- **45103 … 45613**, the last item copied into the buffer (count 1): `Vec { cap n, ptr q, len L + 1 }`
    written at out (cap at + 0, ptr at + 8, len at + 16), ω₀, ω₅, ω₆ restored from s + 472, + 464,
    + 456 and the frame popped, at the return's `jumpInd`. -/
theorem lp_last {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s out n q L : Nat) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat L)
    (m0 : rdN μ s 8 = out) (m32 : rdN μ (s + 32) 8 = n) (m40 : rdN μ (s + 40) 8 = n)
    (m56 : rdN μ (s + 56) 8 = q) (m64 : rdN μ (s + 64) 8 = n) (m72 : rdN μ (s + 72) 8 = q)
    (hn : n < 18446744073709551615) (hL : L + 1 < 18446744073709551616)
    (hs : 65536 ≤ s ∧ s + 480 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (dso : out + 24 ≤ s ∨ s + 480 ≤ out)
    (hwf : ∀ a, s ≤ a → a < s + 480 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45103 ω μ x 45613 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat (rdN μ (s + 472) 8) ∧ ω'[1] = UInt64.ofNat (s + 480) ∧
      ω'[5] = UInt64.ofNat (rdN μ (s + 464) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (s + 456) 8) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = q ∧ rdN μ' (out + 16) 8 = L + 1 ∧
      (∀ a, a < 4294967296 → (a < s + 80 ∨ s + 88 ≤ a) → (a < s + 272 ∨ s + 288 ≤ a) →
        (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, s ≤ a → a < s + 480 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  have hq : q < 18446744073709551616 := by rw [← m72]; exact rdN_lt64 _ _
  have hnn : n % 18446744073709551616 ≠ 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, m0, m32, m40, m56, m64, m72, hnn, hwf, hr, hwo, hro, rdN_writeN_disjoint,
    ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h6]
    all_goals try with_reducible rfl
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | with_reducible exact Nat.mod_eq_of_lt (by omega)
    all_goals first
      | (congr 1; omega)
      | with_reducible exact Nat.mod_eq_of_lt (rdN_lt64 _ _)
      | (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
      | exact UInt64.ofNat_toNat
      | rfl

end Services.Bootstrap.Acc
