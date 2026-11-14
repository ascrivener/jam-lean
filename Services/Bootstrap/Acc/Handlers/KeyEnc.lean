import Services.Bootstrap.Acc.Handlers.DesignateAlloc

/-!
# The storage-key encoder (33843)

`add_recent_work_item` and the results store build their storage keys with the function at 33843:
from a key value at kp (a `u16` tag at kp, an `i16` at kp + 2, a payload from kp + 4), it allocates a
buffer of the tag's size (a table in the read-only data at 68680, eight octets per tag), writes the
tag octet and the variant's payload into it with `extend_from_slice`, and stores the `Vec<u8>`
`{cap, ptr, len}` at out (ω₇).

`kb_pre`: the prologue, to the `alloc` call.
-/

namespace Services.Bootstrap.Acc.Handlers.KeyEnc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Acc.Handlers.DesignateAlloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **33843 … 40494**: the frame of 72 octets at S = sp − 72 (ω₀, ω₅, ω₆ saved at S + 64, S + 56,
    S + 48; kp at S, out at S + 8), the tag t (the `u16` at kp) in ω₆, the buffer's size c (the
    table's word at 68680 + 8 · t) in ω₅, and the call of `alloc(c, 1)` with return address 1566. -/
theorem kb_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp kp out t c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat kp) (hsp : 68712 + 72 ≤ sp ∧ sp < 4294967296)
    (hkd : kp + 2 ≤ sp - 72 ∨ sp ≤ kp)
    (hkp : kp + 2 < 4294967296) (hout : out < 18446744073709551616) (ht : t < 4)
    (mt : μ.readN kp 2 = Num.encodeLE 2 t) (mc : μ.readN (68680 + 8 * t) 8 = Num.encodeLE 8 c)
    (hc : c < 18446744073709551616)
    (hrk : ∀ a, kp ≤ a → a < kp + 2 → μ.readable a = true)
    (hrt : ∀ a, 68680 + 8 * t ≤ a → a < 68680 + 8 * t + 8 → μ.readable a = true)
    (hw : ∀ a, sp - 72 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 33843 ω μ x 40494 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1566 ∧ ω'[1] = UInt64.ofNat (sp - 72) ∧ ω'[5] = UInt64.ofNat c ∧
      ω'[6] = UInt64.ofNat t ∧ ω'[7] = UInt64.ofNat c ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 72) 8 = Num.encodeLE 8 kp ∧ μ'.readN (sp - 64) 8 = Num.encodeLE 8 out ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 72 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rt : rdN μ kp 2 = t := by
    show Num.decodeLE _ = _
    rw [mt, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]
  have rc := rd8 hc mc
  rw [show ω = regsNF ω [] from rfl]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceMul, Nat.reduceAdd] at rc hrt
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, h8, hsp, hkp, hkd, hout, rt, rc, hrk, hrt, hw, hr, bs_40494, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_,
        fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
      · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      all_goals try rw [show sp - 72 + 64 = sp - 8 by omega, show sp - 72 + 56 = sp - 16 by omega,
        show sp - 72 + 48 = sp - 24 by omega, show sp - 72 + 8 = sp - 64 by omega]
      all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
      all_goals try rd_simp []
      all_goals try rfl
      all_goals try (congr 1; omega)

/-- **33886 … 58508**, `alloc` returned ptr ≠ 0 (ω₇) for the buffer of c octets (ω₅), with the tag t in
    ω₆: the `Vec` `{c, ptr, 0}` at S + 16, the tag octet at S + 44, and the call
    `extend(S + 16, S + 44, 1)`, return address 1568 (t = 2), 1572 (t = 1) or 1574 (t = 0, 3). -/
theorem kb_vec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S c ptr t : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat c)
    (h6 : ω[6] = UInt64.ofNat t) (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0)
    (hptr : ptr < 18446744073709551616) (hc : c < 18446744073709551616) (ht : t < 4)
    (hS : S + 72 < 4294967296) (hw : ∀ a, S + 16 ≤ a → a < S + 48 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 33886 ω μ x 58508 ω'
      ((((μ.writeN (S + 16) (Num.encodeLE 8 c)).writeN (S + 24) (Num.encodeLE 8 ptr)).writeN (S + 32)
        (Num.encodeLE 8 0)).writeN (S + 44) [UInt8.ofNat t]) x 12 ∧
      ω'[0] = UInt64.ofNat (if t = 2 then 1568 else if t = 1 then 1572 else 1574) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat c ∧ ω'[6] = UInt64.ofNat t ∧
      ω'[7] = UInt64.ofNat (S + 16) ∧ ω'[8] = UInt64.ofNat (S + 44) ∧ ω'[9] = UInt64.ofNat 1 := by
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hptr]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h6, h7, hp0', hS, hw, bs_58508]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, h6]

/-- **33992 … 58508** (t = 1, after the tag octet): the `i32` at kp + 4 stored at S + 44 and the call
    `extend(S + 16, S + 44, 4)`, return address 1574. -/
theorem kb_t1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S kp v : Nat) (h1 : ω[1] = UInt64.ofNat S) (hv : v < 4294967296)
    (hS : S + 72 < 4294967296) (hkp : kp + 8 < 4294967296) (hkd : kp + 8 ≤ S + 44 ∨ S + 48 ≤ kp + 4)
    (m0 : μ.readN S 8 = Num.encodeLE 8 kp) (mw : μ.readN (kp + 4) 4 = Num.encodeLE 4 v)
    (hrk : ∀ a, kp + 4 ≤ a → a < kp + 8 → μ.readable a = true)
    (hrf : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true)
    (hw : ∀ a, S + 44 ≤ a → a < S + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 33992 ω μ x 58508 ω' μ' x 8 ∧ μ' = μ.writeN (S + 44) (Num.encodeLE 4 v) ∧
      ω'[0] = UInt64.ofNat 1574 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 16) ∧ ω'[8] = UInt64.ofNat (S + 44) ∧ ω'[9] = UInt64.ofNat 4 := by
  have r0 := rd8 (by omega) m0
  have rv : rdN μ (kp + 4) 4 = v := by
    show Num.decodeLE _ = _
    rw [mw, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hkp, r0, rv, hrk, hrf, hw, bs_58508, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · congr 2; split <;> omega
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

end Services.Bootstrap.Acc.Handlers.KeyEnc
