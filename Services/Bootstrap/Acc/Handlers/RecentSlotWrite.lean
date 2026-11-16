import Services.Bootstrap.Acc.Handlers.RecentMatch

/-!
# `add_recent_work_item`'s slot write: the straight-line segments (8172 … 8326)

Spec `addRecent`'s `store (.recent c) (encodeRecent package item)` (GP v0.8.0 Appendix B, Ω_W) and the
new counter:
1. 8172 … 8263: the tag-1 key value {1, c} at sp + 1568 again; (package, item) copied to sp + 1144 (the
   32 octets at sp + 512, the `u16` at sp + 176); an inlined callee frame (sp − 96: ω₀ = 286, ω₅, ω₆
   and the key value's address saved) and the call of `alloc` (40494) for 34 octets, returning to
   32414 (return address 1490);
2. 32414 … 32583, the callee's body: null → the trap at 32584; else a `Vec { 34, ptr, 0 }` at
   sp − 64, two `extend_from_slice` (58508) of the 32 octets and the `u16` (return addresses 1492,
   1494), the key encoder (33843, 1496), `set` (48104, 1498), `dealloc` of both buffers (40613, 1500,
   1502), and the return (286 → 8266) with ω₇ = −1 for `Ok` and `set`'s error code otherwise;
3. 8266 … 8323: ω₇'s low octet must be 255, else the trap at 15361 (`unwrap`); then 2·𝖢·𝖨 from the
   protocol parameters' statics (`u16` at 196616, `u64` at 196696), shifted in 32 bits, a trap at
   15361 if it is 0; the new counter ((c + 1) mod 2³²) mod 2·𝖢·𝖨 in ω₇ (`remU32`, quirk Q19).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlotWrite

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8172 … 8217**: the tag-1 key value {1, c} at sp + 1568 (the `u16` 1, c as a `u32` at sp + 1572), the
    32 octets at sp + 512 (the words q₀ … q₃) copied to sp + 1144, and the low two octets of the word v at
    sp + 176 to sp + 1176. -/
theorem sw_pre1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp c q0 q1 q2 q3 v : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat c)
    (hc : c < 18446744073709551616) (hsp : sp + 1604 < 4294967296)
    (m0 : μ.readN (sp + 512) 8 = Num.encodeLE 8 q0) (m1 : μ.readN (sp + 520) 8 = Num.encodeLE 8 q1)
    (m2 : μ.readN (sp + 528) 8 = Num.encodeLE 8 q2) (m3 : μ.readN (sp + 536) 8 = Num.encodeLE 8 q3)
    (hq0 : q0 < 2 ^ 64) (hq1 : q1 < 2 ^ 64) (hq2 : q2 < 2 ^ 64) (hq3 : q3 < 2 ^ 64)
    (mv : μ.readN (sp + 176) 8 = Num.encodeLE 8 v) (hv : v < 2 ^ 64)
    (hr1 : ∀ a, sp + 176 ≤ a → a < sp + 184 → μ.readable a = true)
    (hr2 : ∀ a, sp + 512 ≤ a → a < sp + 544 → μ.readable a = true)
    (hw1 : ∀ a, sp + 1144 ≤ a → a < sp + 1178 → μ.writable a = true)
    (hw2 : ∀ a, sp + 1568 ≤ a → a < sp + 1576 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8172 ω μ x 8221 ω' μ' x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp + 1568) 2 = Num.encodeLE 2 1 ∧ μ'.readN (sp + 1572) 4 = Num.encodeLE 4 c ∧
      μ'.readN (sp + 1144) 8 = Num.encodeLE 8 q0 ∧ μ'.readN (sp + 1152) 8 = Num.encodeLE 8 q1 ∧
      μ'.readN (sp + 1160) 8 = Num.encodeLE 8 q2 ∧ μ'.readN (sp + 1168) 8 = Num.encodeLE 8 q3 ∧
      μ'.readN (sp + 1176) 2 = Num.encodeLE 2 v ∧
      (∀ a, a < 4294967296 → (a < sp + 1144 ∨ sp + 1178 ≤ a) → (a < sp + 1568 ∨ sp + 1576 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := Handlers.DesignateAlloc.rd8 hq0 m0
  have r1 := Handlers.DesignateAlloc.rd8 hq1 m1
  have r2 := Handlers.DesignateAlloc.rd8 hq2 m2
  have r3 := Handlers.DesignateAlloc.rd8 hq3 m3
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hsp, r0, r1, r2, r3, rv, hr1, hr2, hw1, hw2, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1' h2' => ?_,
      fun a => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try exact encodeLE_mod 4 c
    all_goals try exact encodeLE_mod 2 v

/-- **8221 … 8263**: the inlined callee frame at S = sp − 96 (ω₀ = 286 at S + 88, ω₅ and ω₆ at S + 80
    and S + 72, the key value's address sp + 1568 at S + 24), ω₅ := sp + 1144, ω₆ := 34, and the call
    of `alloc(34, 1)` (40494) with return address 1490. -/
theorem sw_pre2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 68712 + 96 ≤ sp ∧ sp + 1604 < 4294967296)
    (hw : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8221 ω μ x 40494 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1490 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat (sp + 1144) ∧
      ω'[6] = UInt64.ofNat 34 ∧ ω'[7] = UInt64.ofNat 34 ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 72) 8 = Num.encodeLE 8 (sp + 1568) ∧ μ'.readN (sp - 8) 8 = Num.encodeLE 8 286 ∧
      μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧ μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 96 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hsp, hw, hr, bs_40494, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try rw [show sp - 96 + 88 = sp - 8 by omega, show sp - 96 + 80 = sp - 16 by omega,
      show sp - 96 + 72 = sp - 24 by omega, show sp - 96 + 24 = sp - 72 by omega]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- `alloc`'s return (40611) to 32414 (ω₀ = 1490). -/
theorem sw_j1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1490) : FreeStepsH p R 40611 ω μ x 32414 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **32414, `alloc` returned null**: the branch to the trap at 32584. -/
theorem sw_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) : FreeStepsH p R 32414 ω μ x 32584 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7]

/-- The trap at 32584 (the value buffer's allocation failed): ☇ (GP §A.5.1). -/
theorem trap_32584 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 32584 ω μ .panic ω μ := by
  have hd := d_32584 (p := p) (P := P)
  have hs : P.freeStep 32584 ω μ = (.panic, P.next 32584, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- **32414 … 32435, `alloc` returned ptr ≠ 0** (ω₇), the capacity c in ω₆: the `Vec { c, ptr, 0 }` at
    T + 32, and the call `extend(T + 32, ω₅, 32)` (58508) with return address 1492. -/
theorem sw_v1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T c ptr : Nat) (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat c)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 18446744073709551616)
    (hc : c < 18446744073709551616) (hT : T + 96 < 4294967296)
    (hw : ∀ a, T + 32 ≤ a → a < T + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32414 ω μ x 58508 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1492 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 32) ∧ ω'[8] = ω[5] ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (T + 32) 8 = Num.encodeLE 8 c ∧ μ'.readN (T + 40) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (T + 48) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < T + 32 ∨ T + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hptr]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hp0', hT, hw, bs_58508, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, ?_, by reg_val, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try (simp only [h6, h7, UInt64.toNat_ofNat']; congr 1; omega)

/-- **32441 … 32456**: the `u16` v at src + 32 (ω₅ = src) stored at T + 56, and the call
    `extend(T + 32, T + 56, 2)` (58508) with return address 1494. -/
theorem sw_v2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T src v : Nat) (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat src)
    (hT : T + 96 < 4294967296) (hsrc : src + 34 < 4294967296)
    (mv : μ.readN (src + 32) 2 = Num.encodeLE 2 v) (hv : v < 65536)
    (hr : ∀ a, src + 32 ≤ a → a < src + 34 → μ.readable a = true)
    (hw : ∀ a, T + 56 ≤ a → a < T + 58 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32441 ω μ x 58508 ω' μ' x 6 ∧
      ω'[0] = UInt64.ofNat 1494 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 32) ∧ ω'[8] = UInt64.ofNat (T + 56) ∧ ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (T + 56) 2 = Num.encodeLE 2 v ∧
      (∀ a, a < 4294967296 → (a < T + 56 ∨ T + 58 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (src + 32) 2 = v := by
    show Num.decodeLE _ = _; rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hT, hsrc, rv, hr, hw, bs_58508, rdN_writeN_disjoint, ↓rdN_fold]
  · have hsx : ((if v < 32768 then (v : Int) else (v : Int) - 65536) % 18446744073709551616).toNat % 65536 = v := by
      split <;> omega
    refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (rw [← encodeLE_mod 2 v]; congr 1; simp only [hsx]; omega)
    all_goals try (congr 1; omega)

/-- **32462 … 32483**: the value's `Vec { c, ptr, len }` (at T + 32) split: c to T + 16, ptr to ω₅, len to
    T + 8; then the key encoder (33843) with out ω₇ = T + 32, the key value ω₈ (the word at T + 24) and
    return address 1496. -/
theorem sw_v3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T c ptr len kp : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 96 < 4294967296)
    (hc : c < 2 ^ 64) (hptr : ptr < 2 ^ 64) (hlen : len < 2 ^ 64) (hkp : kp < 2 ^ 64)
    (mc : μ.readN (T + 32) 8 = Num.encodeLE 8 c) (mp : μ.readN (T + 40) 8 = Num.encodeLE 8 ptr)
    (ml : μ.readN (T + 48) 8 = Num.encodeLE 8 len) (mk : μ.readN (T + 24) 8 = Num.encodeLE 8 kp)
    (hr : ∀ a, T + 24 ≤ a → a < T + 56 → μ.readable a = true)
    (hw : ∀ a, T + 8 ≤ a → a < T + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32462 ω μ x 33843 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1496 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat ptr ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 32) ∧ ω'[8] = UInt64.ofNat kp ∧
      μ'.readN (T + 16) 8 = Num.encodeLE 8 c ∧ μ'.readN (T + 8) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < T + 8 ∨ T + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  have rk := Handlers.DesignateAlloc.rd8 hkp mk
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hT, rc, rp, rl, rk, hr, hw, bs_33843, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **32489 … 32507**: the key's `Vec { kc, kptr, klen }` at T + 32, the value's ptr in ω₅ (saved at T)
    and its length at T + 8: the call of `set` (48104) with out ω₇ = T + 56, the key ω₈ = kptr (ω₉ = klen
    octets), the value ω₁₀ = ptr (ω₁₁ = len octets), kptr kept in ω₆ and return address 1498. -/
theorem sw_v4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T ptr kptr klen len : Nat) (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat ptr)
    (hT : T + 96 < 4294967296) (hptr : ptr < 2 ^ 64) (hkptr : kptr < 2 ^ 64) (hklen : klen < 2 ^ 64)
    (hlen : len < 2 ^ 64)
    (mp : μ.readN (T + 40) 8 = Num.encodeLE 8 kptr) (mk : μ.readN (T + 48) 8 = Num.encodeLE 8 klen)
    (ml : μ.readN (T + 8) 8 = Num.encodeLE 8 len)
    (hr : ∀ a, T + 8 ≤ a → a < T + 56 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32489 ω μ x 48104 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1498 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat ptr ∧
      ω'[6] = UInt64.ofNat kptr ∧ ω'[7] = UInt64.ofNat (T + 56) ∧ ω'[8] = UInt64.ofNat kptr ∧
      ω'[9] = UInt64.ofNat klen ∧ ω'[10] = UInt64.ofNat ptr ∧ ω'[11] = UInt64.ofNat len ∧
      μ'.readN T 8 = Num.encodeLE 8 ptr ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rp := Handlers.DesignateAlloc.rd8 hkptr mp
  have rk := Handlers.DesignateAlloc.rd8 hklen mk
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hT, rp, rk, rl, hr, hw, bs_48104, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
      by reg_val, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    rotate_left
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5]
    rotate_right
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (simp only [h5, UInt64.toNat_ofNat']; congr 1; omega)
    all_goals try (congr 1; omega)

/-- **`set`'s returns** (the `jumpInd` at 48158, 48250 or 48235) with ω₀ = 1498: on to 32513. -/
theorem sw_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (e : Nat) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 1498) :
    FreeStepsH p R e ω μ x 32513 ω μ x 1 := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [show ω = regsNF ω [] from rfl]
    pvm_go [h0]

/-- **32513 … 32533**, the key's capacity kc ≠ 0 (at T + 32): `set`'s result word r (at T + 56) saved at
    T + 24, the octet b at T + 64 in ω₅, and the call of `dealloc` (40613) with ω₇ = ω₆ (the key's buffer)
    and return address 1500. -/
theorem sw_d1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T kc r b : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 96 < 4294967296)
    (hkc : kc < 2 ^ 64) (hk0 : kc ≠ 0) (hr64 : r < 2 ^ 64) (hb : b < 256)
    (mk : μ.readN (T + 32) 8 = Num.encodeLE 8 kc) (mr : μ.readN (T + 56) 8 = Num.encodeLE 8 r)
    (mb : μ.readN (T + 64) 1 = Num.encodeLE 1 b)
    (hr : ∀ a, T + 32 ≤ a → a < T + 72 → μ.readable a = true)
    (hw : ∀ a, T + 24 ≤ a → a < T + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32513 ω μ x 40613 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1500 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat b ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ μ'.readN (T + 24) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (a < T + 24 ∨ T + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rk := Handlers.DesignateAlloc.rd8 hkc mk
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have rb : rdN μ (T + 64) 1 = b := by
    show Num.decodeLE _ = _; rw [mb, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hb]
  have hk0' : kc % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hkc]; exact hk0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hT, rk, rr, rb, hk0', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_, ?_, fun a ha h1' => ?_, fun a => ?_,
      fun a => ?_⟩
    rotate_left
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    rotate_right
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
        List.lookup_nil, Option.getD_none]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **32539 … 32550**, the value's capacity c ≠ 0 (at T + 16): the call of `dealloc` (40613) with
    ω₇ = the word at T (the value's buffer) and return address 1502. Memory is kept. -/
theorem sw_d2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T c ptr : Nat) (h1 : ω[1] = UInt64.ofNat T) (hT : T + 96 < 4294967296)
    (hc : c < 2 ^ 64) (hc0 : c ≠ 0) (hptr : ptr < 2 ^ 64)
    (mc : μ.readN (T + 16) 8 = Num.encodeLE 8 c) (mp : μ.readN T 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, T ≤ a → a < T + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 32539 ω μ x 40613 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1502 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat ptr := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have hc0' : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, rc, rp, hc0', hr, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
      List.lookup_nil, Option.getD_none]

/-- **32556 … 32582, the return**: ω₇ := −1 if `set`'s result word r (at T + 24) is not −1 (`Ok`), else
    ω₅ (the error code); ω₀, ω₅, ω₆ restored from T + 88, T + 80, T + 72, the frame popped, and the
    return through ω₀ = 286 to 8266. -/
theorem sw_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (T r b v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat b)
    (hT : T + 96 < 4294967296) (hb : b < 2 ^ 64) (hr64 : r < 2 ^ 64) (hv5 : v5 < 2 ^ 64) (hv6 : v6 < 2 ^ 64)
    (mr : μ.readN (T + 24) 8 = Num.encodeLE 8 r) (m0 : μ.readN (T + 88) 8 = Num.encodeLE 8 286)
    (m5 : μ.readN (T + 80) 8 = Num.encodeLE 8 v5) (m6 : μ.readN (T + 72) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, T + 24 ≤ a → a < T + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 32556 ω μ x 8266 ω' μ x 10 ∧
      ω'[1] = UInt64.ofNat (T + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) := by
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have r0 := Handlers.DesignateAlloc.rd8 (by decide) m0
  have r5 := Handlers.DesignateAlloc.rd8 hv5 m5
  have r6 := Handlers.DesignateAlloc.rd8 hv6 m6
  rw [show ω = regsNF ω [] from rfl]
  by_cases hr1 : r = 18446744073709551615
  · subst hr1
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, rr, r0, r5, r6, hr, ↓rdN_fold]
    · refine ⟨?_, by reg_val, by reg_val, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5]
      all_goals try (congr 1; omega)
      all_goals try rw [Nat.mod_eq_of_lt hb]
  · have hr1' : (r + 1) % 18446744073709551616 ≠ 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, rr, r0, r5, r6, hr, hr1', ↓rdN_fold]
    · refine ⟨?_, by reg_val, by reg_val, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5, hr1]
      all_goals try (congr 1; omega)

/-- **The protocol parameters' statics** (written by the entry prologue's `apply()` of the fetched
    parameters, at 56279 and 56205): 𝖢 as a `u16` at 196616 and 𝖨 as a `u64` at 196696. -/
def ParamStatics (μ : Memory) (C I : Nat) : Prop :=
  μ.readN 196616 2 = Num.encodeLE 2 C ∧ C < 65536 ∧ μ.readN 196696 8 = Num.encodeLE 8 I ∧ I < 2 ^ 64

/-- **The ring fits in 32 bits**: 0 < 2·𝖢·𝖨 < 2³², so the binary's 32-bit ring size is 2·𝖢·𝖨. A named
    hypothesis on the chain parameters (the full parameters give 2·341·16 = 10912). -/
def RingFits (C I : Nat) : Prop := 0 < 2 * C * I ∧ 2 * C * I < 2 ^ 32

open Services.Bootstrap.Decode.HeapCtx in
/-- The read-write data 196608 … 208896 (the globals among it) is writable in the allocator's context. -/
theorem rw_writable {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State} (H : HeapCtxC code pb S0 S1 μ s) :
    ∀ a, 196608 ≤ a → a < 208896 → μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, -⟩ := H.pages
  intro a h1 h2
  exact HeapPages.wrAt hp hhb H.st a (.inl ⟨h1, by omega⟩)

/-- **8266 … 8309, `Ok`** (ω₇ = −1): the low octet is 255; 2·𝖢·𝖨 from the statics, computed in 32 bits
    (`shloLImm32`), in ω₇; the addresses 196616 and 196696 saved at sp + 96 and sp + 88. -/
theorem sw_ok1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp C I : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat 18446744073709551615) (hsp : 2147483648 ≤ sp ∧ sp + 1604 < 4294967296)
    (hPS : ParamStatics μ C I) (hR : RingFits C I)
    (hr : ∀ a, 196616 ≤ a → a < 196704 → μ.readable a = true)
    (hw : ∀ a, sp + 88 ≤ a → a < sp + 104 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 8266 ω μ x 8312 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[7].toNat % 4294967296 = 2 * C * I ∧
      (∀ a, a < 4294967296 → (a < sp + 88 ∨ sp + 104 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨mC, hC, mI, hI⟩ := hPS
  obtain ⟨hR0, hR1⟩ := hR
  have rC : rdN μ 196616 2 = C := by
    show Num.decodeLE _ = _; rw [mC, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hC]
  have rI := Handlers.DesignateAlloc.rd8 hI mI
  have hn : 2 * C * I = C * I * 2 := by rw [Nat.mul_comm 2 C, Nat.mul_right_comm]
  rw [hn] at hR0 hR1 ⊢
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hsp, rC, rI, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
      omega
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl

/-- **8312 … 8323**: ω₇ = w with w mod 2³² ≠ 0, so no trap; ω₅ := c + 1 (64-bit) and ω₇ :=
    ((c + 1) mod 2³²) mod (w mod 2³²) in its low 32 bits (`remU32`). -/
theorem sw_ok2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (c w : Nat) (h5 : ω[5] = UInt64.ofNat c) (h7 : ω[7] = UInt64.ofNat w)
    (hc : c < 2 ^ 64) (hw : w < 2 ^ 64) (hw0 : w % 4294967296 ≠ 0) :
    ∃ ω', FreeStepsH p R 8312 ω μ x 8326 ω' μ x 4 ∧ ω'[1] = ω[1] ∧
      ω'[7].toNat % 4294967296 = (c + 1) % 4294967296 % (w % 4294967296) := by
  have hw0' : w % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hw]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h5, h7, hw0', hw0]
  · refine ⟨?_, ?_⟩
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    · have hy : (c + 1) % 4294967296 % (w % 4294967296) < 4294967296 :=
        Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))
      have hm : (c + 1) % 18446744073709551616 % 4294967296 = (c + 1) % 4294967296 :=
        Nat.mod_mod_of_dvd _ (by decide)
      simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h7, Num.sext, Nat.mod_eq_of_lt hw, hm]
      generalize (c + 1) % 4294967296 % (w % 4294967296) = y at hy ⊢
      omega

/-- **8266 … 8276, `Err`** (ω₇ = 3, `set`'s FULL code): the trap at 15361 (`unwrap` of `Err`). -/
theorem sw_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 3) : ∃ ω', FreeStepsH p R 8266 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

end Services.Bootstrap.Acc.Handlers.RecentSlotWrite
