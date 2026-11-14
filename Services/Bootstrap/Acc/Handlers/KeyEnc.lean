import Services.Bootstrap.Acc.Handlers.DesignateAlloc
import Services.Bootstrap.Acc.Handlers.HeapKeep
import Services.Bootstrap.Encode.Writer

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
    (hS : S + 72 < 4294967296) (hkp : kp + 8 < 4294967296)
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

/-- **33934 … 58508** (t = 2, after the tag octet): the call `extend(S + 16, kp + 4, 32)` (the key's
    32-octet payload), return address 1570. -/
theorem kb_t2a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S kp : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 72 < 4294967296)
    (hkp : kp + 36 < 18446744073709551616) (m0 : μ.readN S 8 = Num.encodeLE 8 kp)
    (hrf : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 33934 ω μ x 58508 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1570 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat kp ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 16) ∧ ω'[8] = UInt64.ofNat (kp + 4) ∧ ω'[9] = UInt64.ofNat 32 := by
  have r0 := rd8 (by omega) m0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, r0, hrf, bs_58508, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)

/-- **33951 … 58508** (t = 2, after the payload): the `i16` at kp + 2 stored at S + 44 and the call
    `extend(S + 16, S + 44, 2)`, return address 1574. -/
theorem kb_t2b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S kp v : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat kp)
    (hv : v < 65536) (hS : S + 72 < 4294967296) (hkp : kp + 4 < 4294967296)
    (mv : μ.readN (kp + 2) 2 = Num.encodeLE 2 v)
    (hrk : ∀ a, kp + 2 ≤ a → a < kp + 4 → μ.readable a = true)
    (hw : ∀ a, S + 44 ≤ a → a < S + 46 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 33951 ω μ x 58508 ω' μ' x 8 ∧ μ' = μ.writeN (S + 44) (Num.encodeLE 2 v) ∧
      ω'[0] = UInt64.ofNat 1574 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 16) ∧ ω'[8] = UInt64.ofNat (S + 44) ∧ ω'[9] = UInt64.ofNat 2 := by
  have rv : rdN μ (kp + 2) 2 = v := by
    show Num.decodeLE _ = _
    rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hS, hkp, rv, hrk, hw, bs_58508, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · congr 2; split <;> omega
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **34036 … the return** (`jumpInd` at 34068): the `Vec` `{cap, ptr, len}` at S + 16 copied to out
    (the word at S + 8), ω₀, ω₅, ω₆ restored from S + 64, S + 56, S + 48, the frame closed
    (ω₁ := S + 72), and the return to t (the jump table's entry for ret). -/
theorem kb_epi {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S out cap ptr len ret t r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat S)
    (hS : S + 72 < 4294967296) (hout : out + 24 ≤ 4294967296)
    (hod : out + 24 ≤ S + 16 ∨ S + 72 ≤ out)
    (m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 out) (m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 cap)
    (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 ptr) (m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 len)
    (m64 : μ.readN (S + 64) 8 = Num.encodeLE 8 ret) (m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 r5)
    (m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 r6)
    (hcap : cap < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616) (hr5 : r5 < 18446744073709551616)
    (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrf : ∀ a, S ≤ a → a < S + 72 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 34036 ω μ x t ω'
      (((μ.writeN out (Num.encodeLE 8 cap)).writeN (out + 8) (Num.encodeLE 8 ptr)).writeN (out + 16)
        (Num.encodeLE 8 len)) x 12 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 72) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have r8 := rd8 (by omega) m8
  have r16 := rd8 hcap m16
  have r24 := rd8 hptr m24
  have r32 := rd8 hlen m32
  have r64 := rd8 (by omega) m64
  have r56 := rd8 hr5 m56
  have r48 := rd8 hr6 m48
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hout, hod, r8, r16, r24, r32, r64, r56, r48, hret, hjt, hbt, hrf, hwo, hro,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try (congr 1; omega)

/-- `alloc`'s return (40611) to 33886 (ω₀ = 1566). -/
theorem kb_j1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1566) : FreeStepsH p R 40611 ω μ x 33886 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **33886, `alloc` returned null**: the branch to 34070 (`handle_alloc_error`, a trap). -/
theorem kb_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) : FreeStepsH p R 33886 ω μ x 34070 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7]

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Acc.Handlers.HeapKeep in
/-- **The key's `Vec` while it is built** (frame at S, buffer of c octets at ptr in the allocated chunk
    C): the allocator's context; `{c, ptr, bs.length}` at S + 16; the octets bs written at ptr; and,
    against the memory μA after `alloc`, memory kept off the scratch frame [S − 80, S), the `Vec` and the
    tag slot [S + 16, S + 48) and the buffer, with the same page access. -/
structure KVec (code : ByteArray) (pb S0 S1 : Nat) (μA μ : Memory) (s : Picoalloc.State) (C : Chunk)
    (S c ptr : Nat) (bs : List UInt8) : Prop where
  H : HeapCtxC code pb S0 S1 μ s
  hC : C ∈ chunks s
  hCu : C.used = true
  hCp : C.addr + 32 ≤ ptr
  hCe : ptr + c ≤ C.addr + 32 * C.size
  hpb : 65536 ≤ ptr ∧ ptr + c ≤ 2147483648
  hS : 2147483648 + 96 ≤ S ∧ S0 ≤ S - 80 ∧ S + 72 ≤ S1 ∧ S % 8 = 0
  vc : μ.readN (S + 16) 8 = Num.encodeLE 8 c
  vp : μ.readN (S + 24) 8 = Num.encodeLE 8 ptr
  vl : μ.readN (S + 32) 8 = Num.encodeLE 8 bs.length
  dat : μ.readN ptr bs.length = bs
  len : bs.length ≤ c
  keep : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 48 ≤ a) → (a < ptr ∨ ptr + c ≤ a) →
    μ.read a = μA.read a
  wr : ∀ a, μ.writable a = μA.writable a
  rd : ∀ a, μ.readable a = μA.readable a

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Acc.Handlers.HeapKeep in
/-- **One `extend_from_slice` into the key's `Vec`** (58508 → t, the return address ret): the n octets
    at src (in the frame from S + 40, or above it) appended, the invariant kept for `bs ++ ys`. -/
theorem kb_ext {p : ByteArray} {P : Program} [HasCode p P] {code : ByteArray} {pb S0 S1 : Nat}
    {μA : Memory} {st : Picoalloc.State} {C : Chunk} (x : X) (ω : Regs) (μ : Memory) (S c ptr src n ret t : Nat)
    (bs : List UInt8) (K : KVec code pb S0 S1 μA μ st C S c ptr bs)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat (S + 16))
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n) (hroom : bs.length + n ≤ c)
    (hsrc : S + 40 ≤ src ∧ src + n + 16 < 4294967296)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x t ω' μ' x (7 * n + 360) ∧
      KVec code pb S0 S1 μA μ' st C S c ptr (bs ++ μ.readN src n) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → (a < ptr ∨ ptr + c ≤ a) →
        μ'.read a = μ.read a) := by
  obtain ⟨H, hC, hCu, hCp, hCe, hpb, hS, vc, vp, vl, dat, len, keep, wr, rd⟩ := K
  have hst := H.st
  have hS1 := H.hS1
  obtain ⟨ω', μ', run, e0, e1, e5, e6, edat, elen, frm, rd', wr'⟩ :=
    Services.Bootstrap.Encode.Writer.extend_ok (p := p) (P := P) (R := R) x ω μ S (S + 16) src n c ptr
      bs.length ret t ⟨by omega, by omega, hS.2.2.2⟩ h0 h1 h7 h8 h9 hroom (by omega) vc
      (by rw [show S + 16 + 8 = S + 24 by omega]; exact vp)
      (by rw [show S + 16 + 16 = S + 32 by omega]; exact vl) (by omega) (.inr (by omega))
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
      (.inr (by omega)) hret hjt hbt
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega)) hr
      (fun a h1 h2 => writableData H hC hCu ⟨by omega, by omega⟩)
      (fun a h1 h2 => hst a (by omega) (by omega))
  have fr : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → (a < ptr ∨ ptr + c ≤ a) →
      μ'.read a = μ.read a := fun a h0 h1 h2 h3 =>
    frm a h0 h1 (by omega) (by omega)
  refine ⟨ω', μ', run, ⟨?_, hC, hCu, hCp, hCe, hpb, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e0, e1, e5, e6, fr⟩
  · exact keepData H hC (fun a h1 h2 => frm a (by omega) (.inl (by omega)) (by omega) (.inl (by omega)))
      (fun a => by rw [wr'])
  · rw [← vc]; exact Memory.readN_congr fun j hj => fr _ (by omega) (.inr (by omega)) (.inl (by omega)) (.inr (by omega))
  · rw [← vp]; exact Memory.readN_congr fun j hj => fr _ (by omega) (.inr (by omega)) (.inl (by omega)) (.inr (by omega))
  · rw [List.length_append, Memory.length_readN]
    rw [show S + 16 + 16 = S + 32 by omega] at elen; exact elen
  · rw [List.length_append, Memory.length_readN, Services.Bootstrap.Decode.VecU8.readN_split, edat]
    congr 1
    refine (Memory.readN_congr fun j hj => ?_).trans dat
    exact frm _ (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  · rw [List.length_append, Memory.length_readN]; exact hroom
  · intro a h0 h1 h2 h3
    rw [fr a h0 h1 (by omega) h3]; exact keep a h0 h1 h2 h3
  · intro a; rw [wr', wr]
  · intro a; rw [rd', rd]

open Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Acc.Handlers.HeapKeep in
/-- A store of at most four octets at the tag slot S + 44 keeps the invariant. -/
theorem KVec.store44 {code : ByteArray} {pb S0 S1 : Nat} {μA μ : Memory} {st : Picoalloc.State} {C : Chunk}
    {S c ptr : Nat} {bs : List UInt8} (K : KVec code pb S0 S1 μA μ st C S c ptr bs) (l : List UInt8)
    (hl : l.length ≤ 4) : KVec code pb S0 S1 μA (μ.writeN (S + 44) l) st C S c ptr bs := by
  obtain ⟨H, hC, hCu, hCp, hCe, hpb, hS, vc, vp, vl, dat, len, keep, wr, rd⟩ := K
  have hS1 := H.hS1
  have rw1 : ∀ a, a < 4294967296 → (a < S + 44 ∨ S + 48 ≤ a) → (μ.writeN (S + 44) l).read a = μ.read a :=
    fun a h1 h2 => Memory.read_writeN_disjoint _ _ _ _ (by omega) (by unfold two32; omega) (by unfold two32; omega)
  have rwN : ∀ b n, b + n ≤ 4294967296 → (b + n ≤ S + 44 ∨ S + 48 ≤ b) →
      (μ.writeN (S + 44) l).readN b n = μ.readN b n :=
    fun b n h1 h2 => Memory.readN_writeN_disjoint _ _ _ _ _ (by omega) (by unfold two32; omega) (by unfold two32; omega)
  refine ⟨keepHi H (fun a ha => rw1 a (by omega) (.inl (by omega))) (fun a => by simp), hC, hCu, hCp, hCe, hpb, hS,
    by rw [rwN _ _ (by omega) (.inl (by omega))]; exact vc, by rw [rwN _ _ (by omega) (.inl (by omega))]; exact vp,
    by rw [rwN _ _ (by omega) (.inl (by omega))]; exact vl, by rw [rwN _ _ (by omega) (.inl (by omega))]; exact dat,
    len, fun a h0 h1 h2 h3 => by rw [rw1 a h0 (by omega)]; exact keep a h0 h1 h2 h3, fun a => by simp [wr],
    fun a => by simp [rd]⟩

open Picoalloc in
/-- Reads in the frame off the `Vec` and the tag slot, or above it, are μA's. -/
theorem KVec.readN_eq {code : ByteArray} {pb S0 S1 : Nat} {μA μ : Memory} {st : Picoalloc.State} {C : Chunk}
    {S c ptr : Nat} {bs : List UInt8} (K : KVec code pb S0 S1 μA μ st C S c ptr bs) (b n : Nat)
    (hb : S ≤ b) (hbn : b + n ≤ S + 16 ∨ S + 48 ≤ b) (hn : b + n ≤ 4294967296) :
    μ.readN b n = μA.readN b n := by
  have := K.hpb; have := K.hS
  exact Memory.readN_congr fun j hj => K.keep _ (by omega) (.inr (by omega)) (by omega) (.inr (by omega))

/-- **The key's encoding** from the key value at kp (tag t, the `u16` at kp): the tag octet, then for
    t = 1 the four octets at kp + 4, for t = 2 the 32 octets at kp + 4 and the two at kp + 2. -/
def keyEnc (μ : Memory) (kp t : Nat) : List UInt8 :=
  UInt8.ofNat t :: (if t = 1 then μ.readN (kp + 4) 4
    else if t = 2 then μ.readN (kp + 4) 32 ++ μ.readN (kp + 2) 2 else [])

/-- `keyEnc`'s length: 5, 35 or 1 octets. -/
theorem keyEnc_length (μ : Memory) (kp t : Nat) :
    (keyEnc μ kp t).length = if t = 1 then 5 else if t = 2 then 35 else 1 := by
  unfold keyEnc; by_cases h1 : t = 1 <;> by_cases h2 : t = 2 <;> simp [h1, h2]

theorem readN_enc (μ : Memory) (b n : Nat) : μ.readN b n = Num.encodeLE n (Num.decodeLE (μ.readN b n)) := by
  have := PVM.encodeLE_decodeLE (μ.readN b n); rw [Memory.length_readN] at this; exact this.symm

theorem decodeLE_readN_lt (μ : Memory) (b n : Nat) : Num.decodeLE (μ.readN b n) < 256 ^ n := by
  have := PVM.decodeLE_lt (μ.readN b n); rwa [Memory.length_readN] at this

open Picoalloc Services.Bootstrap.Decode.HeapCtx in
/-- **58508 … 34036, the key's octets** (after `kb_vec`, the tag octet at S + 44): the tag octet
    appended, then t's payload (`kb_t1`, or `kb_t2a` and `kb_t2b`), each by `extend_from_slice`: the
    `Vec` holds `keyEnc μA kp t`. -/
theorem kb_body {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} {μA : Memory} {st : Picoalloc.State} {C : Chunk} (x : X) (ω : Regs) (μ : Memory)
    (S c ptr kp t : Nat) (K : KVec code pb S0 S1 μA μ st C S c ptr [])
    (m44 : μ.readN (S + 44) 1 = [UInt8.ofNat t]) (ht : t < 4)
    (h0 : ω[0] = UInt64.ofNat (if t = 2 then 1568 else if t = 1 then 1572 else 1574))
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat (S + 16)) (h8 : ω[8] = UInt64.ofNat (S + 44))
    (h9 : ω[9] = UInt64.ofNat 1) (hroom : (keyEnc μA kp t).length ≤ c)
    (m0 : μA.readN S 8 = Num.encodeLE 8 kp) (hkp : S + 72 ≤ kp ∧ kp + 64 < 4294967296)
    (hrk : ∀ a, kp ≤ a → a < kp + 36 → μA.readable a = true) :
    ∃ ω' μ' n, FreeStepsH p R 58508 ω μ x 34036 ω' μ' x n ∧
      KVec code pb S0 S1 μA μ' st C S c ptr (keyEnc μA kp t) ∧ ω'[1] = UInt64.ofNat S := by
  have hS := K.hS
  have hS1 := K.H.hS1
  have hst := K.H.st
  have hr44 : ∀ a, S + 44 ≤ a → a < S + 44 + 1 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega))
  rw [keyEnc_length] at hroom
  by_cases t1 : t = 1
  · subst t1
    rw [show (if (1 : Nat) = 2 then 1568 else if (1 : Nat) = 1 then 1572 else 1574) = 1572 from rfl] at h0
    simp only [↓reduceIte] at hroom
    obtain ⟨ω1, μ1, run1, K1, -, e1, -, -, -⟩ := kb_ext (R := R) (P := P) x ω μ S c ptr (S + 44) 1 1572 33992 [] K
      h0 h1 h7 h8 h9 (by simp; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_785]) bs_33992 hr44
    have hv := decodeLE_readN_lt μA (kp + 4) 4
    simp only [Nat.reducePow] at hv
    obtain ⟨ω2, μ2, run2, eμ2, f0, f1, -, -, f7, f8, f9⟩ := kb_t1 (R := R) (P := P) x ω1 μ1 S kp _ e1 hv
      (by omega) (by omega) ((K1.readN_eq S 8 (Nat.le_refl _) (.inl (by omega)) (by omega)).trans m0)
      ((K1.readN_eq (kp + 4) 4 (by omega) (.inr (by omega)) (by omega)).trans (readN_enc _ _ _))
      (fun a h1 h2 => by rw [K1.rd]; exact hrk a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (K1.H.st a (by omega) (by omega)))
      (fun a h1 h2 => K1.H.st a (by omega) (by omega))
    have K2 := eμ2 ▸ K1.store44 (Num.encodeLE 4 (Num.decodeLE (μA.readN (kp + 4) 4))) (by simp)
    obtain ⟨ω3, μ3, run3, K3, -, e3, -, -, -⟩ := kb_ext (R := R) (P := P) x ω2 μ2 S c ptr (S + 44) 4 1574 34036 _ K2
      f0 f1 f7 f8 f9 (by simp; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_786]) bs_34036
      (fun a h1 h2 => Memory.readable_of_writable (K2.H.st a (by omega) (by omega)))
    refine ⟨ω3, μ3, _, (run1.trans run2).trans run3, ?_, e3⟩
    have e : ([] ++ μ.readN (S + 44) 1) ++ μ2.readN (S + 44) 4 = keyEnc μA kp 1 := by
      rw [m44, eμ2, Memory.readN_writeN_same _ _ _ _ (by simp) (by unfold two32; omega), ← readN_enc]
      simp [keyEnc]
    exact e ▸ K3
  by_cases t2 : t = 2
  · subst t2
    rw [show (if (2 : Nat) = 2 then 1568 else if (2 : Nat) = 1 then 1572 else 1574) = 1568 from rfl] at h0
    rw [show (if (2 : Nat) = 1 then 5 else if (2 : Nat) = 2 then 35 else 1) = 35 from rfl] at hroom
    obtain ⟨ω1, μ1, run1, K1, -, e1, -, -, -⟩ := kb_ext (R := R) (P := P) x ω μ S c ptr (S + 44) 1 1568 33934 [] K
      h0 h1 h7 h8 h9 (by simp; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_783]) bs_33934 hr44
    obtain ⟨ω2, run2, f0, f1, f5, -, f7, f8, f9⟩ := kb_t2a (R := R) (P := P) x ω1 μ1 S kp e1 (by omega) (by omega)
      ((K1.readN_eq S 8 (Nat.le_refl _) (.inl (by omega)) (by omega)).trans m0)
      (fun a h1 h2 => Memory.readable_of_writable (K1.H.st a (by omega) (by omega)))
    obtain ⟨ω3, μ3, run3, K3, g0, g1, g5, -, -⟩ := kb_ext (R := R) (P := P) x ω2 μ1 S c ptr (kp + 4) 32 1570 33951 _ K1
      f0 f1 f7 f8 f9 (by simp; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_784]) bs_33951
      (fun a h1 h2 => by rw [K1.rd]; exact hrk a (by omega) (by omega))
    have hv := decodeLE_readN_lt μA (kp + 2) 2
    simp only [Nat.reducePow] at hv
    obtain ⟨ω4, μ4, run4, eμ4, i0, i1, -, -, i7, i8, i9⟩ := kb_t2b (R := R) (P := P) x ω3 μ3 S kp _ g1 (g5.trans f5) hv
      (by omega) (by omega) ((K3.readN_eq (kp + 2) 2 (by omega) (.inr (by omega)) (by omega)).trans (readN_enc _ _ _))
      (fun a h1 h2 => by rw [K3.rd]; exact hrk a (by omega) (by omega))
      (fun a h1 h2 => K3.H.st a (by omega) (by omega))
    have K4 := eμ4 ▸ K3.store44 (Num.encodeLE 2 (Num.decodeLE (μA.readN (kp + 2) 2))) (by simp)
    obtain ⟨ω5, μ5, run5, K5, -, e5, -, -, -⟩ := kb_ext (R := R) (P := P) x ω4 μ4 S c ptr (S + 44) 2 1574 34036 _ K4
      i0 i1 i7 i8 i9 (by simp; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_786]) bs_34036
      (fun a h1 h2 => Memory.readable_of_writable (K4.H.st a (by omega) (by omega)))
    refine ⟨ω5, μ5, _, (((run1.trans run2).trans run3).trans run4).trans run5, ?_, e5⟩
    have e : (([] ++ μ.readN (S + 44) 1) ++ μ1.readN (kp + 4) 32) ++ μ4.readN (S + 44) 2 = keyEnc μA kp 2 := by
      rw [m44, eμ4, Memory.readN_writeN_same _ _ _ _ (by simp) (by unfold two32; omega), ← readN_enc,
        K1.readN_eq (kp + 4) 32 (by omega) (.inr (by omega)) (by omega)]
      simp [keyEnc]
    exact e ▸ K5
  -- t = 0, 3: the tag octet only
  simp only [t1, t2, ↓reduceIte] at h0 hroom
  obtain ⟨ω1, μ1, run1, K1, -, e1, -, -, -⟩ := kb_ext (R := R) (P := P) x ω μ S c ptr (S + 44) 1 1574 34036 [] K
    h0 h1 h7 h8 h9 (by simp at hroom ⊢; omega) ⟨by omega, by omega⟩ ⟨by decide, by decide, by decide⟩
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_786]) bs_34036 hr44
  refine ⟨ω1, μ1, _, run1, ?_, e1⟩
  have e : ([] : List UInt8) ++ μ.readN (S + 44) 1 = keyEnc μA kp t := by rw [m44]; simp [keyEnc, t1, t2]
  exact e ▸ K1

/-- `keyEnc` reads only the 36 octets at kp. -/
theorem keyEnc_congr {μ μ' : Memory} {kp : Nat} (t : Nat) (h : ∀ a, kp ≤ a → a < kp + 36 → μ'.read a = μ.read a) :
    keyEnc μ' kp t = keyEnc μ kp t := by
  have e : ∀ b n, kp ≤ b → b + n ≤ kp + 36 → μ'.readN b n = μ.readN b n := fun b n h1 h2 =>
    Memory.readN_congr fun j hj => h _ (by omega) (by omega)
  unfold keyEnc
  rw [e (kp + 4) 4 (by omega) (by omega), e (kp + 4) 32 (by omega) (by omega), e (kp + 2) 2 (by omega) (by omega)]

open Picoalloc Services.Bootstrap.Decode.HeapCtx in
/-- **The invariant after `kb_vec`**: `{c, ptr, 0}` at S + 16 and the tag octet at S + 44, over the
    memory μA after `alloc`, the buffer the new chunk's data. -/
theorem KVec.init {code : ByteArray} {pb S0 S1 : Nat} {μA : Memory} {st : Picoalloc.State} (S c ptr t : Nat)
    (H : HeapCtxC code pb S0 S1 μA st) (hC : (⟨ptr - 32, (c + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks st)
    (hS : 2147483648 + 96 ≤ S ∧ S0 ≤ S - 80 ∧ S + 72 ≤ S1 ∧ S % 8 = 0) :
    KVec code pb S0 S1 μA ((((μA.writeN (S + 16) (Num.encodeLE 8 c)).writeN (S + 24) (Num.encodeLE 8 ptr)).writeN
      (S + 32) (Num.encodeLE 8 0)).writeN (S + 44) [UInt8.ofNat t]) st ⟨ptr - 32, (c + 31) / 32 + 1, true⟩
      S c ptr [] := by
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  obtain ⟨n1, n2, n3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hC rfl
  dsimp only at n1 n2 n3
  have r1 : ∀ a, a < 4294967296 → (a < S + 16 ∨ S + 48 ≤ a) →
      ((((μA.writeN (S + 16) (Num.encodeLE 8 c)).writeN (S + 24) (Num.encodeLE 8 ptr)).writeN
        (S + 32) (Num.encodeLE 8 0)).writeN (S + 44) [UInt8.ofNat t]).read a = μA.read a := fun a h1 h2 => by
    repeat rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
  have e8 : ∀ (m : Memory) b v, (m.writeN b (Num.encodeLE 8 v)).readN b 8 = Num.encodeLE 8 v := fun m b v =>
    Memory.readN_writeN_same _ _ _ _ (by simp) (by unfold two32; omega)
  refine ⟨keepHi H (fun a ha => r1 a (by omega) (.inl (by omega))) (fun a => by simp), hC, rfl, by dsimp only; omega,
    by dsimp only; omega, ⟨by omega, by omega⟩, hS, ?_, ?_, ?_, by simp [Memory.readN], Nat.zero_le _,
    fun a h0 h1 h2 h3 => r1 a h0 h2, fun a => by simp, fun a => by simp⟩
  · repeat rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    exact e8 _ _ _
  · repeat rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    exact e8 _ _ _
  · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    exact e8 _ _ _

end Services.Bootstrap.Acc.Handlers.KeyEnc
