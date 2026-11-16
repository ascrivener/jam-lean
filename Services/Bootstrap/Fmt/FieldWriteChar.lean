import Services.Bootstrap.Fmt.Sink

/-!
# The `String` sink's `write_char` (59743) for an ASCII character, frame-only

`<String as fmt::Write>::write_char` (vtable word 77048 = 2592, at 59743) pushes a character's
UTF-8 octets. `pad_integral` calls it for zero padding (`{:02x}` of a u8 below 16). For a
character c < 128 it is one octet:

- room left (len < cap): the octet goes to ptr + len and the length to len + 1;
- no room (len = cap): `do_reserve_and_handle` (58615) grows the buffer to
  newcap(len + 1, cap) first, as for `write_str` (`Fmt/Reserve.lean`), returning to 59840 (2594).

These are the steps:
- `wc_fast`: 59743 … 59811, room left;
- `wc_pre`: 59743 … 58615, no room;
- `wc_back`: 58848 … 59811, after `finish_grow`'s success;
- `wc_tail`: 59811 … the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 59743 … 59808, room left (len < cap): a 48-octet frame at S = sp − 48 (ω₀, ω₅, ω₆ at S + 40,
    S + 32, S + 24), the octet's address ptr + len in ω₈, the octet count 1 in ω₉. -/
theorem wc_fast {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp W c cap len ptr r0 v5 v6 : Nat) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat c)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hc : c < 128) (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ sp - 48 ∨ sp ≤ W)
    (rc : rdN μ W 8 = cap) (rl : rdN μ (W + 16) 8 = len) (rp : rdN μ (W + 8) 8 = ptr)
    (hl : len < cap) (hcap : cap < 4294967296) (hp : ptr + len < 4294967296)
    (hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59743 ω μ x 59811 ω' μ' x 17 ∧
      ω'[1] = UInt64.ofNat (sp - 48) ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (ptr + len) ∧ ω'[9] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 48 + 40) 8 = r0 ∧ rdN μ' (sp - 48 + 32) 8 = v5 ∧ rdN μ' (sp - 48 + 24) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 48 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hl64 : len < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hc, hW, hWf, rc, rl, rp, hl, hcap, hp, hl64, hWr, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2, h0, h1, h5, h6, h7, h8]

/-- 59743 … 59834, no room (len = cap): the frame at S = sp − 48 also holds 0, 1 and W at S, S + 8,
    S + 16, and `do_reserve_and_handle` (58615) is called with W, len, 1 octet, alignment and size
    1, returning to 59840 (2594); ω₅ = len and ω₆ = c. -/
theorem wc_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp W c len r0 v5 v6 : Nat) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat c)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hc : c < 128) (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ sp - 48 ∨ sp ≤ W)
    (rc : rdN μ W 8 = len) (rl : rdN μ (W + 16) 8 = len) (hl : len < 4294967296)
    (hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59743 ω μ x 58615 ω' μ' x 21 ∧
      ω'[0] = UInt64.ofNat 2594 ∧ ω'[1] = UInt64.ofNat (sp - 48) ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[6] = UInt64.ofNat c ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat len ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat 1 ∧ ω'[11] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 48) 8 = 0 ∧ rdN μ' (sp - 48 + 8) 8 = 1 ∧ rdN μ' (sp - 48 + 16) 8 = W ∧
      rdN μ' (sp - 48 + 40) 8 = r0 ∧ rdN μ' (sp - 48 + 32) 8 = v5 ∧ rdN μ' (sp - 48 + 24) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 48 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hc, hW, hWf, rc, rl, hl, hWr, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_,
      fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_zero, rdN_one, Nat.mod_eq_of_lt hv.1,
      Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2, h0, h1, h5, h6, h7, h8]

/-- 58686 … 58715, then 59840 … 59858: `do_reserve_and_handle` finds `Ok` at D + 8, stores newcap
    m (ω₅) and the buffer q (from D + 16) in the `String` W (from D), restores ω₀, ω₅, ω₆ from
    D + 48, D + 40, D + 32, closes its frame and returns to `write_char` (59840), which reloads W
    from S + 16 (S = D + 56) and goes to its store (59811) with q + len in ω₈. -/
theorem wc_back2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (D W q m c len : Nat) (hD : 65536 ≤ D ∧ D + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat D) (h5 : ω[5] = UInt64.ofNat m) (hq : q + len < 4294967296)
    (hm : m < 4294967296) (hc : c < 128) (hl : len < 4294967296)
    (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ D ∨ D + 104 ≤ W)
    (r8 : rdN μ (D + 8) 8 = 0) (r16 : rdN μ (D + 16) 8 = q) (rW : rdN μ D 8 = W)
    (r0 : rdN μ (D + 48) 8 = 2594) (r5 : rdN μ (D + 40) 8 = len) (r6 : rdN μ (D + 32) 8 = c)
    (s0 : rdN μ (D + 56) 8 = 0) (s8 : rdN μ (D + 64) 8 = 1) (s16 : rdN μ (D + 72) 8 = W)
    (hr : ∀ a, D ≤ a → a < D + 80 → μ.readable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58686 ω μ x 59811 ω' μ' x 19 ∧
      rdN μ' W 8 = m ∧ rdN μ' (W + 8) 8 = q ∧
      (∀ a, a < 4294967296 → (a < W ∨ W + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[1] = UInt64.ofNat (D + 56) ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (q + len) ∧ ω'[9] = UInt64.ofNat 1 := by
  have hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hWw a h1 h2)
  have hq' : q < 4294967296 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hD, hr, hq, hq', hm, hc, hl, hW, hWf, r8, r16, rW, r0, r5, r6, s0, s8, s16, hWw, hWr,
      rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8]

/-- 59811 … 59957: the octet c stored at a (ω₈), the length len + 1 (ω₅ + ω₉) stored at W + 16,
    `Ok` (ω₇ = 0), ω₀, ω₅, ω₆ restored from S + 40, S + 32, S + 24, the frame closed and the return
    to t. -/
theorem wc_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W c len a r0 t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 48 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat len) (h6 : ω[6] = UInt64.ofNat c)
    (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat a) (h9 : ω[9] = UInt64.ofNat 1)
    (hc : c < 128) (hl : len < 4294967296) (ha : a < 4294967296) (hW : W + 24 < 4294967296)
    (haW : a < W + 16 ∨ W + 24 ≤ a) (haS : a < S ∨ S + 48 ≤ a) (hWS : W + 24 ≤ S ∨ S + 48 ≤ W)
    (r0' : rdN μ (S + 40) 8 = r0) (r5 : rdN μ (S + 32) 8 = v5) (r6 : rdN μ (S + 24) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hwa : μ.writable a = true) (hWw : ∀ b, W + 16 ≤ b → b < W + 24 → μ.writable b = true)
    (hr : ∀ b, S ≤ b → b < S + 48 → μ.readable b = true) :
    ∃ ω' μ', FreeStepsH p R 59811 ω μ x t ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 48) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (W + 16) 8 = len + 1 ∧
      (∀ b, b < 4294967296 → b ≠ a → (b < W + 16 ∨ W + 24 ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hra : μ.readable a = true := Memory.readable_of_writable hwa
  have hv5 : v5 < 18446744073709551616 := by rw [← r5]; exact rdN_lt64 μ _
  have hv6 : v6 < 18446744073709551616 := by rw [← r6]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, h8, h9, hS, hc, hl, ha, hW, haW, haS, hWS, r0', r5, r6, hret, hjt, hbt, hwa, hWw, hr, hra,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 hb2 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hv5, Nat.mod_eq_of_lt hv6]

/-- 58848 … 59811: `finish_grow`'s success path, `do_reserve_and_handle`'s store of newcap m and
    the buffer q in the `String` W, and the way back into `write_char`'s store (`rt`, `wc_back2`),
    with finish_grow's frame at F, do_reserve's at F + 40 and write_char's at F + 96. -/
theorem wc_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F W q m c len : Nat) (hF : 65536 ≤ F ∧ F + 144 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat (F + 48)) (h7 : ω[7] = UInt64.ofNat q)
    (h10 : ω[10] = UInt64.ofNat m) (hq : q + len < 4294967296) (hm : m < 4294967296) (hc : c < 128)
    (hl : len < 4294967296) (hW : F + 144 ≤ W ∧ W + 24 < 4294967296)
    (r0 : rdN μ (F + 32) 8 = 2558) (r5 : rdN μ (F + 24) 8 = m) (r6 : rdN μ (F + 16) 8 = 8)
    (rW : rdN μ (F + 40) 8 = W) (r88 : rdN μ (F + 88) 8 = 2594) (r80 : rdN μ (F + 80) 8 = len)
    (r72 : rdN μ (F + 72) 8 = c) (r96 : rdN μ (F + 96) 8 = 0) (r104 : rdN μ (F + 104) 8 = 1)
    (r112 : rdN μ (F + 112) 8 = W)
    (hw : ∀ a, F ≤ a → a < F + 120 → μ.writable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58848 ω μ x 59811 ω' μ' x 31 ∧
      rdN μ' W 8 = m ∧ rdN μ' (W + 8) 8 = q ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 72 ≤ a) → (a < W ∨ W + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[1] = UInt64.ofNat (F + 96) ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (q + len) ∧ ω'[9] = UInt64.ofNat 1 := by
  obtain ⟨ω1, μ1, run1, a1, a5, a6, z0, zq, fr1, rd1, wr1⟩ := rt (p := p) (P := P) (R := R) x ω μ F q m
    ⟨hF.1, by omega⟩ h1 h6 h7 h10 (by omega) hm r0 r5 r6 (fun a h1 h2 => hw a h1 (by omega))
  have k : ∀ a, F + 72 ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a h2 (Or.inr h1)
  obtain ⟨ω2, μ2, run2, b0, bq, fr2, rd2, wr2, e1, e5, e6, e7, e8, e9⟩ := wc_back2 (p := p) (P := P) (R := R)
    x ω1 μ1 (F + 40) W q m c len ⟨by omega, by omega⟩ (by rw [a1]) a5 hq hm hc hl (by omega) (Or.inr (by omega))
    (by rw [show F + 40 + 8 = F + 48 by omega]; exact z0) (by rw [show F + 40 + 16 = F + 56 by omega]; exact zq)
    (by rw [rdN_frame (fun j hj => fr1 _ (by omega) (Or.inl (by omega)))]; exact rW)
    (by rw [show F + 40 + 48 = F + 88 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r88)
    (by rw [show F + 40 + 40 = F + 80 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r80)
    (by rw [show F + 40 + 32 = F + 72 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r72)
    (by rw [show F + 40 + 56 = F + 96 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r96)
    (by rw [show F + 40 + 64 = F + 104 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r104)
    (by rw [show F + 40 + 72 = F + 112 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r112)
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr1]; exact hWw a h1 h2)
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b0, bq,
    fun a h0 h1 h2 => (fr2 a h0 h2).trans (fr1 a h0 h1), fun a => by rw [rd2, rd1],
    fun a => by rw [wr2, wr1], by rw [e1, show F + 40 + 56 = F + 96 by omega], e5, e6, e7, e8, e9⟩

/-- **The grow path of `write_char`**, from 58615 when len = cap (the call `wc_pre` sets up):
    `do_reserve_and_handle` and `finish_grow` get newcap = max(len + 1, 8, 2 · cap) octets from the
    allocator, store newcap and the new buffer in the `String` W and come back to 59811 (the
    store), with S, len, c, W, buffer + len and 1 in ω₁, ω₅, ω₆, ω₇, ω₈, ω₉. The `String` holds the
    new capacity, the context is kept, and the frame `Keeps` from S up, but for the capacity and
    buffer at W … W + 16. Or the allocator fails (`Exhausts`). -/
theorem wc_reserve {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (S W c len cap : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str s₀ s μ W cap len) (hlt : cap < len + 1)
    (h0 : ω[0] = UInt64.ofNat 2594) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat len)
    (h6 : ω[6] = UInt64.ofNat c) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat len)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat 1) (h11 : ω[11] = UInt64.ofNat 1)
    (hc : c < 128) (hn : len + 1 < 134217728)
    (z0 : rdN μ S 8 = 0) (z8 : rdN μ (S + 8) 8 = 1) (z16 : rdN μ (S + 16) 8 = W)
    (hS : S0 + 416 ≤ S ∧ S % 8 = 0 ∧ 2147484064 ≤ S) (hW : S + 48 ≤ W ∧ W + 24 ≤ S1) :
    (∃ ω' μ' x' s', FreeStepsH p R 58615 ω μ x 59811 ω' μ' x' (2 * (newcap (len + 1) cap - cap) + 1500) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (rdN μ' (W + 8) 8 + len) ∧ ω'[9] = UInt64.ofNat 1 ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W (newcap (len + 1) cap) len ∧
      Keeps pb S (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ' s') ∨
    Exhausts p R pb 58615 ω μ x (2 * (newcap (len + 1) cap - cap) + 1500) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hm := newcap_ge (len + 1) cap
  have hml := newcap_lt (len + 1) cap (by omega) (by have := hs.lt; omega)
  have hm2 : newcap (len + 1) cap < 268435456 := by
    have : newcap (len + 1) cap ≤ max (len + 1) 8 ∨ newcap (len + 1) cap ≤ 2 * cap := by
      unfold newcap; simp only [Nat.max_def]; split <;> split <;> omega
    omega
  generalize hmd : newcap (len + 1) cap = m at hm hml hm2 ⊢
  obtain ⟨hm1, hm8, hm3⟩ := hm
  have hcap := hs.lt
  have hle := hs.le
  have hst := stack_wr H (lo := S0) (hi := S1) (Nat.le_refl _) (Nat.le_refl _)
  -- the String's buffer address
  generalize hpd : rdN μ (W + 8) 8 = ptr
  have hp64 : ptr < 18446744073709551616 := by rw [← hpd]; exact rdN_lt _ _ _
  have k1 : ∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ.read a = μ.read a := fun _ _ _ => rfl
  have w1 : ∀ a, μ.writable a = μ.writable a := fun _ => rfl
  -- 58615 … 58667
  obtain ⟨ω2, μ2, run2, b1, b6, b8, b9, b10, b11, b12, s48, s40, s32, s0, k2, rd2, wr2⟩ :=
    rs2a (p := p) (P := P) (R := R) x ω μ (S - 56) W 1 len cap ptr 2594 len c ⟨by omega, by omega⟩
    h0 (by rw [h1]; congr 1; omega) h5 h6 h7 h8 h9 h10 h11
    ⟨by omega, by omega, by omega, hp64⟩ ⟨by omega, by omega, by omega⟩ (Or.inr (by omega))
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))]; exact hs.rc)
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))]; exact hpd)
    (fun a h1 h2 => by rw [Memory.readable_of_writable (by rw [w1]; exact hst a (by omega) (by omega))])
    (fun a h1 h2 => by rw [w1]; exact hst a (by omega) (by omega))
  -- 58667 … 58759
  obtain ⟨ω3, run3, c1, c6, c8, c9, c10, c11, c12⟩ := rs2b (p := p) (P := P) (R := R) x ω2 μ2 (S - 96) len 1 cap
    ⟨by omega, by omega⟩ (by rw [b1]; congr 1; omega) b6 b8 (by rw [b10]) b12 ⟨by omega, by omega⟩
    (fun a h1 h2 => by rw [wr2, w1]; exact hst a (by omega) (by omega))
  rw [hmd] at run3 c10
  generalize hM3 : ((μ2.writeN (S - 96 + 32) (Num.encodeLE 8 2558)).writeN (S - 96 + 24)
    (Num.encodeLE 8 m)).writeN (S - 96 + 16) (Num.encodeLE 8 8) = μ3 at run3
  have k3 : ∀ a, a < 4294967296 → (a < S - 96 + 16 ∨ S - 96 + 40 ≤ a) → μ3.read a = μ2.read a := fun a ha0 ha1 => by
    rw [← hM3]
    simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
  have w3 : ∀ a, μ3.writable a = μ2.writable a := fun a => by
    rw [← hM3]; simp only [Memory.writable_writeN]
  -- finish_grow's frame F = S − 96, do_reserve's D = S − 56
  have hF : 65536 ≤ S - 96 ∧ S - 96 + 96 < 4294967296 := ⟨by omega, by omega⟩
  have r58 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S ≤ a) → μ3.read a = μ.read a := fun a ha0 ha1 => by
    rw [k3 a ha0 (by omega), k2 a ha0 (by omega)]
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [w3, wr2, w1]
  -- what μ3 holds: finish_grow's saved words, do_reserve's frame and src at S
  have q32 : rdN μ3 (S - 96 + 32) 8 = 2558 := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]
  have q24 : rdN μ3 (S - 96 + 24) 8 = m := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]; omega
  have q16 : rdN μ3 (S - 96 + 16) 8 = 8 := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]
  have kk : ∀ a, S - 96 + 40 ≤ a → a < S → μ3.read a = μ2.read a := fun a h1 h2 => k3 a (by omega) (Or.inr h1)
  have q40 : rdN μ3 (S - 96 + 40) 8 = W := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 40 = S - 56 by omega]
    exact rdN_of_readN s0 (by omega)
  have q88 : rdN μ3 (S - 96 + 88) 8 = 2594 := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 88 = S - 56 + 48 by omega]
    exact rdN_of_readN s48 (by omega)
  have q80 : rdN μ3 (S - 96 + 80) 8 = len := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 80 = S - 56 + 40 by omega]
    exact rdN_of_readN s40 (by omega)
  have q72 : rdN μ3 (S - 96 + 72) 8 = c := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 72 = S - 56 + 32 by omega]
    exact rdN_of_readN s32 (by omega)
  have q96 : rdN μ3 (S - 96 + 96) 8 = 0 := by
    rw [rdN_frame (fun j hj => r58 _ (by omega) (Or.inr (by omega))), show S - 96 + 96 = S by omega]; exact z0
  have q104 : rdN μ3 (S - 96 + 104) 8 = 1 := by
    rw [rdN_frame (fun j hj => r58 _ (by omega) (Or.inr (by omega))), show S - 96 + 104 = S + 8 by omega]; exact z8
  have q112 : rdN μ3 (S - 96 + 112) 8 = W := by
    rw [rdN_frame (fun j hj => r58 _ (by omega) (Or.inr (by omega))), show S - 96 + 112 = S + 16 by omega]; exact z16
  have qlen : rdN μ3 (W + 16) 8 = len := by
    rw [rdN_frame (fun j hj => r58 _ (by omega) (Or.inr (by omega)))]; exact hs.rl
  -- the common end: from finish_grow's success (58848) to 59811
  have fin : ∀ (μ5 : Memory) (x5 : X) (s' : State) (ω6 : Regs) (q N : Nat),
      FreeStepsH p R 58615 ω μ x 58848 ω6 μ5 x5 N → N ≤ 2 * (m - cap) + 1468 →
      ω6[1] = UInt64.ofNat (S - 96) → ω6[6] = UInt64.ofNat (S - 96 + 48) → ω6[7] = UInt64.ofNat q →
      ω6[10] = UInt64.ofNat m → 0 < q → q < 2147483648 →
      HeapCtx env pb S0 S1 μ5 s' → s'.base = s.base →
      Keeps pb S (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ5 s' →
      (∀ a, S - 96 + 16 ≤ a → a < 4294967296 → μ5.read a = μ3.read a) →
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = q ∧ d.size = (m + 31) / 32 + 1 ∧
        ∀ e ∈ chunks s₀, e.used = true → e.addr ≠ d.addr) →
      (∃ ω' μ' x' s', FreeStepsH p R 58615 ω μ x 59811 ω' μ' x' (2 * (m - cap) + 1500) ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat len ∧ ω'[6] = UInt64.ofNat c ∧
        ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (rdN μ' (W + 8) 8 + len) ∧ ω'[9] = UInt64.ofNat 1 ∧
        HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W m len ∧
        Keeps pb S (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ' s') := by
    intro μ5 x5 s' ω6 q N run hN g1 g6 g7 g10 hq0 hq1 H5 hb5 K5 hk5 hbuf
    have rr : ∀ {a : Nat} {v : Nat}, S - 96 + 16 ≤ a → a + 8 ≤ 4294967296 → rdN μ3 a 8 = v →
        rdN μ5 a 8 = v := fun h1 h2 h3 => by
      rw [rdN_frame (fun j hj => hk5 _ (by omega) (by omega))]; exact h3
    obtain ⟨ω7, μ7, run7, eW, eq, fr7, rd7, wr7, e1, e5, e6, e7, e8, e9⟩ := wc_back (p := p) (P := P) (R := R)
      x5 ω6 μ5 (S - 96) W q m c len ⟨by omega, by omega⟩ g1 g6 g7 g10 (by omega) (by omega) hc (by omega)
      ⟨by omega, by omega⟩ (rr (by omega) (by omega) q32) (rr (by omega) (by omega) q24)
      (rr (by omega) (by omega) q16) (rr (by omega) (by omega) q40) (rr (by omega) (by omega) q88)
      (rr (by omega) (by omega) q80) (rr (by omega) (by omega) q72) (rr (by omega) (by omega) q96)
      (rr (by omega) (by omega) q104) (rr (by omega) (by omega) q112)
      (fun a h1 h2 => H5.st a (by omega) (by omega))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
    have H7 : HeapCtx env pb S0 S1 μ7 s' := ctx_hi H5 (fun a ha => fr7 a (by omega) (Or.inl (by omega))
      (Or.inl (by omega))) wr7
    obtain ⟨d, hd, hdu, hdq, hds, hdf⟩ := hbuf
    have K7 : Keeps pb S (fun a => W ≤ a ∧ a < W + 16) s₀ μ5 μ7 s' :=
      Keeps.of_frame (Z := fun a => (S - 96 + 48 ≤ a ∧ a < S - 96 + 72) ∨ (W ≤ a ∧ a < W + 16)) K5.used
        (fun a ha hz => fr7 a ha (by omega) (by omega)) rd7 wr7
        (fun a hz => H5.st a (by omega) (by omega)) (fun a hz h => by omega)
        (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H5.wf (K5.used c hc hu)
          have := H5.hbT
          unfold InData at ha; omega)
    have el : rdN μ7 (W + 16) 8 = len := by
      rw [rdN_frame (fun j hj => fr7 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]
      exact rr (by omega) (by omega) qlen
    refine ⟨ω7, μ7, x5, s', (run.trans run7).mono (by omega), by rw [e1, show S - 96 + 96 = S by omega],
      e5, e6, e7, by rw [eq]; exact e8, e9, H7, hb5, ⟨eW, el, by omega, by omega, K5.used,
        Or.inr ⟨d, hd, hdu, by rw [eq]; exact hdq, hds, hdf⟩⟩, ?_⟩
    have := K5.trans' K7
    rwa [Nat.max_self] at this
  -- the frame of the steps before the allocator: only S − 96 … S + 8 written
  have Kpre : ∀ μ4 : Memory, (∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a) →
      (∀ a, μ4.readable a = μ.readable a) → (∀ a, μ4.writable a = μ.writable a) →
      Keeps pb S (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ4 s := fun μ4 h4 rd4 wr4 =>
    Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base
      (fun a ha hz => by rw [h4 a ha (by omega), r58 a ha (by omega)]) rd4 wr4
      (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
      (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hs.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have rd3 : ∀ a, μ3.readable a = μ.readable a := fun a => by
    rw [← hM3]; simp only [Memory.readable_writeN]; rw [rd2]
  by_cases hc0 : cap = 0
  · -- no buffer yet: `alloc`
    subst hc0
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8⟩ := rs3a (p := p) (P := P) (R := R) x ω3 μ3 (S - 96) m hF
      c1 (by rw [c8, b8]) c10 ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
    generalize hM4 : (μ3.writeN (S - 96) (Num.encodeLE 8 1)).writeN (S - 96 + 8) (Num.encodeLE 8 m) = μ4 at run4
    have k4 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a := fun a ha0 ha1 => by
      rw [← hM4]; simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
    have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by
      rw [← hM4]; simp only [Memory.readable_writeN]; exact rd3 a
    have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by
      rw [← hM4]; simp only [Memory.writable_writeN]; exact wr3 a
    have H4 : HeapCtx env pb S0 S1 μ4 s := ctx_hi H (fun a ha => by
      rw [k4 a (by omega) (Or.inl (by omega)), r58 a (by omega) (Or.inl (by omega))]) (fun a => wr4 a)
    have K4 := Kpre μ4 k4 rd4 wr4
    rcases HA ω4 μ4 x s (S - 96) m 1 H4 (d1.trans c1) d7 d8 (Nat.le_refl _) (by omega) (by omega) (by omega)
      (by omega) (by omega) with ⟨q, s', ω5, μ5, x5, run5, H5, hb5, K5, hnew, hfresh, hq32, e7, e0, e1, e5, e6⟩ |
      ⟨ω5, μ5, x5, run5, e7, hb, hfail⟩
    · have hq := chunk_bounds H5.wf hnew
      have hbT := H.hbT
      simp only at hq
      obtain ⟨ω6, run6, f1, f5, f6, f7, f10⟩ := rt_a (p := p) (P := P) (R := R) x5 ω5 μ5 (S - 96) q m hF
        (e1.trans (d1.trans c1)) e7 ⟨by omega, by omega⟩
        (by rw [rdN_frame (fun j hj => K5.hi _ (by omega) (by omega) id), ← hM4]
            simp (disch := pvm_arith) only [rdN_writeN_same8]; omega)
        (fun a h1 h2 => by
          rw [Memory.readable_of_writable (H5.st a (by omega) (by omega))])
      have rt0 := ret_alloc (p := p) (P := P) (R := R) x5 ω5 μ5 (e0.trans d0)
      exact Or.inl (fin μ5 x5 s' ω6 q _ (((((run2.trans run3).trans run4).trans run5).trans rt0).trans run6)
        (by omega) (f1.trans (e1.trans (d1.trans c1))) (f6.trans (e6.trans (d6.trans c6))) (f7.trans e7)
        (f10) (by omega) (by omega) H5 (by rw [hb5])
        (by have := K4.trans' ((K5.rebase hs.base).mono (sp' := S) (by omega) (fun _ h => h.elim))
            rwa [Nat.max_self] at this)
        (fun a h1 h2 => by rw [K5.hi a (by omega) h2 id, k4 a h2 (by omega)])
        ⟨_, hnew, rfl, by simp only; omega, rfl, fun e he hu => by
          simp only; exact hfresh e (hs.base e he hu) hu⟩)
    · exact Or.inr ((Exhausts.pre ((run2.trans run3).trans run4)
        (⟨ω5, μ5, x5, 40611, run5, e7, Or.inl ⟨rfl, s, hb, _, hfail⟩⟩ : Exhausts p R pb 40494 ω4 μ4 x 540)).mono
        (by omega))
  · -- a buffer of cap > 0 octets: `realloc`
    obtain ⟨c, hc, hcu, hca, hcs, hcf⟩ := hs.buf.resolve_left hc0
    rw [hpd] at hca
    have hcb := chunk_bounds H.wf hc
    have hbT := H.hbT
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9, d10⟩ := rs3r (p := p) (P := P) (R := R) x ω3 μ3 (S - 96) cap ptr m
      hF c1 (by rw [c8, b8]) (by rw [c9, b9]) c10 (by rw [c11, b11]) ⟨by omega, by omega⟩ (by omega) (by omega)
      (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
    generalize hM4 : (μ3.writeN (S - 96) (Num.encodeLE 8 1)).writeN (S - 96 + 8) (Num.encodeLE 8 m) = μ4 at run4
    have k4 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a := fun a ha0 ha1 => by
      rw [← hM4]; simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
    have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by
      rw [← hM4]; simp only [Memory.readable_writeN]; exact rd3 a
    have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by
      rw [← hM4]; simp only [Memory.writable_writeN]; exact wr3 a
    have H4 : HeapCtx env pb S0 S1 μ4 s := ctx_hi H (fun a ha => by
      rw [k4 a (by omega) (Or.inl (by omega)), r58 a (by omega) (Or.inl (by omega))]) (fun a => wr4 a)
    have K4 := Kpre μ4 k4 rd4 wr4
    rcases HR ω4 μ4 x s (S - 96) ptr 1 m c H4 hba hc hcu hca (by omega) (by omega) (d1.trans c1) d7 d9 d10
      (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) (by omega) with
      ⟨r, s', ω5, μ5, x5, run5, H5, hb5, O5, oth, ⟨d, hd, hdu, hdr, hds, hdf⟩, e7, e0, e1, e5, e6⟩ |
      ⟨ω5, μ5, x5, run5, e7, hb, hfail⟩
    · have hq := chunk_bounds H5.wf hd
      rw [hb5] at hq
      obtain ⟨ω6, run6, f1, f5, f6, f7, f10⟩ := rt_r (p := p) (P := P) (R := R) x5 ω5 μ5 (S - 96) r m hF
        (e1.trans (d1.trans c1)) e7 ⟨by omega, by omega⟩
        (by rw [rdN_frame (fun j hj => O5.hi _ (by omega) (by omega) id), ← hM4]
            simp (disch := pvm_arith) only [rdN_writeN_same8]; omega)
        (fun a h1 h2 => by
          rw [Memory.readable_of_writable (H5.st a (by omega) (by omega))])
      have rt0 := ret_realloc (p := p) (P := P) (R := R) x5 ω5 μ5 (e0.trans d0)
      have K5 : Keeps pb (S - 96) (fun _ => False) s₀ μ4 μ5 s' :=
        ⟨O5, fun e he hu => (oth e (hs.base e he hu) hu (fun h => hcf e he hu (by rw [h]))).1,
          fun e he hu => (oth e (hs.base e he hu) hu (fun h => hcf e he hu (by rw [h]))).2⟩
      exact Or.inl (fin μ5 x5 s' ω6 r _ (((((run2.trans run3).trans run4).trans run5).trans rt0).trans run6)
        (by rw [hcs]; omega) (f1.trans (e1.trans (d1.trans c1))) (f6.trans (e6.trans (d6.trans c6))) (f7.trans e7)
        (f10) (by omega) (by omega) H5 (by rw [hb5])
        (by have := K4.trans' (K5.mono (sp' := S) (by omega) (fun _ h => h.elim))
            rwa [Nat.max_self] at this)
        (fun a h1 h2 => by rw [O5.hi a (by omega) h2 id, k4 a h2 (by omega)])
        ⟨d, hd, hdu, hdr, hds, fun e he hu => by
          rcases hdf with h | h
          · rw [h]; exact hcf e he hu
          · exact h e (hs.base e he hu) hu⟩)
    · exact Or.inr ((Exhausts.pre ((run2.trans run3).trans run4)
        (⟨ω5, μ5, x5, 40821, run5, e7, Or.inr ⟨rfl, s, hb, _, _, _, hfail⟩⟩ :
          Exhausts p R pb 40701 ω4 μ4 x (64 * (c.size - 1) + 1300))).mono (by rw [hcs]; omega))


/-- **`write_char` of an ASCII character into a `String`, frame-only** (59743): called with the
    `String` W (ω₇) and a character c < 128 (ω₈), and a return address ω₀ that `djump` resolves to
    t, it either:
    - returns `Ok` (ω₇ = 0) to t, ω₀, ω₁, ω₅, ω₆ as they were, the `String` one octet longer (the
      octet unspecified here), its capacity cap' = cap or newcap(len + 1, cap), within
      2(cap' − cap) + 1600 steps, the context kept and, from sp up, only W … W + 24 changed; or
    - reaches a failed allocator call. -/
theorem write_char_ascii {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp W c cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str s₀ s μ W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat c)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 464 ≤ sp ∧ sp % 8 = 0 ∧ 2147484112 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hc : c < 128) (hn : len + 1 < 134217728) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 59743 ω μ x t ω' μ' x' (2 * (cap' - cap) + 1600) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W cap' (len + 1) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + 1))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 59743 ω μ x (1073741824 + 1600) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have hle := hs.le
  have hbT := H.hbT
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  have hr0 : ret < 18446744073709551616 := by omega
  -- the frame below sp, written by write_char only
  have Kf : ∀ μ1 : Memory, (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → μ1.read a = μ.read a) →
      (∀ a, μ1.readable a = μ.readable a) → (∀ a, μ1.writable a = μ.writable a) →
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s := fun μ1 fr1 rd1 wr1 =>
    Keeps.of_frame (Z := fun a => sp - 48 ≤ a ∧ a < sp) hs.base
      (fun a ha hz => fr1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun d hd hu a ha => by
        have := chunk_bounds H.wf (hs.base d hd hu)
        unfold InData at ha; omega)
  by_cases hb : len < cap
  · -- room left
    obtain ⟨d, hd, hdu, hda, hds, hdf⟩ := hs.buf.resolve_left (by omega)
    have hdb := chunk_bounds H.wf hd
    have := H.hb0
    generalize hpd : rdN μ (W + 8) 8 = ptr at hda
    obtain ⟨ω1, μ1, run1, a1, a5, a6, a7, a8, a9, sv0, sv5, sv6, fr1, rd1, wr1⟩ := wc_fast (p := p) (P := P)
      (R := R) x ω μ sp W c cap len ptr ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 ⟨hr0, hv.1, hv.2⟩ hc
      (by omega) (Or.inr hW.1) hs.rc hs.rl hpd hb (by omega) (by omega) hWr
      (fun a h1 h2 => hst a (by omega) (by omega))
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
    have hwb : μ1.writable (ptr + len) = true :=
      Decode.VecU8.heap_writable H1 hd hdu (by unfold InData; omega)
    obtain ⟨ω2, μ2, run2, c0, c1, c5, c6, c7, cl, fr2, rd2, wr2⟩ := wc_tail (p := p) (P := P) (R := R) x ω1 μ1
      (sp - 48) W c len (ptr + len) ret t v5 v6 ⟨by omega, by omega⟩ a1 a5 a6 a7 a8 a9 hc (by omega) (by omega)
      (by omega) (by omega) (by omega) (Or.inr (by omega)) sv0 sv5 sv6 hret hjt hbt hwb
      (fun a h1 h2 => H1.st a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (H1.st a (by omega) (by omega)))
    have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.VecU8.ctx_congr_data H1 hd
      (fun a ha h => fr2 a (by omega) (by omega) (by omega)) wr2
    have K2 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ1 μ2 s :=
      Keeps.of_frame (Z := fun a => (sp - 48 ≤ a ∧ a < sp) ∨ a = ptr + len ∨ (W + 16 ≤ a ∧ a < W + 24)) hs.base
        (fun a ha hz => fr2 a ha (by omega) (by omega)) rd2 wr2
        (fun a hz => by
          rcases hz with h | h | h
          · exact H1.st a (by omega) (by omega)
          · rw [h]; exact hwb
          · exact H1.st a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun e he hu a ha => by
          have he' := hs.base e he hu
          have := chunk_bounds H.wf he'
          have hne : e ≠ d := fun h => hdf e he hu (by rw [h])
          have := Decode.VecU8.data_disj H.wf he' hd hne ha
          unfold InData at ha; omega)
    have K1 := Kf μ1 fr1 rd1 wr1
    refine Or.inl ⟨ω2, μ2, x, s, cap, (run1.trans run2).mono (by omega), H2, rfl, ?_, Nat.le_refl _, by omega,
      ?_, c0, by rw [c1, show sp - 48 + 48 = sp by omega], c5, c6, c7⟩
    · have kW : ∀ j, j < 16 → μ2.read (W + j) = μ.read (W + j) := fun j hj => by
        rw [fr2 _ (by omega) (by omega) (by omega), fr1 _ (by omega) (Or.inr (by omega))]
      exact hs.update kW cl (by omega)
    · have := K1.trans' K2
      rwa [Nat.max_self] at this
  · -- no room: grow
    have hlc : cap = len := by omega
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, z0, z8, z16, sv0, sv5, sv6, fr1, rd1, wr1⟩ :=
      wc_pre (p := p) (P := P) (R := R) x ω μ sp W c len ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      ⟨hr0, hv.1, hv.2⟩ hc (by omega) (Or.inr hW.1) (by rw [← hlc]; exact hs.rc) hs.rl (by omega) hWr
      (fun a h1 h2 => hst a (by omega) (by omega))
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
    have kW : ∀ j, j < 24 → μ1.read (W + j) = μ.read (W + j) := fun j hj => fr1 _ (by omega) (Or.inr (by omega))
    have hs1 : Str s₀ s μ1 W cap len := hs.update (fun j hj => kW j (by omega))
      ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hs.rl) hle
    have K1 := Kf μ1 fr1 rd1 wr1
    rcases wc_reserve (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s (sp - 48) W c len cap H1 hba hs1
      (by omega) a0 a1 a5 a6 a7 a8 a9 a10 a11 hc hn z0 z8 z16 ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ with
      ⟨ω2, μ2, x2, s', run2, b1, b5, b6, b7, b8, b9, H2, hb2, hs2, K2⟩ | hx
    · generalize hmd : newcap (len + 1) cap = m at run2 hs2
      have hm := newcap_ge (len + 1) cap
      have hmx : newcap (len + 1) cap ≤ max cap (max 8 (2 * (len + 1))) := by
        unfold newcap; simp only [Nat.max_def]; split <;> split <;> split <;> split <;> omega
      rw [hmd] at hm hmx
      obtain ⟨d, hd, hdu, hda, hds, hdf⟩ := hs2.buf.resolve_left (by omega)
      have hdb := chunk_bounds H2.wf hd
      have := H.hb0
      rw [hb2] at hdb
      generalize hpd : rdN μ2 (W + 8) 8 = ptr at hda b8
      have hwb : μ2.writable (ptr + len) = true :=
        Decode.VecU8.heap_writable H2 hd hdu (by unfold InData; omega)
      have hk2 : ∀ a, sp - 48 ≤ a → a < 4294967296 → ¬ (W ≤ a ∧ a < W + 16) → μ2.read a = μ1.read a :=
        fun a h1 h2 h3 => K2.hi a h1 h2 h3
      obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, cl, fr3, rd3, wr3⟩ := wc_tail (p := p) (P := P) (R := R) x2 ω2 μ2
        (sp - 48) W c len (ptr + len) ret t v5 v6 ⟨by omega, by omega⟩ b1 b5 b6 b7 b8 b9 hc (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inr (by omega))
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv0)
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv5)
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv6)
        hret hjt hbt hwb
        (fun a h1 h2 => H2.st a (by omega) (by omega))
        (fun a h1 h2 => Memory.readable_of_writable (H2.st a (by omega) (by omega)))
      have H3 : HeapCtx env pb S0 S1 μ3 s' := Decode.VecU8.ctx_congr_data H2 hd
        (fun a ha h => fr3 a (by omega) (by omega) (by omega)) wr3
      have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ2 μ3 s' :=
        Keeps.of_frame (Z := fun a => (sp - 48 ≤ a ∧ a < sp) ∨ a = ptr + len ∨ (W + 16 ≤ a ∧ a < W + 24)) K2.used
          (fun a ha hz => fr3 a ha (by omega) (by omega)) rd3 wr3
          (fun a hz => by
            rcases hz with h | h | h
            · exact H2.st a (by omega) (by omega)
            · rw [h]; exact hwb
            · exact H2.st a (by omega) (by omega))
          (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
          (fun e he hu a ha => by
            have he' := K2.used e he hu
            have := chunk_bounds H2.wf he'
            have hne : e ≠ d := fun h => hdf e he hu (by rw [h])
            have := Decode.VecU8.data_disj H2.wf he' hd hne ha
            unfold InData at ha; omega)
      refine Or.inl ⟨ω3, μ3, x2, s', m, ((run1.trans run2).trans run3).mono (by omega), H3, hb2,
        ?_, by omega, hmx, ?_, c0, by rw [c1, show sp - 48 + 48 = sp by omega], c5, c6, c7⟩
      · refine hs2.update (fun j hj => fr3 _ (by omega) (by omega) (by omega)) ?_ (by omega)
        rw [cl]
      · have K12 := K1.trans' (K2.mono (sp' := sp) (by omega) (fun a h => ⟨h.1, by omega⟩))
        have K123 := K12.trans' K3
        rwa [Nat.max_self, Nat.max_self] at K123
    · have : newcap (len + 1) cap - cap < 536870912 := by
        unfold newcap; simp only [Nat.max_def]; split <;> split <;> omega
      exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
