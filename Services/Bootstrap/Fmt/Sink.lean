import Services.Bootstrap.Fmt.Frame
import Services.Bootstrap.Fmt.WriteStr
import Services.Bootstrap.Fmt.Reserve
import Services.Bootstrap.Fmt.Memcpy
import Services.Bootstrap.Decode.VecU8Heap

/-!
# The `String` sink: `write_str`, frame-only
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000

variable {X : Type} {R : HostRel X}

/-- 59989 … 60028, n > 0: the copy into the buffer and the return. From the `String` W's buffer ptr
    and length len (ω₉), `memcpy` puts the n octets at src at ptr + len, then the length len + n goes
    to W + 16 and `write_str` returns `Ok` to its caller. Memory changes only in S − 48 … S + 8 (the
    frames), the n octets at ptr + len and W + 16 … W + 24. -/
theorem ws_copytail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W n len ptr src ret t v5 v6 : Nat) (hS : 65536 + 48 ≤ S ∧ S + 32 < 4294967296 ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat len) (hn : 0 < n)
    (hp : rdN μ (W + 8) 8 = ptr) (hb : 65536 ≤ ptr ∧ ptr + len + n + 16 < 4294967296)
    (hs : 65536 ≤ src ∧ src + n + 16 < 4294967296)
    (hW : S + 32 ≤ W ∧ W + 24 < 4294967296)
    (hdj : ptr + len + n + 24 ≤ src ∨ src + n + 24 ≤ ptr + len)
    (hfd : ptr + len + n ≤ S - 48) (hfs : S + 8 ≤ src ∨ src + n + 16 ≤ S - 48)
    (hsW : src + n ≤ W ∨ W + 24 ≤ src)
    (r0 : rdN μ (S + 24) 8 = ret) (r5 : rdN μ (S + 16) 8 = v5) (r6 : rdN μ (S + 8) 8 = v6)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hwb : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ.writable a = true)
    (hws : ∀ a, S - 48 ≤ a → a < S + 32 → μ.writable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59989 ω μ x t ω' μ' x (7 * n + 340) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 32) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (W + 16) 8 = n + len ∧
      (∀ a, a < 4294967296 → (a < S - 48 ∨ S + 8 ≤ a) → (a < ptr + len ∨ ptr + len + n ≤ a) →
        (a < W + 16 ∨ W + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs : ∀ a, S - 48 ≤ a → a < S + 32 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hws a h1 h2)
  -- the copy's set-up
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := ws_copy (p := p) (P := P) (R := R) x ω μ S W n len ptr
    ⟨by omega, by omega⟩ h1 h5 h6 h9 (by omega) (by omega) hp (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (hWw a h1 h2)) (fun a h1 h2 => hws a (by omega) (by omega))
  generalize hM1 : μ.writeN S (Num.encodeLE 8 len) = μ1 at run1
  have m1 : ∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ1.read a = μ.read a := fun a ha0 ha1 => by
    rw [← hM1, Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
      (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
  have w1 : ∀ a, μ1.writable a = μ.writable a := fun a => by rw [← hM1, Memory.writable_writeN]
  have d1 : ∀ a, μ1.readable a = μ.readable a := fun a => by rw [← hM1, Memory.readable_writeN]
  -- `memcpy`
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, fr2, rd2, wr2⟩ := memcpy_frame (p := p) (P := P) (R := R) x ω1 μ1
    2598 60005 S (ptr + len) src n a0 (a1.trans h1) a7 (a8.trans h8) a9 (by decide) jte_1298 bs_60005
    ⟨by omega, by omega, hS.2.2⟩ hs (by omega) (by omega) (Or.inr hfd) hfs
    (fun a h1 h2 => by rw [d1]; exact hr a h1 h2) (fun a h1 h2 => by rw [w1]; exact hwb a h1 h2)
    (fun a h1 h2 => by rw [w1]; exact hws a h1 (by omega))
  -- the length reloaded and stored, the return
  have rl2 : rdN μ2 S 8 = len := by
    rw [rdN_frame (fun j hj => fr2 _ (by omega) (by omega) (Or.inr (by omega)))]
    rw [← hM1]; unfold rdN
    rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨ω3, run3, c9, c1, c5, c6⟩ := ws_tail (p := p) (P := P) (R := R) x ω2 μ2 S len ⟨by omega, by omega⟩
    (b1.trans (a1.trans h1)) rl2 (fun a h1 h2 => by rw [rd2, d1]; exact hrs a (by omega) (by omega))
  have keep2 : ∀ a, S + 8 ≤ a → a < S + 32 → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 _ (by omega) (by omega) (Or.inr (by omega)), m1 a (by omega) (Or.inr h1)]
  obtain ⟨ω4, run4, e0, e1, e5, e6, e7⟩ := ws_fin (p := p) (P := P) (R := R) x ω3 μ2 S W n len ret t v5 v6
    ⟨by omega, by omega⟩ (c1.trans (b1.trans (a1.trans h1))) (c5.trans (b5.trans (a5.trans h5)))
    (c6.trans (b6.trans (a6.trans h6))) c9 (by omega) (by omega) (Or.inr (by omega))
    (fun a h1 h2 => by rw [wr2, w1]; exact hWw a (by omega) h2)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r0)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r5)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r6)
    hv5 hv6 hret hjt hbt (fun a h1 h2 => by rw [rd2, d1]; exact hrs a (by omega) h2)
  refine ⟨ω4, _, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), e0, e1, e5, e6, e7, ?_,
    fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
  · unfold rdN
    rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
      (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
      fr2 a ha0 ha2 (by omega), m1 a ha0 (by omega)]
  · rw [Memory.readable_writeN, rd2, d1]
  · rw [Memory.writable_writeN, wr2, w1]

/-! ### The `String` and the allocator's context -/

/-- A chunk of a well-formed state lies in base … base + 2³⁰. -/
theorem chunk_bounds {s : State} (hwf : WF s) {c : Chunk} (hc : c ∈ chunks s) :
    s.base ≤ c.addr ∧ c.addr + 32 * c.size ≤ s.base + 1073741824 ∧ 0 < c.size := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  omega

/-- A well-formed state has a chunk. -/
theorem chunks_ne {s : State} (hwf : WF s) : ∃ c, c ∈ chunks s := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  cases h : chunks s with
  | nil => rw [h] at ht; simp only [Tiles] at ht; omega
  | cons c cs => exact ⟨c, List.mem_cons_self⟩

/-- **The allocator's context is kept by writes at or above 2³¹** (the stack) that keep every
    octet's access. -/
theorem ctx_hi {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) (hk : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ww : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  obtain ⟨c, hc⟩ := chunks_ne H.wf
  exact Decode.VecU8Heap.ctx_congr_data H hc (fun a ha _ => hk a ha) ww

/-- **The `String` at W**, as the logging runs keep it, from the state s₀ a run started with to s:
    its capacity `cap` at W and its length `len` at W + 16, len ≤ cap < 2²⁹; every allocated
    chunk of s₀ still allocated in s; and, unless cap = 0, its buffer (at W + 8) the data of an
    allocated chunk c of s of exactly ⌈cap/32⌉ + 1 units, at an address no allocated chunk of s₀
    has (a fresh allocation of the run). -/
structure Str (s₀ s : State) (μ : Memory) (W cap len : Nat) : Prop where
  rc : rdN μ W 8 = cap
  rl : rdN μ (W + 16) 8 = len
  le : len ≤ cap
  lt : cap < 536870912
  base : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s
  buf : cap = 0 ∨ ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = rdN μ (W + 8) 8 ∧
    c.size = (cap + 31) / 32 + 1 ∧ ∀ d ∈ chunks s₀, d.used = true → d.addr ≠ c.addr

end Services.Bootstrap.Fmt
