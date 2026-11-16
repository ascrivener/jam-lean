import Services.Bootstrap.Acc.Handlers.InstrLoopTail
import Services.Bootstrap.Acc.Transfer.CopyVal
import Services.Bootstrap.MemcpyBig
import Services.Bootstrap.Decode.Hash

/-!
# R5, the instruction loop: the body's front (8540 → 8735)

Spec `onWorkItem`'s `for i in is do …` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop): from the head
with cur ≠ end, the next slot (at cur = c) is taken (cur := c + 232), copied to sp + 744 (two `memcpy`
calls through sp + 512), the index counter k at sp + 504 saved at sp + 736 and bumped, and the tag
decoded. `il_front` covers the tags other than 3 (`Zombify`) and 15 (`Checkpoint`), which reach 8735
directly.
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **8540 … 8735, a slot whose tag is neither 3 nor 15**: from the head (or from 8554 with ω₆ = c, where
    the loop's entry falls through) with cur c ≠ end e (at sp + 480,
    sp + 496), the slot's word0 w (not `None`'s niche), the counter k at sp + 504: on to 8735 with
    the slot's 232 octets copied to sp + 744, cur = c + 232, the counter k + 1 at sp + 504 and k at
    sp + 736; the memory from sp up kept outside sp + 480 … sp + 488 and sp + 504 … sp + 976, and below sp − 48. -/
theorem il_front {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c e k w : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    {i0 : Nat} (hstart : i0 = 8540 ∨ (i0 = 8554 ∧ ω[6] = UInt64.ofNat c))
    (hsp : 2147483648 ≤ sp ∧ sp + 1632 < 4294967296 ∧ sp % 8 = 0)
    (hc : 65536 ≤ c ∧ c + 512 ≤ sp ∧ c % 8 = 0) (he : e < 2 ^ 64) (hce : c ≠ e) (hk : k + 1 < 2 ^ 64)
    (hw64 : w < 2 ^ 64) (hwN : w ≠ 18446744073709551614) (ht3 : slotTag w ≠ 3) (ht15 : slotTag w ≠ 15)
    (mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 c) (me : μ.readN (sp + 496) 8 = Num.encodeLE 8 e)
    (mw : μ.readN c 8 = Num.encodeLE 8 w) (mk : μ.readN (sp + 504) 8 = Num.encodeLE 8 k)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (hrs : ∀ a, c ≤ a → a < c + 232 → μ.readable a = true)
    (hws : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.writable a = true) :
    ∃ ω' μ' N, FreeStepsH p R i0 ω μ x 8735 ω' μ' x N ∧ ω'[1] = ω[1] ∧
      μ'.readN (sp + 744) 232 = μ.readN c 232 ∧
      μ'.readN (sp + 480) 8 = Num.encodeLE 8 (c + 232) ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 (k + 1) ∧ μ'.readN (sp + 736) 8 = Num.encodeLE 8 k ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have rd : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hws a h1 h2)
  -- 8540 → 8554
  obtain ⟨ω1, n1, run1, a1, a6⟩ : ∃ ω1 n1, FreeStepsH p R i0 ω μ x 8554 ω1 μ x n1 ∧ ω1[1] = ω[1] ∧
      ω1[6] = UInt64.ofNat c := by
    rcases hstart with rfl | ⟨rfl, h6⟩
    · obtain ⟨ω1, run1, a1, -, a6⟩ := il_head (R := R) (P := P) x ω μ sp c e h1 ⟨by omega, by omega⟩ (by omega) he
        hce mc me (fun a h1 h2 => rd a (by omega) (by omega))
      exact ⟨ω1, _, run1, a1, a6⟩
    · exact ⟨ω, 0, .refl, rfl, h6⟩
  -- 8554 → 68729 (memcpy c + 8 → sp + 512)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, m2, fr2, rd2, wr2⟩ := il_next (R := R) (P := P) x ω1 μ sp c w
    (a1.trans h1) a6 ⟨by omega, by omega⟩ ⟨hc.1, by omega⟩ hw64 hwN mw (fun a h1 h2 => hrs a h1 (by omega))
    (fun a h1 h2 => hws a (by omega) (by omega))
  have rs2 : ∀ a, c ≤ a → a < c + 232 → μ2.read a = μ.read a := fun a h1 h2 => fr2 a (by omega) (.inl (by omega))
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, m3, fr3, rd3, wr3⟩ := memcpy_val (R := R) (P := P) x ω2 μ2 296 8589 sp
    (sp + 512) (c + 8) 224 b0 (b1.trans (a1.trans h1)) b7 b8 b9 (by decide) jte_147 bs_8589
    ⟨by omega, by omega, hs3⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega)) (.inl (by omega))
    (.inr (by omega)) (fun a h1 h2 => by rw [rd2]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
  -- 8589 → 68729 (memcpy sp + 512 → sp + 752)
  have fr32 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 512 ∨ sp + 736 ≤ a) → μ3.read a = μ2.read a :=
    fun a h1 h2 h3 => fr3 a h1 h3 (.inr h2)
  have mk3 : μ3.readN (sp + 504) 8 = Num.encodeLE 8 k := by
    rw [← mk]; exact Memory.readN_congr fun j hj => (fr32 _ (by omega) (by omega) (.inl (by omega))).trans
      (fr2 _ (by omega) (.inr (by omega)))
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, m4k, m4i, m4w, fr4, rd4, wr4⟩ := il_copy2 (R := R) (P := P) x ω3 μ3
    sp k w (c1.trans (b1.trans (a1.trans h1))) (c5.trans b5) ⟨by omega, by omega⟩ hk hw64 mk3
    (fun a h1 h2 => by rw [rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, m5, fr5, rd5, wr5⟩ := memcpy_big_aligned (R := R) (P := P) x ω4 μ4 298 8627
    sp (sp + 752) (sp + 512) 224 d0 (d1.trans (c1.trans (b1.trans (a1.trans h1)))) d7 d8 d9 (by decide) jte_148
    bs_8627 ⟨by omega, by omega, hs3⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (.inr (by omega))
    (.inl (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd4, rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
  -- 8627 → 8735
  have fr5' : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 752 ∨ sp + 976 ≤ a) → μ5.read a = μ4.read a :=
    fun a h1 h2 h3 => fr5 a h1 h3 (.inr h2)
  have fr4' : ∀ a, a < 4294967296 → (a < sp + 504 ∨ sp + 512 ≤ a) → (a < sp + 736 ∨ sp + 752 ≤ a) →
      μ4.read a = μ3.read a := fr4
  have fr_hi : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
      μ5.read a = μ.read a :=
    fun a h1 h2 h3 => by
      rw [fr5' a h1 h2 (by omega), fr4' a h1 (by omega) (by omega), fr32 a h1 h2 (by omega),
        fr2 a h1 (by omega)]
  have m184' : μ5.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808 := by
    rw [← m184]; exact Memory.readN_congr fun j hj => fr_hi _ (by omega) (by omega) (.inl (by omega))
  have m216' : μ5.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809 := by
    rw [← m216]; exact Memory.readN_congr fun j hj => fr_hi _ (by omega) (by omega) (.inl (by omega))
  obtain ⟨ω6, run6, f1⟩ := il_tag_other (R := R) (P := P) x ω5 μ5 sp w
    e1 (e5.trans (d5.trans (c5.trans b5))) ⟨by omega, by omega⟩ hw64 ht3 ht15 m184' m216'
    (fun a h1 h2 => by rw [rd5, rd4, rd3, rd2]; exact rd a (by omega) (by omega))
  have e5_4 : ∀ a, sp + 480 ≤ a → a < sp + 752 → μ5.read a = μ4.read a := fun a h1 h2 =>
    fr5' a (by omega) (by omega) (.inl h2)
  refine ⟨ω6, μ5, _, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    f1.trans (e1.trans h1.symm), ?_, ?_, ?_, ?_, fun a ha h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
  · rw [show (232 : Nat) = 8 + 224 from rfl, Decode.Hash.readN_add, Decode.Hash.readN_add]
    congr 1
    · rw [show μ5.readN (sp + 744) 8 = μ4.readN (sp + 744) 8 from
        Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega), m4w, mw]
    · rw [show sp + 744 + 8 = sp + 752 by omega, m5, show μ4.readN (sp + 512) 224 = μ3.readN (sp + 512) 224 from
        Memory.readN_congr fun j hj => fr4' _ (by omega) (.inr (by omega)) (.inl (by omega)), m3]
      exact Memory.readN_congr fun j hj => rs2 _ (by omega) (by omega)
  · rw [← m2]; exact Memory.readN_congr fun j hj => by
      rw [e5_4 _ (by omega) (by omega), fr4' _ (by omega) (.inl (by omega)) (.inl (by omega)),
        fr32 _ (by omega) (by omega) (.inl (by omega))]
  · rw [← m4k]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rw [← m4i]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rcases h2 with h2 | h2
    · rw [fr5 a ha (.inl (by omega)) (.inl h2), fr4 a ha (.inl (by omega)) (.inl (by omega)),
        fr3 a ha (.inl (by omega)) (.inl h2), fr2 a ha (.inl (by omega))]
    · exact fr_hi a ha h2 h3
  · rw [rd5, rd4, rd3, rd2]
  · rw [wr5, wr4, wr3, wr2]

/-- **8540 … 8627, the front up to the tag decode** (any slot; used for `Checkpoint`, tag 15): as
    `il_front`, ending at 8627 with the slot's word0 w in ω₅. -/
theorem il_front8627 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c e k w : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    {i0 : Nat} (hstart : i0 = 8540 ∨ (i0 = 8554 ∧ ω[6] = UInt64.ofNat c))
    (hsp : 2147483648 ≤ sp ∧ sp + 1632 < 4294967296 ∧ sp % 8 = 0)
    (hc : 65536 ≤ c ∧ c + 512 ≤ sp ∧ c % 8 = 0) (he : e < 2 ^ 64) (hce : c ≠ e) (hk : k + 1 < 2 ^ 64)
    (hw64 : w < 2 ^ 64) (hwN : w ≠ 18446744073709551614)
    (mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 c) (me : μ.readN (sp + 496) 8 = Num.encodeLE 8 e)
    (mw : μ.readN c 8 = Num.encodeLE 8 w) (mk : μ.readN (sp + 504) 8 = Num.encodeLE 8 k)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (hrs : ∀ a, c ≤ a → a < c + 232 → μ.readable a = true)
    (hws : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.writable a = true) :
    ∃ ω' μ' N, FreeStepsH p R i0 ω μ x 8627 ω' μ' x N ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat w ∧
      μ'.readN (sp + 744) 232 = μ.readN c 232 ∧
      μ'.readN (sp + 480) 8 = Num.encodeLE 8 (c + 232) ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 (k + 1) ∧ μ'.readN (sp + 736) 8 = Num.encodeLE 8 k ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have rd : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hws a h1 h2)
  -- 8540 → 8554
  obtain ⟨ω1, n1, run1, a1, a6⟩ : ∃ ω1 n1, FreeStepsH p R i0 ω μ x 8554 ω1 μ x n1 ∧ ω1[1] = ω[1] ∧
      ω1[6] = UInt64.ofNat c := by
    rcases hstart with rfl | ⟨rfl, h6⟩
    · obtain ⟨ω1, run1, a1, -, a6⟩ := il_head (R := R) (P := P) x ω μ sp c e h1 ⟨by omega, by omega⟩ (by omega) he
        hce mc me (fun a h1 h2 => rd a (by omega) (by omega))
      exact ⟨ω1, _, run1, a1, a6⟩
    · exact ⟨ω, 0, .refl, rfl, h6⟩
  -- 8554 → 68729 (memcpy c + 8 → sp + 512)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, m2, fr2, rd2, wr2⟩ := il_next (R := R) (P := P) x ω1 μ sp c w
    (a1.trans h1) a6 ⟨by omega, by omega⟩ ⟨hc.1, by omega⟩ hw64 hwN mw (fun a h1 h2 => hrs a h1 (by omega))
    (fun a h1 h2 => hws a (by omega) (by omega))
  have rs2 : ∀ a, c ≤ a → a < c + 232 → μ2.read a = μ.read a := fun a h1 h2 => fr2 a (by omega) (.inl (by omega))
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, m3, fr3, rd3, wr3⟩ := memcpy_val (R := R) (P := P) x ω2 μ2 296 8589 sp
    (sp + 512) (c + 8) 224 b0 (b1.trans (a1.trans h1)) b7 b8 b9 (by decide) jte_147 bs_8589
    ⟨by omega, by omega, hs3⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega)) (.inl (by omega))
    (.inr (by omega)) (fun a h1 h2 => by rw [rd2]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
  -- 8589 → 68729 (memcpy sp + 512 → sp + 752)
  have fr32 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 512 ∨ sp + 736 ≤ a) → μ3.read a = μ2.read a :=
    fun a h1 h2 h3 => fr3 a h1 h3 (.inr h2)
  have mk3 : μ3.readN (sp + 504) 8 = Num.encodeLE 8 k := by
    rw [← mk]; exact Memory.readN_congr fun j hj => (fr32 _ (by omega) (by omega) (.inl (by omega))).trans
      (fr2 _ (by omega) (.inr (by omega)))
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, m4k, m4i, m4w, fr4, rd4, wr4⟩ := il_copy2 (R := R) (P := P) x ω3 μ3
    sp k w (c1.trans (b1.trans (a1.trans h1))) (c5.trans b5) ⟨by omega, by omega⟩ hk hw64 mk3
    (fun a h1 h2 => by rw [rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, m5, fr5, rd5, wr5⟩ := memcpy_big_aligned (R := R) (P := P) x ω4 μ4 298 8627
    sp (sp + 752) (sp + 512) 224 d0 (d1.trans (c1.trans (b1.trans (a1.trans h1)))) d7 d8 d9 (by decide) jte_148
    bs_8627 ⟨by omega, by omega, hs3⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (.inr (by omega))
    (.inl (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd4, rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
  -- 8627 → 8735
  have fr5' : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 752 ∨ sp + 976 ≤ a) → μ5.read a = μ4.read a :=
    fun a h1 h2 h3 => fr5 a h1 h3 (.inr h2)
  have fr4' : ∀ a, a < 4294967296 → (a < sp + 504 ∨ sp + 512 ≤ a) → (a < sp + 736 ∨ sp + 752 ≤ a) →
      μ4.read a = μ3.read a := fr4
  have fr_hi : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
      μ5.read a = μ.read a :=
    fun a h1 h2 h3 => by
      rw [fr5' a h1 h2 (by omega), fr4' a h1 (by omega) (by omega), fr32 a h1 h2 (by omega),
        fr2 a h1 (by omega)]
  have e5_4 : ∀ a, sp + 480 ≤ a → a < sp + 752 → μ5.read a = μ4.read a := fun a h1 h2 =>
    fr5' a (by omega) (by omega) (.inl h2)
  refine ⟨ω5, μ5, _, run1.trans (run2.trans (run3.trans (run4.trans run5))),
    e1.trans h1.symm, e5.trans (d5.trans (c5.trans b5)), ?_, ?_, ?_, ?_, fun a ha h2 h3 => ?_, fun a => ?_,
    fun a => ?_⟩
  · rw [show (232 : Nat) = 8 + 224 from rfl, Decode.Hash.readN_add, Decode.Hash.readN_add]
    congr 1
    · rw [show μ5.readN (sp + 744) 8 = μ4.readN (sp + 744) 8 from
        Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega), m4w, mw]
    · rw [show sp + 744 + 8 = sp + 752 by omega, m5, show μ4.readN (sp + 512) 224 = μ3.readN (sp + 512) 224 from
        Memory.readN_congr fun j hj => fr4' _ (by omega) (.inr (by omega)) (.inl (by omega)), m3]
      exact Memory.readN_congr fun j hj => rs2 _ (by omega) (by omega)
  · rw [← m2]; exact Memory.readN_congr fun j hj => by
      rw [e5_4 _ (by omega) (by omega), fr4' _ (by omega) (.inl (by omega)) (.inl (by omega)),
        fr32 _ (by omega) (by omega) (.inl (by omega))]
  · rw [← m4k]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rw [← m4i]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rcases h2 with h2 | h2
    · rw [fr5 a ha (.inl (by omega)) (.inl h2), fr4 a ha (.inl (by omega)) (.inl (by omega)),
        fr3 a ha (.inl (by omega)) (.inl h2), fr2 a ha (.inl (by omega))]
    · exact fr_hi a ha h2 h3
  · rw [rd5, rd4, rd3, rd2]
  · rw [wr5, wr4, wr3, wr2]

/-- **8540 … 8735, a `Zombify` slot** (tag 3): as `il_front`, and the flag [sp + 160] := 1. The front: from the head with cur c ≠ end e (at sp + 480,
    sp + 496), the slot's word0 w (not `None`'s niche), the counter k at sp + 504: on to 8735 with
    the slot's 232 octets copied to sp + 744, cur = c + 232, the counter k + 1 at sp + 504 and k at
    sp + 736; the memory from sp up kept outside sp + 480 … sp + 488 and sp + 504 … sp + 976, and below sp − 48. -/
theorem il_front_zomb {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp c e k w : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    {i0 : Nat} (hstart : i0 = 8540 ∨ (i0 = 8554 ∧ ω[6] = UInt64.ofNat c))
    (hsp : 2147483648 ≤ sp ∧ sp + 1632 < 4294967296 ∧ sp % 8 = 0)
    (hc : 65536 ≤ c ∧ c + 512 ≤ sp ∧ c % 8 = 0) (he : e < 2 ^ 64) (hce : c ≠ e) (hk : k + 1 < 2 ^ 64)
    (hw64 : w < 2 ^ 64) (hwN : w ≠ 18446744073709551614) (ht : slotTag w = 3)
    (mc : μ.readN (sp + 480) 8 = Num.encodeLE 8 c) (me : μ.readN (sp + 496) 8 = Num.encodeLE 8 e)
    (mw : μ.readN c 8 = Num.encodeLE 8 w) (mk : μ.readN (sp + 504) 8 = Num.encodeLE 8 k)
    (m184 : μ.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808)
    (m216 : μ.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809)
    (hrs : ∀ a, c ≤ a → a < c + 232 → μ.readable a = true)
    (hws : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.writable a = true) :
    ∃ ω' μ' N, FreeStepsH p R i0 ω μ x 8735 ω' μ' x N ∧ ω'[1] = ω[1] ∧
      μ'.readN (sp + 160) 8 = Num.encodeLE 8 1 ∧ μ'.readN (sp + 744) 232 = μ.readN c 232 ∧
      μ'.readN (sp + 480) 8 = Num.encodeLE 8 (c + 232) ∧
      μ'.readN (sp + 504) 8 = Num.encodeLE 8 (k + 1) ∧ μ'.readN (sp + 736) 8 = Num.encodeLE 8 k ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
        (a < sp + 160 ∨ sp + 168 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hs1, hs2, hs3⟩ := hsp
  have rd : ∀ a, sp - 48 ≤ a → a < sp + 1632 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hws a h1 h2)
  -- 8540 → 8554
  obtain ⟨ω1, n1, run1, a1, a6⟩ : ∃ ω1 n1, FreeStepsH p R i0 ω μ x 8554 ω1 μ x n1 ∧ ω1[1] = ω[1] ∧
      ω1[6] = UInt64.ofNat c := by
    rcases hstart with rfl | ⟨rfl, h6⟩
    · obtain ⟨ω1, run1, a1, -, a6⟩ := il_head (R := R) (P := P) x ω μ sp c e h1 ⟨by omega, by omega⟩ (by omega) he
        hce mc me (fun a h1 h2 => rd a (by omega) (by omega))
      exact ⟨ω1, _, run1, a1, a6⟩
    · exact ⟨ω, 0, .refl, rfl, h6⟩
  -- 8554 → 68729 (memcpy c + 8 → sp + 512)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, m2, fr2, rd2, wr2⟩ := il_next (R := R) (P := P) x ω1 μ sp c w
    (a1.trans h1) a6 ⟨by omega, by omega⟩ ⟨hc.1, by omega⟩ hw64 hwN mw (fun a h1 h2 => hrs a h1 (by omega))
    (fun a h1 h2 => hws a (by omega) (by omega))
  have rs2 : ∀ a, c ≤ a → a < c + 232 → μ2.read a = μ.read a := fun a h1 h2 => fr2 a (by omega) (.inl (by omega))
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, m3, fr3, rd3, wr3⟩ := memcpy_val (R := R) (P := P) x ω2 μ2 296 8589 sp
    (sp + 512) (c + 8) 224 b0 (b1.trans (a1.trans h1)) b7 b8 b9 (by decide) jte_147 bs_8589
    ⟨by omega, by omega, hs3⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega)) (.inl (by omega))
    (.inr (by omega)) (fun a h1 h2 => by rw [rd2]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) (by omega))
  -- 8589 → 68729 (memcpy sp + 512 → sp + 752)
  have fr32 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 512 ∨ sp + 736 ≤ a) → μ3.read a = μ2.read a :=
    fun a h1 h2 h3 => fr3 a h1 h3 (.inr h2)
  have mk3 : μ3.readN (sp + 504) 8 = Num.encodeLE 8 k := by
    rw [← mk]; exact Memory.readN_congr fun j hj => (fr32 _ (by omega) (by omega) (.inl (by omega))).trans
      (fr2 _ (by omega) (.inr (by omega)))
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, m4k, m4i, m4w, fr4, rd4, wr4⟩ := il_copy2 (R := R) (P := P) x ω3 μ3
    sp k w (c1.trans (b1.trans (a1.trans h1))) (c5.trans b5) ⟨by omega, by omega⟩ hk hw64 mk3
    (fun a h1 h2 => by rw [rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3, wr2]; exact hws a (by omega) (by omega))
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, m5, fr5, rd5, wr5⟩ := memcpy_big_aligned (R := R) (P := P) x ω4 μ4 298 8627
    sp (sp + 752) (sp + 512) 224 d0 (d1.trans (c1.trans (b1.trans (a1.trans h1)))) d7 d8 d9 (by decide) jte_148
    bs_8627 ⟨by omega, by omega, hs3⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (.inr (by omega))
    (.inl (by omega)) (.inl (by omega))
    (fun a h1 h2 => by rw [rd4, rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr4, wr3, wr2]; exact hws a (by omega) (by omega))
  -- 8627 → 8735
  have fr5' : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 752 ∨ sp + 976 ≤ a) → μ5.read a = μ4.read a :=
    fun a h1 h2 h3 => fr5 a h1 h3 (.inr h2)
  have fr4' : ∀ a, a < 4294967296 → (a < sp + 504 ∨ sp + 512 ≤ a) → (a < sp + 736 ∨ sp + 752 ≤ a) →
      μ4.read a = μ3.read a := fr4
  have fr_hi : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 480 ∨ (sp + 488 ≤ a ∧ a < sp + 504) ∨ sp + 976 ≤ a) →
      μ5.read a = μ.read a :=
    fun a h1 h2 h3 => by
      rw [fr5' a h1 h2 (by omega), fr4' a h1 (by omega) (by omega), fr32 a h1 h2 (by omega),
        fr2 a h1 (by omega)]
  have m184' : μ5.readN (sp + 184) 8 = Num.encodeLE 8 9223372036854775808 := by
    rw [← m184]; exact Memory.readN_congr fun j hj => fr_hi _ (by omega) (by omega) (.inl (by omega))
  have m216' : μ5.readN (sp + 216) 8 = Num.encodeLE 8 9223372036854775809 := by
    rw [← m216]; exact Memory.readN_congr fun j hj => fr_hi _ (by omega) (by omega) (.inl (by omega))
  obtain ⟨ω6, μ6, run6, f1, m6, fr6, rd6, wr6⟩ := il_tag_zomb (R := R) (P := P) x ω5 μ5 sp w
    e1 (e5.trans (d5.trans (c5.trans b5))) ⟨by omega, by omega⟩ hw64 ht m184' m216'
    (fun a h1 h2 => by rw [rd5, rd4, rd3, rd2]; exact rd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr5, wr4, wr3, wr2]; exact hws a (by omega) (by omega))
  have e6_5 : ∀ a, a < 4294967296 → (a < sp + 160 ∨ sp + 168 ≤ a) → μ6.read a = μ5.read a := fr6
  have e5_4 : ∀ a, sp + 480 ≤ a → a < sp + 752 → μ5.read a = μ4.read a := fun a h1 h2 =>
    fr5' a (by omega) (by omega) (.inl h2)
  refine ⟨ω6, μ6, _, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    f1.trans (e1.trans h1.symm), m6, ?_, ?_, ?_, ?_, fun a ha h2 h3 h4 => ?_, fun a => ?_, fun a => ?_⟩
  all_goals try rw [show μ6.readN (sp + 744) 232 = μ5.readN (sp + 744) 232 from
    Memory.readN_congr fun j hj => e6_5 _ (by omega) (.inr (by omega))]
  all_goals try rw [show μ6.readN (sp + 480) 8 = μ5.readN (sp + 480) 8 from
    Memory.readN_congr fun j hj => e6_5 _ (by omega) (.inr (by omega))]
  all_goals try rw [show μ6.readN (sp + 504) 8 = μ5.readN (sp + 504) 8 from
    Memory.readN_congr fun j hj => e6_5 _ (by omega) (.inr (by omega))]
  all_goals try rw [show μ6.readN (sp + 736) 8 = μ5.readN (sp + 736) 8 from
    Memory.readN_congr fun j hj => e6_5 _ (by omega) (.inr (by omega))]
  · rw [show (232 : Nat) = 8 + 224 from rfl, Decode.Hash.readN_add, Decode.Hash.readN_add]
    congr 1
    · rw [show μ5.readN (sp + 744) 8 = μ4.readN (sp + 744) 8 from
        Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega), m4w, mw]
    · rw [show sp + 744 + 8 = sp + 752 by omega, m5, show μ4.readN (sp + 512) 224 = μ3.readN (sp + 512) 224 from
        Memory.readN_congr fun j hj => fr4' _ (by omega) (.inr (by omega)) (.inl (by omega)), m3]
      exact Memory.readN_congr fun j hj => rs2 _ (by omega) (by omega)
  · rw [← m2]; exact Memory.readN_congr fun j hj => by
      rw [e5_4 _ (by omega) (by omega), fr4' _ (by omega) (.inl (by omega)) (.inl (by omega)),
        fr32 _ (by omega) (by omega) (.inl (by omega))]
  · rw [← m4k]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rw [← m4i]; exact Memory.readN_congr fun j hj => e5_4 _ (by omega) (by omega)
  · rw [e6_5 a ha h4]
    rcases h2 with h2 | h2
    · rw [fr5 a ha (.inl (by omega)) (.inl h2), fr4 a ha (.inl (by omega)) (.inl (by omega)),
        fr3 a ha (.inl (by omega)) (.inl h2), fr2 a ha (.inl (by omega))]
    · exact fr_hi a ha h2 h3
  · rw [rd6, rd5, rd4, rd3, rd2]
  · rw [wr6, wr5, wr4, wr3, wr2]

end Services.Bootstrap.Acc.Handlers.InstrLoop
